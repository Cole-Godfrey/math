use metamath_rs::database::DbOptions;
use metamath_rs::diag::Diagnostic;
use metamath_rs::statement::StatementAddress;
use metamath_rs::verify::ProofBuilder;
use metamath_rs::{Database, StatementType};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::ops::Range;
use std::path::Path;

// every node records the exact rule invocation and ordered hypothesis occurrences.
#[derive(Serialize)]
struct Step {
    reference: String,
    arguments: Vec<usize>,
    expression_digest: String,
}

struct Builder<'a> {
    database: &'a Database,
    steps: Vec<Step>,
}

fn text(bytes: &[u8]) -> String {
    std::str::from_utf8(bytes).expect("non-utf8 source token").to_owned()
}

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

impl ProofBuilder for Builder<'_> {
    type Item = usize;
    type Accum = Vec<usize>;

    fn push(&mut self, hypotheses: &mut Self::Accum, hypothesis: usize) {
        hypotheses.push(hypothesis);
    }

    fn build(&mut self, address: StatementAddress, arguments: Vec<usize>, pool: &[u8], expression: Range<usize>) -> usize {
        let statement = self.database.statement_by_address(address);
        let mut tokens = vec![text(&statement.math_at(0))];
        let mut token = Vec::new();
        for byte in &pool[expression] {
            token.push(byte & 0x7f);
            if byte & 0x80 != 0 {
                tokens.push(text(&token));
                token.clear();
            }
        }
        assert!(token.is_empty(), "unterminated encoded math token");
        let identifier = self.steps.len();
        assert!(arguments.iter().all(|child| *child < identifier));
        self.steps.push(Step {
            reference: text(statement.label()),
            arguments,
            expression_digest: sha(&serde_json::to_vec(&tokens).unwrap()),
        });
        identifier
    }
}

fn emit(output: &mut impl Write, value: &Value) {
    serde_json::to_writer(&mut *output, value).unwrap();
    output.write_all(b"\n").unwrap();
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    assert_eq!(arguments.len(), 3, "expected database and output paths");
    let input = &arguments[1];
    let source = fs::read(input).expect("database is missing");
    let basename = Path::new(input).file_name().unwrap().to_str().unwrap();
    let mut database = Database::new(DbOptions { autosplit: false, jobs: 1, ..Default::default() });
    database.parse(input.clone(), Vec::new());
    database.verify_pass();
    let diagnostics = database.diag_notations();
    let mut warnings = Vec::new();
    for (_, diagnostic) in diagnostics {
        match diagnostic {
            Diagnostic::CommentMarkerNotStart(span) if basename == "big-unifier.mm" && sha(&source) == "664669725ff42cb35a4b4c10823b5a7664d8f404eab94385de0ace79e6aa501e" => {
                warnings.push(json!({"kind":"comment_marker_not_start", "start":span.start, "end":span.end}));
            }
            other => panic!("database verification diagnostic: {other:?}"),
        }
    }
    let temporary = format!("{}.partial", arguments[2]);
    let mut output = BufWriter::new(File::create(&temporary).unwrap());
    emit(&mut output, &json!({"record":"header", "schema_version":1, "proof_system":"metamath", "database":basename, "source_sha256":sha(&source), "source_bytes":source.len(), "retained_warnings":warnings}));
    let newlines: Vec<usize> = source.iter().enumerate().filter_map(|(index, byte)| (*byte == b'\n').then_some(index)).collect();
    let mut counts = BTreeMap::<String, usize>::new();
    let mut steps = 0;
    let mut previous_end = 0;
    let mut assertions = 0;
    for (ordinal, statement) in database.statements().enumerate() {
        assert_eq!(database.statement_source_name(statement.address()), input);
        assert_eq!(statement.segment().buffer.as_slice(), source.as_slice(), "source buffer differs from the pinned file");
        let kind = format!("{:?}", statement.statement_type());
        *counts.entry(kind.clone()).or_default() += 1;
        let full = statement.span_full();
        assert_eq!(full.start as usize, previous_end, "source fragments do not cover the file in order");
        previous_end = full.end as usize;
        assert!(previous_end <= source.len());
        let label = text(statement.label());
        let math: Vec<String> = statement.math_iter().map(|token| text(&token)).collect();
        let proof: Vec<String> = statement.proof_spans().iter().map(|span| text(span.as_ref(&source))).collect();
        let mut frame_data = Value::Null;
        if statement.is_assertion() {
            assertions += 1;
            let frame = database.scope_result().get(statement.label()).expect("assertion has no scope frame");
            let variables: Vec<String> = frame.var_list.iter().map(|atom| text(database.name_result().atom_name(*atom))).collect();
            let hypotheses: Vec<String> = frame.hypotheses.iter().map(|hypothesis| text(database.statement_by_address(hypothesis.address()).label())).collect();
            let mandatory: Vec<Vec<String>> = frame.mandatory_dv.iter().map(|(left, right)| vec![variables[*left].clone(), variables[*right].clone()]).collect();
            let mut active = Vec::new();
            for (left, row) in frame.optional_dv.iter().enumerate() {
                for right in row.iter() {
                    if left < right { active.push(vec![variables[left].clone(), variables[right].clone()]); }
                }
            }
            frame_data = json!({"hypotheses":hypotheses, "mandatory_variables":&variables[..frame.mandatory_count], "variables":variables, "mandatory_disjoint":mandatory, "proof_disjoint":active});
        }
        let mut dag = Value::Null;
        if statement.statement_type() == StatementType::Provable {
            let mut builder = Builder { database: &database, steps: Vec::new() };
            let root = database.verify_one(&mut builder, statement).expect("proof replay failed during export");
            assert!(root < builder.steps.len());
            steps += builder.steps.len();
            dag = json!({"nodes":builder.steps, "root":root});
        }
        emit(&mut output, &json!({"record":"statement", "ordinal":ordinal, "kind":kind, "label":if label.is_empty() {Value::Null} else {json!(label)}, "expression":math, "proof":proof, "frame":frame_data, "proof_dag":dag, "source":{"start":full.start,"end":full.end,"line":newlines.partition_point(|offset| *offset < full.start as usize)+1,"end_line":newlines.partition_point(|offset| *offset < full.end as usize)+1}}));
        if assertions > 0 && assertions % 5000 == 0 && statement.is_assertion() { eprintln!("exported {assertions} assertions"); }
    }
    assert_eq!(previous_end, source.len(), "source coverage is incomplete");
    assert_eq!(fs::read(input).unwrap(), source, "database bytes changed during verification");
    emit(&mut output, &json!({"record":"summary", "counts":counts, "assertions":assertions, "proof_nodes":steps, "source_sha256":sha(&source)}));
    output.flush().unwrap();
    drop(output);
    fs::rename(temporary, &arguments[2]).unwrap();
    eprintln!("export complete: {assertions} assertions and {steps} proof nodes");
}

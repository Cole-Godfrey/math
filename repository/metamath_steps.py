"""reconstruct each displayed native proof step from its ordered substitutions."""

from __future__ import annotations

from functools import lru_cache
from copy import deepcopy

from .core import require
from .metamath_audit import Auditor, disjoint_pairs, fingerprint, Rule
from .metamath_store import identity


class NativeSteps:
    """interpret the retained proof dag in its own scoped assertion frame."""

    def __init__(self, snapshot):
        self.snapshot = snapshot

    @lru_cache(maxsize=16384)
    def record(self, name):
        with self.snapshot.reader() as reader:
            return reader.declaration(name)

    @lru_cache(maxsize=64)
    def reconstruct(self, name):
        declaration = self.record(name)
        database = declaration['database_id']
        frame = declaration['frame']
        if declaration['kind'] != 'Provable':
            return {'declaration': name, 'proof_system': 'metamath', 'kind': declaration['kind'],
                    'statement_tokens': declaration['expression'], 'frame': frame,
                    'proof_tokens': [], 'root': None, 'steps': [], 'context': []}
        with self.snapshot.reader() as reader:
            proof = reader.proof(name)
        dag = proof['dag']
        auditor = Auditor()
        labels = {node['reference'] for node in dag['nodes']} | set(frame['hypotheses'])
        records = {}
        pending = list(labels)
        while pending:
            label = pending.pop()
            if label in records:
                continue
            row = self.record(identity(database, label))
            records[label] = row
            if row['frame']:
                pending.extend(row['frame']['hypotheses'])
            auditor.rules[label] = Rule(label, row['kind'], tuple(row['expression']), row['ordinal'],
                tuple(row['frame']['hypotheses']) if row['frame'] else (),
                frozenset(disjoint_pairs(row['frame']['mandatory_disjoint'])) if row['frame'] else frozenset())
        auditor.variables = set(frame['variables'])
        auditor.disjoint = set(disjoint_pairs(frame['proof_disjoint']))
        for label in labels:
            row = records[label]
            require(row['ordinal'] < declaration['ordinal'], 'native proof uses a future or circular declaration')
            if row['kind'] == 'Floating':
                variable = row['expression'][1]
                require(variable not in auditor.floating or auditor.floating[variable] == label,
                        'native proof mixes distinct active typings of one variable')
                auditor.variables.add(variable)
                auditor.floating[variable] = label
            elif row['kind'] == 'Essential':
                auditor.essential.append(label)
        results, steps = [], []
        for index, node in enumerate(dag['nodes']):
            require(type(node['arguments']) is list and all(type(child) is int and 0 <= child < index
                    for child in node['arguments']), 'native proof has a forward or invalid step reference')
            result = auditor.apply(node['reference'], [results[child] for child in node['arguments']], set())
            expression = list(result.expression)
            require(fingerprint(expression) == node['expression_digest'], 'native step expression differs from checked export')
            results.append(result)
            steps.append({'index': index, 'reference': identity(database, node['reference']),
                          'arguments': list(node['arguments']), 'expression_tokens': expression,
                          'expression_digest': node['expression_digest']})
        root = dag['root']
        require(type(root) is int and 0 <= root < len(results), 'native proof root differs')
        require(list(results[root].expression) == declaration['expression'], 'native proof concludes another statement')
        require(results[root].tree == declaration['checked']['proof_digest'],
                'native displayed derivation differs from independently checked source')
        context = [{'name': identity(database, label), 'kind': records[label]['kind'],
                    'expression_tokens': records[label]['expression'], 'mandatory': label in frame['hypotheses']}
                   for label in sorted(labels, key=lambda item: records[item]['ordinal'])
                   if records[label]['kind'] in ['Floating', 'Essential']]
        return {'declaration': name, 'proof_system': 'metamath', 'kind': declaration['kind'],
                'statement_tokens': declaration['expression'], 'frame': frame,
                'proof_tokens': proof['tokens'], 'root': root, 'steps': steps, 'context': context}

    def inspect(self, name, step=None):
        data = self.reconstruct(name)
        if data['root'] is None:
            require(step is None, 'a declared rule or local hypothesis has no proof steps')
            return deepcopy({**data, 'focused': None, 'step_count': 0})
        index = data['root'] if step is None else step
        require(type(index) is int and 0 <= index < len(data['steps']), 'unknown native proof step')
        focused = data['steps'][index]
        return deepcopy({key: value for key, value in data.items() if key != 'steps'} | {
            'focused': focused, 'arguments': [data['steps'][child] for child in focused['arguments']],
            'step_count': len(data['steps'])})

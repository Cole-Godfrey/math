"""translate pinned native miu proof steps into checked lean derivations."""

from __future__ import annotations

import hashlib

from .metamath_audit import require
from .metamath_steps import NativeSteps
from .metamath_store import identity


SOURCE_SHA256 = '2b37347a892060adaa2c361d4b0fec92b49b8c2a40ddcc4a82c996f2f1eb58fa'
RULES = {
    'we': (['wff'], []),
    'wM': (['wff', 'x', 'M'], ['wx']),
    'wI': (['wff', 'x', 'I'], ['wx']),
    'wU': (['wff', 'x', 'U'], ['wx']),
    'wxy': (['wff', 'x', 'y'], ['wx', 'wy']),
    'ax': (['|-', 'M', 'I'], []),
    'I_': (['|-', 'x', 'I', 'U'], ['wx', 'Ia']),
    'II': (['|-', 'M', 'x', 'x'], ['wx', 'IIa']),
    'III': (['|-', 'x', 'U', 'y'], ['wx', 'wy', 'IIIa']),
    'IV': (['|-', 'x', 'y'], ['wx', 'wy', 'IVa']),
}
HYPOTHESES = {
    'wx': ('Floating', ['wff', 'x']),
    'wy': ('Floating', ['wff', 'y']),
    'Ia': ('Essential', ['|-', 'x', 'I']),
    'IIa': ('Essential', ['|-', 'M', 'x']),
    'IIIa': ('Essential', ['|-', 'x', 'I', 'I', 'I', 'y']),
    'IVa': ('Essential', ['|-', 'x', 'U', 'U', 'y']),
}


def lean_word(tokens):
    """render only the three literal symbols of the source calculus."""
    require(all(type(token) is str and token in {'M', 'I', 'U'} for token in tokens),
            'miu translation contains an unresolved symbol')
    return '[' + ', '.join(tokens) + ']'


def translate(snapshot, name):
    """reconstruct every logical step as an application of its lean rule constructor."""
    node = snapshot.declaration(name)
    require(node['database_id'] == 'miu.mm', 'lean translation is available only for miu.mm')
    require(node['kind'] == 'Provable', 'miu translation requires a proved statement')
    require(hashlib.sha256(snapshot.source(name, full=True)).hexdigest() == SOURCE_SHA256,
            'miu source differs from the reviewed interpretation')
    require(not node['frame']['hypotheses'] and not node['frame']['mandatory_disjoint'],
            'miu translation requires a closed proof')
    for label, (kind, expression) in HYPOTHESES.items():
        hypothesis = snapshot.declaration(identity('miu.mm', label))
        require(hypothesis['kind'] == kind and hypothesis['expression'] == expression and
                hypothesis['frame'] is None, 'miu hypothesis differs from its lean interpretation: ' + label)
    for label, (expression, hypotheses) in RULES.items():
        rule = snapshot.declaration(identity('miu.mm', label))
        require(rule['kind'] == 'Axiom' and rule['expression'] == expression and
                rule['frame']['hypotheses'] == hypotheses and not rule['frame']['mandatory_disjoint'],
                'miu rule differs from its lean interpretation: ' + label)
    data = NativeSteps(snapshot).reconstruct(name)
    lines = ['import Math.Logic.Miu', '', 'set_option autoImplicit false',
             'set_option warningAsError true', '', 'open Math.Miu Math.Miu.Symbol', '',
             '-- native source sha256: ' + SOURCE_SHA256,
             '-- native checked proof digest: ' + node['checked']['proof_digest'],
             'example : Derivable ' + lean_word(data['statement_tokens'][1:]) + ' := by']
    proved = set()
    for step in data['steps']:
        expression = step['expression_tokens']
        require(expression and expression[0] in {'wff', '|-'}, 'unknown miu judgment')
        lean_word(expression[1:])
        if expression[0] == 'wff':
            continue
        label = step['reference'].removeprefix('metamath:miu.mm:')
        require(label in {'ax', 'I_', 'II', 'III', 'IV'}, 'unknown miu logical rule')
        arguments = [data['steps'][index] for index in step['arguments']]
        hypothesis = None
        words = []
        for argument in arguments:
            value = argument['expression_tokens']
            if value[0] == 'wff':
                words.append(lean_word(value[1:]))
            else:
                require(argument['index'] in proved, 'miu premise has no translated derivation')
                require(hypothesis is None, 'miu rule has several logical premises')
                hypothesis = 'step_' + str(argument['index'])
        if label == 'ax':
            require(not words and hypothesis is None, 'miu axiom has unexpected arguments')
            value = 'Derivable.ax'
        else:
            require(hypothesis is not None and len(words) == (2 if label in {'III', 'IV'} else 1),
                    'miu rule argument frame differs')
            value = 'Derivable.' + label + ' ' + ' '.join([*words, hypothesis])
        lines.append('  have step_' + str(step['index']) + ' : Derivable ' +
                     lean_word(expression[1:]) + ' := ' + value)
        proved.add(step['index'])
    require(data['root'] in proved, 'miu proof has no translated conclusion')
    lines.append('  exact step_' + str(data['root']))
    return '\n'.join(lines) + '\n'

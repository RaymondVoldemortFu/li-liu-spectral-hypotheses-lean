"""Compare the explicit GRH propositions in two lean4export files.
Resolves the source's named proposition, global names and universe levels.
Expands the challenge compiler's auxiliary proof for the numeral two.
Compares the bodies of the listed mathematical definitions as well.
Binder names are ignored. Transitive library dependencies are checked in each native export.
"""
from array import array
from functools import lru_cache
import hashlib
import json
import mmap
from pathlib import Path
import re
import sys

DEFINITIONS = (
    'DirichletCharacter', 'DirichletCharacter.IsPrimitive', 'DirichletCharacter.conductor',
    'DirichletCharacter.FactorsThrough', 'DirichletCharacter.LFunction', 'ZMod.LFunction',
    'Complex.re',
)

INDEX = re.compile(rb'"(ie|il|in)":(\d+)')
DECL = re.compile(rb'^\{"(?:def|thm|opaque)":')
try:
    from ujson import loads
except ImportError:
    from json import loads


class Export:
    def __init__(self, path):
        self.stream = open(path, 'rb')
        self.data = mmap.mmap(self.stream.fileno(), 0, access=mmap.ACCESS_READ)
        self.tables = {b'ie': array('Q'), b'in': array('Q', [0]), b'il': array('Q', [0])}
        self.declarations = {}
        pos = 0
        while line := self.data.readline():
            match = INDEX.search(line)
            if match:
                table = self.tables[match[1]]
                assert int(match[2]) == len(table)
                table.append(pos)
            elif DECL.match(line):
                decl = next(iter(loads(line).values()))
                self.declarations[decl['name']] = decl
            pos += len(line)

    def node(self, kind, index):
        self.data.seek(self.tables[kind][index])
        record = loads(self.data.readline())
        del record[kind.decode('ascii')]
        return next(iter(record.items()))

    @lru_cache(maxsize=4096)
    def name(self, index):
        if index == 0:
            return ()
        tag, node = self.node(b'in', index)
        return self.name(node['pre']) + (node['str' if tag == 'str' else 'i'],)

    @lru_cache(maxsize=2048)
    def level(self, index):
        if index == 0:
            return 'zero'
        tag, node = self.node(b'il', index)
        if tag == 'param':
            return [tag, self.name(node)]
        if tag == 'succ':
            return [tag, self.level(node)]
        if tag in ('max', 'imax'):
            return [tag, self.level(node[0]), self.level(node[1])]
        raise ValueError(f'unexpected universe level in theorem statement: {tag}')

    def term(self, index):
        tag, node = self.node(b'ie', index)
        if tag in ('forallE', 'lam'):
            return [tag, node['binderInfo'], self.term(node['type']), self.term(node['body'])]
        if tag == 'const':
            if self.name(node['name']) == ('RiemannZetaZerosOnLine', '_proof_1'):
                assert not node['us']
                return self.term(self.declarations[node['name']]['value'])
            return [tag, self.name(node['name']), [self.level(u) for u in node['us']]]
        if tag == 'sort':
            return [tag, self.level(node)]
        if tag == 'app':
            return [tag, self.term(node['fn']), self.term(node['arg'])]
        if tag in ('lit', 'natVal', 'strVal', 'bvar'):
            return [tag, node]
        if tag == 'proj':
            return [tag, self.name(node['typeName']), node['idx'], self.term(node['struct'])]
        raise ValueError(f'unexpected node in theorem statement: {tag}')

    def declaration(self, full_name):
        suffix = full_name.split('.')[-1].encode()
        pattern = re.compile(rb'\{"in":(\d+),"str":\{"pre":\d+,"str":"' + re.escape(suffix) + rb'"\}\}')
        for m in pattern.finditer(self.data):
            index = int(m[1])
            if self.name(index) == tuple(full_name.split('.')) and index in self.declarations:
                return self.declarations[index]
        raise KeyError(full_name)

    def forall_type(self, index):
        while True:
            tag, data = self.node(b'ie', index)
            if tag == 'forallE':
                return index
            if tag != 'const' or data['us']:
                raise ValueError('expected a named proposition or universal quantification')
            index = self.declarations[data['name']]['value']


def snapshot(source, target, premise):
    index = source.declaration(target)['type']
    if premise:
        tag, data = source.node(b'ie', index)
        assert tag == 'forallE'
        index = data['type']
    value = source.term(source.forall_type(index))
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(',', ':')).encode()


if __name__ == '__main__':
    challenge, spectral = map(Path, sys.argv[1:3])
    old = Export(challenge)
    external = snapshot(old, 'LFunction_eq_zero_re_of_isPrimitive', False)
    definitions = {n: old.term(old.declaration(n)['value']) for n in DEFINITIONS}
    old.data.close()
    old.stream.close()
    current = Export(spectral)
    local = snapshot(current, 'GoldbachSpectral435.primitive_GRH_spectral_consequences', True)
    specialization = snapshot(current, 'GoldbachSpectral435.all_local_of_primitive', True)
    for name, expected in definitions.items():
        actual = current.term(current.declaration(name)['value'])
        if actual != expected:
            raise ValueError(f'mathematical definition differs: {name}')
        encoding = json.dumps(actual, sort_keys=True, separators=(',', ':')).encode()
        print('matching definition', name, hashlib.sha256(encoding).hexdigest())
    current.data.close()
    current.stream.close()
    print('challenge type', hashlib.sha256(external).hexdigest())
    print('spectral premise', hashlib.sha256(local).hexdigest())
    print('specialization premise', hashlib.sha256(specialization).hexdigest())
    if local != specialization:
        raise ValueError('spectral conclusion and conductor-specialization premises differ')
    if external != local:
        from difflib import unified_diff
        print('\n'.join(unified_diff(json.dumps(json.loads(external), indent=1).splitlines(),
                                    json.dumps(json.loads(local), indent=1).splitlines(), n=2)))
        sys.exit(1)
    print('Explicit terms agree after unfolding the proposition and numeral helper and removing binder names.')


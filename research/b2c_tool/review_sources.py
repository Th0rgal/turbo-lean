"""Link report-selected examples to explicit declarations in historical source."""
import hashlib
import json
import pathlib
import re
import subprocess
import sys

from report import nonaux
from run_experiment import CLIFV, DATA

report_path, output_path = map(pathlib.Path, sys.argv[1:])
report = json.loads(report_path.read_text())
examples = {}

def add(label, xs):
    for x in xs:
        ident = x['commit'], x['module'], x['name']
        entry = examples.setdefault(ident, {**x, 'buckets': []})
        assert entry['K'] == x['K'] and entry['kernel_ms'] == x['kernel_ms']
        entry['buckets'].append(label)

add('overall reuse', report['optimistic_kernel_reuse']['examples'])
for field in ('kernel_reuse_by_kind', 'cutoff_kernel_by_kind'):
    for kind, value in report[field].items():
        add(field + ': ' + kind, value['examples'])
for field, key in [('top_20_kernel_reuse_modules', 'kernel_reuse_examples'),
                   ('top_20_module_cutoff_modules', 'cutoff_examples')]:
    for value in report[field]:
        add(field + ': ' + value['module'], value[key])

sources = {}
snapshots = {}
pattern = re.compile(r'^\s*(?:(?:protected|private|noncomputable|unsafe|partial)\s+)*'
                     r'(theorem|lemma|def|abbrev|inductive|structure|axiom|opaque)\s+([^\s(:{]+)')
reviewed = []
pending = []
for ident, x in sorted(examples.items()):
    commit, module, name = ident
    assert nonaux(name)
    source_file = module.replace('.', '/') + '.lean'
    source_key = commit, source_file
    if source_key not in sources:
        sources[source_key] = subprocess.check_output(['git', 'show', commit + ':' + source_file], cwd=CLIFV)
    src = sources[source_key]
    if commit not in snapshots:
        snapshots[commit] = json.loads((DATA / commit[:8] / 'sources.json').read_text())
    digest = hashlib.sha256(src).hexdigest()
    assert digest == snapshots[commit][module]
    matches = []
    for line_number, line in enumerate(src.decode().splitlines(), 1):
        m = pattern.match(line)
        if m and (name == m[2] or name.endswith('.' + m[2])):
            matches.append({'source_line': line_number, 'source_kind': m[1], 'declaration_start': line.strip()})
    if len(matches) != 1:
        pending.append({**x, 'source_file': source_file, 'matching_source_starts': matches})
        continue
    reviewed.append({**x, 'source_file': source_file, 'source_SHA256': digest,
                     **matches[0], 'explicit_source_declaration_verified': True})

out = {'report_SHA256': hashlib.sha256(report_path.read_bytes()).hexdigest(),
       'scope': 'Historical source linkage for the supplied report only; report scope and completion gates remain in force',
       'selected_example_occurrences': len(examples), 'source_linked_examples': len(reviewed),
       'all_selected_examples_source_linked': not pending, 'examples': reviewed, 'pending_review': pending,
       'reported_example_shortfalls': report['example_shortfalls']}
output_path.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: v for k, v in out.items() if k not in ('examples', 'pending_review')}))
for x in pending:
    print('PENDING', x['commit'][:8], x['module'], x['name'], len(x['matching_source_starts']))

if pending:
    raise SystemExit(1)

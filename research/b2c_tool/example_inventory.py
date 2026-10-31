"""Exhaustively inventory measured groups in report example-shortfall buckets.

This explains missing examples; it does not waive the completion requirement.
Run after report.py: example_inventory.py <report.json> <inventory.json>.
"""
import gzip
import hashlib
import json
import pathlib
import sys

from report import nonaux
from run_experiment import DATA


def read_groups(path):
    with gzip.open(path, 'rt') as stream:
        for line in stream:
            yield json.loads(line)


def main():
    report_path, output_path = map(pathlib.Path, sys.argv[1:])
    report = json.loads(report_path.read_text())
    assert len(report['completed_commits']) == 20
    inventories = {}
    for label in report['example_shortfalls']:
        mechanism, category, value = label.split(' ', 2)
        assert mechanism in ('reuse', 'cutoff') and category in ('kind', 'module')
        inventories[label] = {'mechanism': mechanism, 'category': category, 'value': value,
                              'eligible_group_occurrences': 0, 'kernel_cpu_ns': 0,
                              'names': set(), 'excluded_names': set(), 'source_candidates': []}
    transitions = {t['commit']: t for t in report['transitions']}
    previous_keys = set()
    for index, commit in enumerate(report['commits']):
        directory = DATA / commit[:8]
        current_keys = set()
        if index:
            transition = transitions[commit]
            built = {m['module'] for m in json.loads((directory / 'build.json').read_text())['modules']}
            assert built == set(transition['built_modules'])
            cutoff = set(transition['cutoff_avoidable_modules'])
        for group in read_groups(directory / 'kernel_groups.jsonl.gz'):
            current_keys.add(group['K'])
            if not index or not group['module'].startswith('FV.') or group['module'] not in built:
                continue
            reusable = group['kind'] not in ('inductive', 'quotient') and group['K'] in previous_keys
            for bucket in inventories.values():
                eligible = reusable if bucket['mechanism'] == 'reuse' else group['module'] in cutoff
                if not eligible or group[bucket['category']] != bucket['value']:
                    continue
                bucket['eligible_group_occurrences'] += 1
                bucket['kernel_cpu_ns'] += group['cpu_ns']
                for name in group['names']:
                    if nonaux(name):
                        bucket['names'].add(name)
                        bucket['source_candidates'].append({'commit': commit, 'module': group['module'],
                            'kind': group['kind'], 'name': name, 'K': group['K'], 'cpu_ns': group['cpu_ns']})
                    else:
                        bucket['excluded_names'].add(name)
        previous_keys = current_keys
    for bucket in inventories.values():
        bucket['names'] = sorted(bucket['names'])
        bucket['excluded_names'] = sorted(bucket['excluded_names'])
        bucket['distinct_nonauxiliary_names'] = len(bucket['names'])
        bucket['missing_distinct_names'] = max(0, 3 - len(bucket['names']))
        assert bucket['missing_distinct_names'] > 0
    result = {'report_SHA256': hashlib.sha256(report_path.read_bytes()).hexdigest(),
              'scope': 'Exhaustive actual-group inventory for final report shortfalls across C2..C20',
              'completion_requirement_waived': False,
              'example_filter': 'report.nonaux; generated instances, matchers, and hygienic names excluded',
              'buckets': inventories}
    output_path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({label: {'distinct_names': b['distinct_nonauxiliary_names'],
                             'names': b['names'], 'group_occurrences': b['eligible_group_occurrences']}
                      for label, b in inventories.items()}, indent=2))


if __name__ == '__main__':
    main()

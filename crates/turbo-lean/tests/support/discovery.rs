use super::*;
#[path = "corpus.rs"]
mod corpus;

/// Heavy Lean-oracle regression; deliberately NOT ignored: cargo test --release runs it in CI.
#[test]
fn check_decl_corpus_discovery_parity() {
    let tmp = corpus::Temp::new("discovery");
    let mut count = 0;
    let mut missing = Vec::new();
    let mut extra = Vec::new();
    for module in corpus::MODULES {
        let src =
            std::fs::read_to_string(corpus::fixtures().join(format!("{module}.lean"))).unwrap();
        let expected = corpus::oracle(&tmp.0, module, &src);
        let split = split_lean_source(&src, &[]);
        assert!(
            split.eligible_for_sharding,
            "{module}: {:?}",
            split.fallback_reason
        );
        let actual: std::collections::BTreeSet<_> = split
            .shards
            .iter()
            .map(|s| s.qualified_name.clone())
            .collect();
        assert_eq!(
            actual.len(),
            split.shards.len(),
            "duplicate shards in {module}"
        );
        count += expected.len();
        missing.extend(expected.difference(&actual).cloned());
        extra.extend(actual.difference(&expected).cloned());
    }
    eprintln!(
        "A0d discovery: {count} declarations; {} missing, {} extra",
        missing.len(),
        extra.len()
    );
    assert!(
        missing.is_empty() && extra.is_empty(),
        "missing={missing:?}; extra={extra:?}"
    );
}

#[test]
fn qualified_shards_reconstruct_the_correct_namespace() {
    let src = "namespace A\ntheorem same : 1 = 1 := rfl\nend A\nnamespace B\ntheorem same : 2 = 2 := rfl\nend B\n";
    let split = split_lean_source(src, &[]);
    assert_eq!(
        split
            .shards
            .iter()
            .map(|s| s.qualified_name.as_str())
            .collect::<Vec<_>>(),
        ["A.same", "B.same"]
    );
    let b = reconstruct_single_shard_source(src, "B.same")
        .unwrap()
        .unwrap();
    assert!(b.contains("theorem same : 1 = 1  := sorry"));
    assert!(b.contains("theorem same : 2 = 2 := rfl"));
}

#[test]
fn decl_lookup_rejects_ambiguous_suffixes_and_uses_legacy_names() {
    let src = "namespace A\ntheorem same : 1 = 1 := rfl\nend A\nnamespace B\ntheorem same : 2 = 2 := rfl\nend B\n";
    let mut shards = split_lean_source(src, &[]).shards;
    for reverse in [false, true] {
        if reverse {
            shards.reverse();
        }
        let error = find_decl_shard_index(&shards, "same")
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("A.same") && error.contains("B.same"),
            "{error}"
        );
        for target in ["A.same", "B.same"] {
            let idx = find_decl_shard_index(&shards, target).unwrap().unwrap();
            assert_eq!(shards[idx].qualified_name, target);
        }
    }
    let error = reconstruct_single_shard_source(src, "same")
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("A.same") && error.contains("B.same"),
        "{error}"
    );
    assert_eq!(
        find_decl_shard_index(&shards, "Missing.same").unwrap(),
        None
    );
    assert!(!decl_name_matches_target("A.same", "ame"));
    assert!(!decl_name_matches_target("same", "A.same"));
    shards.truncate(1);
    shards[0].qualified_name.clear();
    shards[0].name = "Legacy.same".to_string();
    for target in ["same", "Legacy.same"] {
        assert_eq!(find_decl_shard_index(&shards, target).unwrap(), Some(0));
    }
}

#[test]
fn qualified_targets_select_only_one_proof_in_fast_sources() {
    let src = "import Mathlib.Data.Nat.Basic\nnamespace A\ntheorem same : 1 = 1 := rfl\nend A\nnamespace B\ntheorem same : 2 = 2 := rfl\nend B\n";
    let split = split_lean_source(src, &[]);
    for (target, selected, other) in [("A.same", "1 = 1", "2 = 2"), ("B.same", "2 = 2", "1 = 1")] {
        let names = [target.to_string()].into_iter().collect();
        let pruned = build_pruned_imports_shard_source(src, &names).unwrap();
        assert!(
            pruned.contains(&format!("theorem same : {selected} := rfl")),
            "{pruned}"
        );
        assert!(
            !pruned.contains(&format!("theorem same : {other} := rfl")),
            "{pruned}"
        );
        let fast =
            build_fast_olean_shard_source_with_split(src, &split, "Fixture", &names).unwrap();
        assert_eq!(fast.matches("_turbo_verify_").count(), 1, "{fast}");
        assert!(fast.contains(selected) && !fast.contains(other), "{fast}");
    }
}

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
        let actual: std::collections::BTreeSet<_> =
            split.shards.iter().map(|s| s.name.clone()).collect();
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

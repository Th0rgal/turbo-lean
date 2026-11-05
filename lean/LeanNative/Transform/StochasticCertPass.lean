import LeanNative.Proofs.StochasticCertSoundness

namespace LeanNative.Transform

open LeanNative.Proofs

def verifiedStochasticCertContract (bundle : CertifiedRuleBundle := cachedStochasticBundle) :
    VerifiedCodePassContract where
  name := "StochasticCert"
  theoremRef := "LeanNative.Proofs.applyCertifiedBundleCode_sound"
  notes := "Explicitly loaded certified scalar rewrites; no search at pass runtime"
  runCode := applyCertifiedBundleCode bundle
  sound := applyCertifiedBundleCode_sound bundle

def mkStochasticCertPass (bundle : CertifiedRuleBundle) : TransformPass :=
  TransformPass.ofVerifiedContract (verifiedStochasticCertContract bundle)

def stochasticCertPass : TransformPass := mkStochasticCertPass cachedStochasticBundle

end LeanNative.Transform

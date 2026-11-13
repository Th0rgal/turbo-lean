# C1a WIP checkpoint and preservation policy

Operator requirement acknowledged UTC 2026-11-13T11:59:27.412076+00:00.
Commit and export WIP at least every30minutes and before any VM TTL/cap/stop/
destruction. No credentials on managed VM. Coordinator must authenticate and
push the exported branch, and harvest artifacts off VM. Local export alone
is NOT a completed checkpoint. Require coordinator confirmation of remote
ref and off-VM harvest; no VM cleanup before that confirmation. Any future
child worker must inherit this requirement.

Current implementation and validated binaries: bd58dbedd76a49be3942f3b029d5ac85718589a6.
This checkpoint adds documentation only; no rebuilt binary is claimed.
Final dynamic P0 PASS2/2 (28.920s); trust PASS20/20 (35.107s),12 embedded
runner tests PASS. Final dynamic PCS batch/E2E link PASS; audit598 declarations,
0rejections; unique strong field symbols/CLMUL and130 unchanged cache hashes.
Evidence /var/lib/orb-node/work/c1a-evidence/pcs-final-dynamic.
No matched XMSS1400<1second and<4294967296byte certificate exists.

Prior loss: operator reported mm5xvnw6ha,mm3dagt4ua,mmp2t4xd94 permanently gone.
Historical implementation/cache artifacts were not available to this worker;
reconstruction used public committed references. No direct provider lifecycle
or wipe evidence was supplied to this worker. Expiry/recycling versus wipe
and the precise missing-push cause remain unverified. Current recovery's own
anonymous GitHub push failed; no credentials were sought. This does not prove
the historical push failure mechanism.

## Coordinator lifecycle evidence now published

Read app integration9f5869b9940af259deecbe000a42ff527a40b9d7:plan.md
incident section. It documents mm5xvnw6ha destruction2026-11-11T00:44:03Z
with owner_failed before expiry01:00:47Z. Worker had detached29d85f7 and
uncommitted modifications; final249433-byte patch SHA
c3b93b720d76d5468375f4d30247488382fec23e84983b570aa0002c81417277
was generated00:36:16 but no subsequent commit/push or complete off-VM
harvest receipt was found. Cause: VM destruction carrying unpublished
compiler state without complete off-VM harvest. TTL expiry and workspace
wipe are not demonstrated. Initial owner-failure classification cause
remains unknown; owner_failed does not prove worker tests failed.
This is coordinator-published evidence; raw lifecycle receipts remain on
the coordinator. Distinct C1c mmp2t4xd94 was not the C1a fork.

Coordinator confirmed only older compiler ba5b99b and older15388723-byte
archive4ac1830c... off VM. Latest source and r3 delivery remain pending
remote-ref/off-VM confirmation; do not conflate these checkpoints.

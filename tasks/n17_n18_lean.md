# N17 / N18 Lean specification — 2026-09-24

## Intent

Close the two stretch Lean items of the N block. N18 formalizes the
input-conditioned reconstruction map that §6 says a self following a scene
needs; N17 restates gluing and approximate selection over the decodability
cover of §4 instead of a spatial one.

## N18 — input-conditioned reconstruction (`Phase6_ConditionedReconstruction`)

Data (`ConditionedEncoding`): a relevant family, a declared input `input : S → U`,
an encoder `S → C`, and a readout `U → C → S`. The map is
`F u s = readout u (encode s)`.

1. `dist_le_of_conditioned_contracting`: each `F u` is `Λ`-Lipschitz on the
   family, `F` is `L`-Lipschitz in the input, and every member is reconstructed
   within `ε`. Then `d(s,t) ≤ (2ε + L·d(u_s,u_t))/(1−Λ)`. Constant input
   recovers the fixed-map bound; within one input fibre the fixed-map diameter
   limit still holds.
2. `dist_selfState_le`, `dist_selfState_input_le`: with `S` complete and each `F u` a
   contraction, the fixed points satisfy `d(s_u,s_v) ≤ L·d(u,v)/(1−Λ)` and
   each reconstructed member is within `ε/(1−Λ)` of its input's fixed point.
3. Guard: `card_le_card_codes_fibre` counts codes within one input fibre, and
   `dist_le_of_encode_const` shows a constant encoder (the stored-state
   readout) reconstructs only families whose fibres have diameter `≤ 2ε`.
   The code criterion binds within fibres and nowhere else.

Witness (`Examples/ConditionedReconstruction.lean` §36): four reals in two
fibres, a one-bit code, `Λ = 1/2`, `ε = 3/4`; the family's diameter exceeds every fixed
contraction's limit and each fibre needs both codes. The stored-state witness
reconstructs exactly and its fibres are singletons.

## N17 — the decodability cover (`Phase5_ContentCover`)

Data (`DecodingSetup`): regions `ι`, content variables `V`, states `S` with a
relevant family, each variable's true value `V → S → ℝ`, region readouts and
per-variable decoders. `domain θ i` is the set of variables region `i` decodes
within `θ` on every relevant state.

1. Exact gluing: the partial decodes are sections of the presheaf of functions
   on `V` with the discrete topology, which Mathlib proves is a sheaf; the
   spatial `sheaf_glue_unique` applies verbatim (`decode_glue_unique`).
2. Compatibility is a consequence of decodability: two regions' decodes of a
   shared variable differ by at most `2θ` (`decode_compatible`), attained.
3. Selection over the domains is within `θ` of the true value and within `2θ`
   of each region's decode; two selections differ by at most `2θ`.
4. Decoder-class guard: a region whose readout is injective on the relevant
   family decodes every variable exactly with an unrestricted decoder
   (`exists_exact_decoder_of_injOn`), so its domain is everything.

Not transferred, stated in the docstrings and manuscript: the probability
presheaf and measure representation, the `√N` phase-to-content bounds and nerve
chains (they bound spatial patches of phases), and anything about which cover
is physically correct.

## Constraints

No axioms, `sorry`, toolchain changes or new Python. Doc-strings state scope.
Every name `main.tex` rests on gets a Table S1 row. PDFs, proof companion and
`arxiv_submit/` rebuilt in the commit that changes their sources.

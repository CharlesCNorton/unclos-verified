# Sovereign Geometer

*A Formal Verification of Maritime Law and the South China Sea Arbitration*

Machine-checked proofs that China's Nine-Dash Line claims are invalid under UNCLOS.

**Author:** Charles C. Norton | December 2025

## Background

The United Nations Convention on the Law of the Sea (UNCLOS) establishes the legal framework for maritime sovereignty. Articles 47, 56, 60, and 121 define which geographic features generate exclusive economic zones (EEZ), what ratio constraints apply to archipelagic baselines, and how artificial modifications affect legal status.

In 2016, an Arbitral Tribunal ruled that China's "Nine-Dash Line" claim to the South China Sea was invalid. China rejected the ruling. The dispute continues through artificial island construction and naval presence.

This formalization encodes UNCLOS provisions as Coq predicates and proves the Tribunal's conclusions with mathematical rigor. The disputed features are not merely illegal under treaty interpretation—they fail to satisfy the geometric and logical preconditions for EEZ generation.

## The Main Result

The Nine-Dash Line claim is invalid on three independent grounds:

| Ground | Article | Proof |
| :----- | :------ | :---- |
| Geometric | 47 | Any baseline enclosing the Spratlys yields ratio > 128,000:1; maximum permitted is 9:1 |
| Classificatory | 121(3) | All disputed features are rocks or low-tide elevations; neither generates EEZ |
| Logical | 56 | Historic rights in foreign EEZ contradict the exclusivity that defines EEZ |

Each ground is independently sufficient. The claim fails three different ways.

## What's Proven

The formalization establishes geodetic primitives via the haversine formula on a spherical Earth of radius 3440.065 nautical miles. Maritime zones are defined as buffer regions: territorial sea at 12nm, contiguous zone at 24nm, EEZ at 200nm, extended continental shelf at 350nm. Zone nesting is proven.

Feature classification follows Article 121: islands sustaining human habitation generate full EEZ; rocks above water at high tide generate territorial sea only; low-tide elevations generate nothing. The `generates_eez` function returns false for all four analyzed features (Mischief Reef, Subi Reef, Fiery Cross Reef, Johnson Reef).

Article 47 ratio constraints are verified via interval arithmetic. The minimum enclosing area for the Spratly Islands exceeds 256,000 square nautical miles while maximum land area is under 2 square nautical miles. The ratio theorem proves any enclosing baseline violates the 9:1 ceiling.

Article 60(8) transparency is encoded: `legal_status` ignores artificial modifications. Mischief Reef with 5.6 km² of reclaimed land remains a low-tide elevation. Artificial runways do not create islands.

Historic rights supersession follows from chronology: China ratified UNCLOS on 7 June 1996; the Nine-Dash Line claim dates to 1 December 1947. Ratification extinguished incompatible prior claims. Julian Day arithmetic verifies the ordering.

The Tribunal's jurisdiction is proven despite China's 2006 Article 298 declaration. EEZ entitlement disputes are interpretation/application disputes under Article 286, which Article 298 exclusions do not reach.

## Axiom Status

The formalization contains no axioms and no admitted lemmas. Every theorem, including the winding-number point-in-polygon test cases on synthetic data, depends only on Coq's standard library and the classical Reals axiomatization.

## Files

```
sovereign_geometer.v    Coq proofs (10,918 lines)
```

## Key Theorems

```coq
Theorem scs_features_no_eez :
  forall f, In f scs_disputed_features -> generates_eez f = false.

Theorem universal_baseline_ratio_violation :
  forall baseline enclosed_area land_area,
  encloses_all_scs_features baseline ->
  enclosed_area >= min_enclosing_area_sq_nm ->
  land_area <= max_scs_land_area_sq_nm ->
  (enclosed_area - land_area) / land_area > 9.

Theorem nine_dash_line_superseded :
  claim_extinguished nine_dash_line_claim china.

Theorem nine_dash_line_logical_inconsistency :
  forall historic rights claimant_id coastal,
  historic_rights_compatible historic rights ->
  unclos_compliant rights ->
  claimant_id <> cs_id coastal ->
  ~ historic claimant_id (cs_eez coastal).
```

## Building

Requires Coq 8.19+ with the standard library Reals.

```bash
coqc sovereign_geometer.v
```

Verification takes approximately 2-3 minutes depending on hardware.

## References

- PCA Case No. 2013-19, Award of 12 July 2016
- United Nations Convention on the Law of the Sea (1982)
- UN Treaty Collection, Chapter XXI.6 (UNCLOS status)
- Gao & Jia, "The Nine-Dash Line in the South China Sea" (2013) 107 AJIL 98

# SHA-3: EasyCrypt → Gaudí declaration mapping

Source: <https://gitlab.com/easycrypt/sha3> at `4315ef7` (2026-05-07), the security part only
(`proof/`, `proof/smart_counter/`).  Generated from the sources (comments stripped, `clone … with`
substitutions skipped): one row per top-level declaration, in file order.  Conventions in
`README.md`; deviations in `Exceptions.md`.

Status: `—` not started · `def` definition ported · `stated` statement ported, proof `sorry` ·
`done` proven · `exc` deviation (see `Exceptions.md`).

| EC file | lines | lemmas | Lean file |
|---|---:|---:|---|
| `proof/Common.ec` | 734 | 64 | `GaudisCrypt/Examples/SHA3/Common.lean` |
| `proof/Indifferentiability.eca` | 69 | 0 | `GaudisCrypt/Examples/SHA3/Indifferentiability.lean` |
| `proof/OptionIndifferentiability.eca` | 62 | 0 | `GaudisCrypt/Examples/SHA3/OptionIndifferentiability.lean` |
| `proof/IRO.eca` | 131 | 1 | `GaudisCrypt/Examples/SHA3/IRO.lean` |
| `proof/smart_counter/SLCommon.ec` | 1074 | 65 | `GaudisCrypt/Examples/SHA3/SmartCounter/SLCommon.lean` |
| `proof/smart_counter/ConcreteF.eca` | 461 | 3 | `GaudisCrypt/Examples/SHA3/SmartCounter/ConcreteF.lean` |
| `proof/smart_counter/Handle.eca` | 2723 | 64 | `GaudisCrypt/Examples/SHA3/SmartCounter/Handle.lean` |
| `proof/smart_counter/Gcol.eca` | 359 | 8 | `GaudisCrypt/Examples/SHA3/SmartCounter/Gcol.lean` |
| `proof/smart_counter/Gext.eca` | 727 | 13 | `GaudisCrypt/Examples/SHA3/SmartCounter/Gext.lean` |
| `proof/smart_counter/Gconcl.ec` | 390 | 4 | `GaudisCrypt/Examples/SHA3/SmartCounter/Gconcl.lean` |
| `proof/BlockSponge.ec` | 149 | 2 | `GaudisCrypt/Examples/SHA3/BlockSponge.lean` |
| `proof/smart_counter/Gconcl_list.ec` | 2221 | 48 | `GaudisCrypt/Examples/SHA3/SmartCounter/Gconcl_list.lean` |
| `proof/Sponge.ec` | 2164 | 75 | `GaudisCrypt/Examples/SHA3/Sponge.lean` |
| `proof/SHA3Indiff.ec` | 322 | 7 | `GaudisCrypt/Examples/SHA3/SHA3Indiff.lean` |
| `proof/SHA3_OIndiff.ec` | 260 | 1 | `GaudisCrypt/Examples/SHA3/SHA3_OIndiff.lean` |
| `proof/SecureHash.eca` | 148 | 0 | `GaudisCrypt/Examples/SHA3/SecureHash.lean` |
| `proof/SecureRO.eca` | 526 | 3 | `GaudisCrypt/Examples/SHA3/SecureRO.lean` |
| `proof/SecureORO.eca` | 492 | 3 | `GaudisCrypt/Examples/SHA3/SecureORO.lean` |
| `proof/IndifRO_is_secure.ec` | 218 | 3 | `GaudisCrypt/Examples/SHA3/IndifRO_is_secure.lean` |
| `proof/SHA3Security.ec` | 1275 | 23 | `GaudisCrypt/Examples/SHA3/SHA3Security.lean` |
| `proof/SHA3OSecurity.ec` | 2652 | 41 | `GaudisCrypt/Examples/SHA3/SHA3OSecurity.lean` |

## `proof/Common.ec`

Lean: `GaudisCrypt/Examples/SHA3/Common.lean`, namespace `GaudisCrypt.SHA3.Common`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 11 | op | `r` |  | `r`, `ge2_r` (fields of `Params`) | def |
| 12 | op | `c` |  | `c`, `gt0_c` (fields of `Params`) | def |
| 16 | lemma | `gt0_r` |  | `gt0_r` | done |
| 19 | lemma | `ge0_r` |  | `ge0_r` | done |
| 22 | lemma | `ge0_c` |  | `ge0_c` | done |
| 26 | clone export | `BitWord` |  | `Capacity` | def |
| 36 | clone export | `BitWord` |  | `Block` | def |
| 46 | op | `cdistr` |  | `cdistr` | def |
| 47 | op | `bdistr` |  | `bdistr` | def |
| 52 | lemma | `dvdz_close` |  | `dvdz_close` | done |
| 67 | lemma | `chunk_nil'` |  | `chunk_nil'` | done |
| 70 | lemma | `chunk_sing'` |  | `chunk_sing'` | done |
| 78 | lemma | `b0P` |  | `b0P` | done |
| 85 | lemma | `bits2w_inj_eq` |  | `bits2w_inj_eq` | done |
| 89 | lemma | `last_drop_all_but_last` |  | `last_drop_all_but_last` | done |
| 102 | clone export | `PRP` |  | `PRPSec (PRP clone, at D := block × capacity)` | def |
| 105 | clone export | `StrongPRP` |  | `PRPSec` | def |
| 107 | clone export | `RP` |  | `Perm, dD, dD_ll, PRIMITIVE` | def |
| 119 | lemma | `needed_blocks0` |  | `needed_blocks0` | done |
| 124 | lemma | `needed_blocks_non_pos` |  | `needed_blocks_non_pos` | done |
| 133 | lemma | `needed_blocks_suff` |  | `needed_blocks_suff` | done |
| 142 | lemma | `needed_blocks_correct` |  | `needed_blocks_correct` | done |
| 156 | lemma | `needed_blocks_prod_r` |  | `needed_blocks_prod_r` | done |
| 163 | lemma | `needed_blocks_eq_div_r` |  | `needed_blocks_eq_div_r` | done |
| 181 | lemma | `needed_blocks_succ_eq_div_r` |  | `needed_blocks_succ_eq_div_r` | done |
| 211 | lemma | `needed_blocks_rel_div_r` |  | `needed_blocks_rel_div_r` | done |
| 221 | op | `num0` |  | `num0` | def |
| 223 | op | `mkpad` |  | `mkpad` | def |
| 225 | op | `pad` |  | `pad` | def |
| 227 | op | `unpad` |  | `unpad` | def |
| 234 | lemma | `rev_mkpad` |  | `rev_mkpad` | done |
| 237 | lemma | `last_mkpad` |  | `last_mkpad` | done |
| 240 | lemma | `head_mkpad` |  | `head_mkpad` | done |
| 243 | lemma | `last_pad` |  | `last_pad` | done |
| 246 | lemma | `size_mkpad` |  | `size_mkpad` | done |
| 252 | lemma | `size_pad_equiv` |  | `size_pad_equiv` | done |
| 259 | lemma | `size_padE` |  | `size_padE` | done |
| 263 | lemma | `size_pad` |  | `size_pad` | done |
| 267 | lemma | `size_pad_dvd_r` |  | `size_pad_dvd_r` | done |
| 270 | lemma | `dvd_r_num0` |  | `dvd_r_num0` | done |
| 273 | lemma | `num0_ge0` |  | `num0_ge0` | done |
| 276 | lemma | `num0_ltr` |  | `num0_ltr` | done |
| 279 | lemma | `index_true_behead_mkpad` |  | `index_true_behead_mkpad` | done |
| 286 | lemma | `padE` |  | `padE` | done |
| 294 | lemma | `padK` |  | `padK` | done |
| 315 | lemma | `unpadK` |  | `unpadK` | done |
| 342 | inductive | `unpad_spec` |  | `unpad_spec` | def |
| 348 | lemma | `unpadP` |  | `unpadP` | done |
| 361 | op | `chunk` |  | `chunk` | def |
| 363 | lemma | `size_chunk` |  | `size_chunk` | done |
| 366 | lemma | `in_chunk_size` |  | `in_chunk_size` | done |
| 369 | lemma | `chunkK` |  | `chunkK` | done |
| 372 | lemma | `chunk_nil` |  | `chunk_nil` | done |
| 375 | lemma | `chunk_sing` |  | `chunk_sing` | done |
| 378 | lemma | `chunk_cat` |  | `chunk_cat` | done |
| 382 | lemma | `chunk_padK` |  | `chunk_padK` | done |
| 385 | lemma | `flattenK` |  | `flattenK` | done |
| 391 | op | `blocks2bits` |  | `blocks2bits` | def |
| 393 | lemma | `blocks2bits_nil` |  | `blocks2bits_nil` | done |
| 396 | lemma | `blocks2bits_sing` |  | `blocks2bits_sing` | done |
| 399 | lemma | `blocks2bits_cat` |  | `blocks2bits_cat` | done |
| 403 | lemma | `size_blocks2bits` |  | `size_blocks2bits` | done |
| 411 | lemma | `size_blocks2bits_dvd_r` |  | `size_blocks2bits_dvd_r` | done |
| 414 | op | `bits2blocks` |  | `bits2blocks` | def |
| 416 | lemma | `bits2blocks_nil` |  | `bits2blocks_nil` | done |
| 419 | lemma | `bits2blocks_sing` |  | `bits2blocks_sing` | done |
| 423 | lemma | `bits2blocks_cat` |  | `bits2blocks_cat` | done |
| 430 | lemma | `blocks2bitsK` |  | `blocks2bitsK` | done |
| 438 | lemma | `bits2blocksK` |  | `bits2blocksK` | done |
| 454 | op | `pad2blocks` |  | `pad2blocks` | def |
| 455 | op | `unpad_blocks` |  | `unpad_blocks` | def |
| 457 | lemma | `pad2blocksK` |  | `pad2blocksK` | done |
| 463 | lemma | `unpadBlocksK` |  | `unpadBlocksK` | done |
| 476 | lemma | `pad2blocks_inj` |  | `pad2blocks_inj` | done |
| 481 | lemma | `size_pad2blocks` |  | `size_pad2blocks` | done |
| 492 | op | `extend` |  | `extend` | def |
| 495 | op | `strip` |  | `strip` | def |
| 499 | lemma | `strip_ge0` |  | `strip_ge0` | done |
| 503 | lemma | `extendK` |  | `extendK` | done |
| 521 | lemma | `stripK` |  | `stripK` | done |
| 545 | op | `valid_toplevel` |  | `valid_toplevel` | def |
| 549 | op | `valid_block` |  | `valid_block` | def |
| 551 | lemma | `valid_pad2blocks` |  | `valid_pad2blocks` | done |
| 557 | inductive | `valid_block_spec` |  | `valid_block_spec` | def |
| 562 | lemma | `valid_blockP` |  | `valid_blockP` | done |
| 575 | lemma | `valid_block_ends_not_b0` |  | `valid_block_ends_not_b0` | done |
| 598 | inductive | `valid_block_struct_spec` |  | `valid_block_struct_spec` | def |
| 608 | lemma | `valid_block_structP` |  | `valid_block_structP` | done |
| 718 | op | `valid_absorb` |  | `valid_absorb` | def |
| 720 | inductive | `valid_absorb_spec` |  | `valid_absorb_spec` | def |
| 726 | lemma | `valid_absorbP` |  | `valid_absorbP` | done |

## `proof/Indifferentiability.eca`

Lean: `GaudisCrypt/Examples/SHA3/Indifferentiability.lean`, namespace `GaudisCrypt.SHA3.Indifferentiability`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 2 | type | `p.` |  | `p.` | def |
| 4 | module type | `PRIMITIVE` |  | `PRIMITIVE` | def |
| 10 | module type | `DPRIMITIVE` |  | `DPRIMITIVE` | def |
| 16 | type | `f_in` |  | `f_in` | def |
| 18 | module type | `FUNCTIONALITY` |  | `FUNCTIONALITY` | def |
| 23 | module type | `DFUNCTIONALITY` |  | `DFUNCTIONALITY` | def |
| 33 | module type | `CONSTRUCTION` |  | `CONSTRUCTION` | def |
| 38 | module type | `SIMULATOR` |  | `SIMULATOR` | def |
| 44 | module type | `DISTINGUISHER` |  | `DISTINGUISHER` | def |
| 48 | module | `Indif` |  | `Indif` | def |
| 60 | module | `GReal` |  | `GReal` | def |
| 61 | module | `GIdeal` |  | `GIdeal` | def |

## `proof/OptionIndifferentiability.eca`

Lean: `GaudisCrypt/Examples/SHA3/OptionIndifferentiability.lean`, namespace `GaudisCrypt.SHA3.OptionIndifferentiability`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 2 | type | `p.` |  | `p.` | def |
| 4 | module type | `OPRIMITIVE` |  | `OPRIMITIVE` | def |
| 10 | module type | `ODPRIMITIVE` |  | `ODPRIMITIVE` | def |
| 16 | type | `f_in` |  | `f_in` | def |
| 18 | module type | `OFUNCTIONALITY` |  | `OFUNCTIONALITY` | def |
| 23 | module type | `ODFUNCTIONALITY` |  | `ODFUNCTIONALITY` | def |
| 33 | module type | `OCONSTRUCTION` |  | `OCONSTRUCTION` | def |
| 38 | module type | `OSIMULATOR` |  | `OSIMULATOR` | def |
| 44 | module type | `ODISTINGUISHER` |  | `ODISTINGUISHER` | def |
| 48 | module | `OIndif` |  | `OIndif` | def |
| 60 | module | `OGReal` |  | `OGReal` | def |
| 61 | module | `OGIdeal` |  | `OGIdeal` | def |

## `proof/IRO.eca`

Lean: `GaudisCrypt/Examples/SHA3/IRO.lean`, namespace `GaudisCrypt.SHA3.IRO`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 8 | type | `to`, `from` |  | `«to»`, `«from»` (section variables) | def |
| 10 | op | `valid` |  | `valid` | def |
| 11 | op | `dto` |  | `dto` | def |
| 13 | module type | `IRO` |  | `IRO_T` | exc (E3) |
| 20 | pred | `prefix_closed` |  | `prefix_closed` | def |
| 26 | pred | `prefix_closed'` |  | `prefix_closed'` | def |
| 32 | lemma | `prefix_closed_equiv` |  | `prefix_closed_equiv` | done |
| 37 | module | `IRO` |  | `IRO` | def |
| 73 | module | `IRO'` |  | `IRO'` | def |

## `proof/smart_counter/SLCommon.ec`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/SLCommon.lean`, namespace `GaudisCrypt.SHA3.SLCommon`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 17 | type | `state` |  | `state` | def |
| 18 | op | `dstate` |  | `dstate` | def |
| 20 | clone include | `Indifferentiability` |  | `Indifferentiability` | def |
| 29 | op | `max_size` |  | `max_size`, `max_ge0` (fields of `Params`) | def |
| 32 | clone export | `Tuple` |  | `Tuple` | def |
| 37 | op | `bl_enum` |  | `bl_enum` | def |
| 38 | op | `bl_univ` |  | `bl_univ` | def |
| 43 | clone import | `FullRO` |  | `FullRO` | def |
| 51 | module | `Redo` |  | `Redo` | def |
| 60 | module | `SqueezelessSponge` |  | `SqueezelessSponge` | def |
| 84 | clone export | `DProd.ProdSampling` |  | `DProd.ProdSampling` | def |
| 91 | op | `incl` |  | `incl` | def |
| 97 | type | `handle` |  | `handle` | def |
| 99 | type | `hstate` |  | `hstate` | def |
| 101 | type | `ccapacity` |  | `ccapacity` | def |
| 103 | type | `smap` |  | `smap` | def |
| 104 | type | `hsmap` |  | `hsmap` | def |
| 105 | type | `handles` |  | `handles` | def |
| 107 | pred | `is_pre_permutation` |  | `is_pre_permutation` | def |
| 111 | lemma | `half_permutation_set` |  | `half_permutation_set` | done |
| 122 | lemma | `pre_permutation_set` |  | `pre_permutation_set` | done |
| 131 | op | `step_hpath` |  | `step_hpath` | def |
| 138 | op | `build_hpath` |  | `build_hpath` | def |
| 141 | inductive | `build_hpath_spec` |  | `build_hpath_spec` | def |
| 149 | lemma | `build_hpathP` |  | `build_hpathP` | done |
| 169 | lemma | `build_hpath_map0` |  | `build_hpath_map0` | done |
| 177 | theory | `Prefix.` | theory Prefix. | `Prefix` (namespace) | def |
| 179 | op | `prefix` | theory Prefix. | `Prefix.«prefix»` | def |
| 185 | lemma | `prefix0s` | theory Prefix. | `Prefix.prefix0s` | done |
| 188 | lemma | `prefixs0` | theory Prefix. | `Prefix.prefixs0` | done |
| 191 | lemma | `prefix_eq` | theory Prefix. | `Prefix.prefix_eq` | done |
| 195 | lemma | `prefixC` | theory Prefix. | `Prefix.prefixC` | done |
| 203 | lemma | `prefix_ge0` | theory Prefix. | `Prefix.prefix_ge0` | done |
| 211 | lemma | `prefix_sizel` | theory Prefix. | `Prefix.prefix_sizel` | done |
| 219 | lemma | `prefix_sizer` | theory Prefix. | `Prefix.prefix_sizer` | done |
| 225 | lemma | `prefix_take` | theory Prefix. | `Prefix.prefix_take` | done |
| 234 | lemma | `take_take` | theory Prefix. | `Prefix.take_take` | done |
| 250 | lemma | `prefix_take_leq` | theory Prefix. | `Prefix.prefix_take_leq` | done |
| 257 | lemma | `prefix_nth` | theory Prefix. | `Prefix.prefix_nth` | done |
| 268 | op | `max_prefix` | theory Prefix. | `Prefix.max_prefix` | def |
| 274 | op | `get_max_prefix` | theory Prefix. | `Prefix.get_max_prefix` | def |
| 278 | pred | `prefix_inv` | theory Prefix. | `Prefix.prefix_inv` | def |
| 289 | pred | `all_prefixes` | theory Prefix. | `Prefix.all_prefixes` | def |
| 292 | lemma | `aux_mem_get_max_prefix` | theory Prefix. | `Prefix.aux_mem_get_max_prefix` | done |
| 301 | lemma | `mem_get_max_prefix` | theory Prefix. | `Prefix.mem_get_max_prefix` | done |
| 308 | lemma | `take_get_max_prefix` | theory Prefix. | `Prefix.take_get_max_prefix` | done |
| 317 | lemma | `take_get_max_prefix2` | theory Prefix. | `Prefix.take_get_max_prefix2` | done |
| 328 | lemma | `prefix_cat` | theory Prefix. | `Prefix.prefix_cat` | done |
| 332 | lemma | `prefix_leq_take` | theory Prefix. | `Prefix.prefix_leq_take` | done |
| 342 | lemma | `prefix0` | theory Prefix. | `Prefix.prefix0` | done |
| 350 | lemma | `head_nth0` | theory Prefix. | `Prefix.head_nth0` | done |
| 353 | lemma | `get_prefix` | theory Prefix. | `Prefix.get_prefix` | done |
| 386 | lemma | `get_max_prefix_leq` | theory Prefix. | `Prefix.get_max_prefix_leq` | done |
| 390 | lemma | `get_max_prefix_is_max` | theory Prefix. | `Prefix.get_max_prefix_is_max` | done |
| 397 | lemma | `get_max_prefix_max` | theory Prefix. | `Prefix.get_max_prefix_max` | done |
| 402 | lemma | `all_take_in` | theory Prefix. | `Prefix.all_take_in` | done |
| 416 | lemma | `prefix_inv_leq` | theory Prefix. | `Prefix.prefix_inv_leq` | done |
| 434 | lemma | `max_prefix_eq` | theory Prefix. | `Prefix.max_prefix_eq` | done |
| 440 | lemma | `prefix_max_prefix_eq_size` | theory Prefix. | `Prefix.prefix_max_prefix_eq_size` | done |
| 456 | lemma | `prefix_get_max_prefix_eq_size` | theory Prefix. | `Prefix.prefix_get_max_prefix_eq_size` | done |
| 463 | lemma | `get_max_prefix_exists` | theory Prefix. | `Prefix.get_max_prefix_exists` | done |
| 473 | lemma | `prefix_geq` | theory Prefix. | `Prefix.prefix_geq` | done |
| 482 | lemma | `prefix_take_prefix` | theory Prefix. | `Prefix.prefix_take_prefix` | done |
| 491 | lemma | `prefix_leq_prefix_cat` | theory Prefix. | `Prefix.prefix_leq_prefix_cat` | done |
| 498 | lemma | `prefix_take_leq_prefix` | theory Prefix. | `Prefix.prefix_take_leq_prefix` | done |
| 506 | lemma | `prefix_take_geq_prefix` | theory Prefix. | `Prefix.prefix_take_geq_prefix` | done |
| 519 | lemma | `get_max_prefix_take` | theory Prefix. | `Prefix.get_max_prefix_take` | done |
| 534 | lemma | `drop_prefix_neq` | theory Prefix. | `Prefix.drop_prefix_neq` | done |
| 541 | lemma | `prefix_prefix_prefix` | theory Prefix. | `Prefix.prefix_prefix_prefix` | done |
| 548 | lemma | `prefix_lt_size` | theory Prefix. | `Prefix.prefix_lt_size` | done |
| 574 | lemma | `asfadst` | theory Prefix. | `Prefix.asfadst` | done |
| 589 | lemma | `prefix_exchange_prefix_inv` | theory Prefix. | `Prefix.prefix_exchange_prefix_inv` | done |
| 606 | lemma | `prefix_inv_nil` | theory Prefix. | `Prefix.prefix_inv_nil` | done |
| 616 | lemma | `aux_prefix_exchange` | theory Prefix. | `Prefix.aux_prefix_exchange` | done |
| 634 | lemma | `prefix_exchange` | theory Prefix. | `Prefix.prefix_exchange` | done |
| 654 | pred | `all_prefixes_fset` | theory Prefix. | `Prefix.all_prefixes_fset` | def |
| 657 | pred | `inv_prefix_block` | theory Prefix. | `Prefix.inv_prefix_block` | def |
| 664 | lemma | `prefix_gt0_mem` | theory Prefix. | `Prefix.prefix_gt0_mem` | done |
| 673 | lemma | `inv_prefix_block_mem_take` | theory Prefix. | `Prefix.inv_prefix_block_mem_take` | done |
| 686 | lemma | `prefix_cat_leq_prefix_size` | theory Prefix. | `Prefix.prefix_cat_leq_prefix_size` | done |
| 694 | lemma | `prefix_cat1` | theory Prefix. | `Prefix.prefix_cat1` | done |
| 707 | lemma | `prefix_leq_prefix_cat_size` | theory Prefix. | `Prefix.prefix_leq_prefix_cat_size` | done |
| 753 | lemma | `diff_size_prefix_leq_cat` | theory Prefix. | `Prefix.diff_size_prefix_leq_cat` | done |
| 787 | pred | `invm` | theory Prefix. | `Prefix.invm` | def |
| 790 | lemma | `invm_set` | theory Prefix. | `Prefix.invm_set` | done |
| 807 | module | `C` |  | `C` | def |
| 816 | module | `PC` |  | `PC` | def |
| 839 | module | `DPRestr` |  | `DPRestr` | def |
| 861 | module | `PRestr` |  | `PRestr` (Lean function, `T.mk`) | def |
| 874 | module | `FC` |  | `FC` | def |
| 893 | module | `DFRestr` |  | `DFRestr` | def |
| 910 | module | `FRestr` |  | `FRestr` (Lean function, `T.mk`) | def |
| 923 | module | `DRestr` |  | `DRestr` (`D` a Lean parameter) | def |
| 932 | lemma | `rp_ll` |  | `rp_ll` | done |
| 935 | lemma | `rpi_ll` |  | `rpi_ll` | done |
| 938 | lemma | `rf_ll` |  | `rf_ll` | done |
| 941 | lemma | `DRestr_ll` |  | `DRestr_ll` (`{-DRestr(D)}` as `C.footprint ⊔ glob D`; `D` with `Module.ECModule`, E2) | done |
| 957 | declare module | `F` | section RESTR. | `F` | def |
| 958 | declare module | `P` | section RESTR. | `P` | def |
| 959 | declare module | `D` | section RESTR. | `D` | def |
| 961 | lemma | `swap_restr` | section RESTR. | `swap_restr` | done |
| 974 | declare module | `P` | section COUNT. | `P` | def |
| 975 | declare module | `CO` | section COUNT. | `CO` | def |
| 976 | declare module | `D` | section COUNT. | `D` | def |
| 978 | declare axiom | `f_ll` | section COUNT. | `f_ll` (hypothesis) | def |
| 979 | declare axiom | `fi_ll` | section COUNT. | `fi_ll` (hypothesis) | def |
| 981 | declare axiom | `CO_ll` | section COUNT. | `CO_ll` (hypothesis) | def |
| 983 | declare axiom | `D_ll` | section COUNT. | `D_ll` (hypothesis) | def |
| 987 | lemma | `Pr_restr` | section COUNT. | `Pr_restr` (`call (: bad, inv)`: `prhlProc_abstract_call_upto_module`, E11; its oracle subgoals `Pr_restr_F_upto`, `Pr_restr_f(i)_upto`, `FC_f_bad`, `PC_f(i)_bad`) | done |
| 1014 | op | `hinv` |  | `hinv` | def |
| 1017 | op | `hinvK` |  | `hinvK` | def |
| 1020 | op | `huniq` |  | `huniq` | def |
| 1026 | lemma | `hinvP` |  | `hinvP` | done |
| 1036 | lemma | `huniq_hinv` |  | `huniq_hinv` | done |
| 1048 | lemma | `hinvKP` |  | `hinvKP` | done |
| 1058 | lemma | `huniq_hinvK` |  | `huniq_hinvK` | done |
| 1065 | lemma | `huniq_hinvK_h` |  | `huniq_hinvK_h` | done |
| 1073 | module | `GReal` |  | `GReal` (definition) | def |

## `proof/smart_counter/ConcreteF.eca`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/ConcreteF.lean`, namespace `GaudisCrypt.SHA3.ConcreteF`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 8 | module | `PF` |  | `PF` | def |
| 42 | module | `CF` |  | `CF` (definition) | def |
| 45 | declare module | `D` | section . | `D` (section variable) | def |
| 47 | declare axiom | `D_ll` | section . | `D_ll` (hypothesis) | def |
| 51 | local module | `GReal'` | section . | `GReal'` (definition) | def |
| 53 | local clone import | `Strong_RP_RF` | section . | `Switching` (namespace; variables are lens parameters, E6) | def (`realize uD_uf_fu`: `Switching.uD_uf_fu`, done) |
| 77 | lemma | `size_behead` | section . | `size_behead` | done |
| 80 | local module | `` | section . | `` | def |
| 88 | local lemma | `DoubleBounding` | section . | `DoubleBounding` | stated |
| 220 | local clone import | `ProdSampling` | section . | `S` | def |
| 224 | lemma | `Real_Concrete` | section . | `Real_Concrete` | stated |

## `proof/smart_counter/Handle.eca`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Handle.lean`, namespace `GaudisCrypt.SHA3.Handle`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 10 | clone export | `PROM.FullRO` |  | `ROhandle` (namespace), `FRO.m` | def |
| 18 | clone export | `ConcreteF` |  | `open ConcreteF` | def |
| 20 | module | `G1` |  | `G1.M`, `G1.S` (modules), `G1` (`D` a Lean parameter) | def |
| 27 | module | `M` | module G1 | `G1.M` | def |
| 58 | module | `S` | module G1 | `G1.S` | def |
| 179 | inductive | `m_mh` |  | `m_mh` | def |
| 195 | inductive | `m_p` |  | `m_p` | def |
| 210 | inductive | `ro_p` |  | `ro_p` | def |
| 214 | inductive | `mh_spec` |  | `mh_spec` | def |
| 237 | inductive | `pi_spec` |  | `pi_spec` | def |
| 245 | inductive | `hs_spec` |  | `hs_spec` | def |
| 251 | inductive | `inv_spec` |  | `inv_spec` | def |
| 255 | inductive | `INV_CF_G1` |  | `INV_CF_G1` | def |
| 272 | lemma | `m_mh_of_INV` |  | `m_mh_of_INV` | done |
| 281 | lemma | `mi_mhi_of_INV` |  | `mi_mhi_of_INV` | done |
| 290 | lemma | `incl_of_INV` |  | `incl_of_INV` | done |
| 299 | lemma | `incli_of_INV` |  | `incli_of_INV` | done |
| 308 | lemma | `mh_of_INV` |  | `mh_of_INV` | done |
| 316 | lemma | `pi_of_INV` |  | `pi_of_INV` | done |
| 324 | lemma | `hs_of_INV` |  | `hs_of_INV` | done |
| 332 | lemma | `inv_of_INV` |  | `inv_of_INV` | done |
| 338 | lemma | `invG_of_INV` |  | `invG_of_INV` | done |
| 348 | lemma | `m_p_of_INV` |  | `m_p_of_INV` | done |
| 353 | lemma | `all_prefixes_of_m_p` |  | `all_prefixes_of_m_p` | done |
| 364 | lemma | `all_prefixes_of_INV` |  | `all_prefixes_of_INV` | done |
| 375 | lemma | `ch_gt0` |  | `ch_gt0` | done |
| 378 | lemma | `ch_neq0` |  | `ch_neq0` | done |
| 381 | lemma | `ch_notdomE_hs` |  | `ch_notdomE_hs` | done |
| 386 | lemma | `Sch_notdomE_hs` |  | `Sch_notdomE_hs` | done |
| 391 | lemma | `ch_notdomE2_mh` |  | `ch_notdomE2_mh` | done |
| 401 | lemma | `Sch_notdomE2_mh` |  | `Sch_notdomE2_mh` | done |
| 411 | lemma | `dom_hs_neq_ch` |  | `dom_hs_neq_ch` | done |
| 417 | lemma | `dom_hs_neq_Sch` |  | `dom_hs_neq_Sch` | done |
| 423 | lemma | `notin_m_notin_mh` |  | `notin_m_notin_mh` | done |
| 433 | lemma | `notin_m_notin_Gm` |  | `notin_m_notin_Gm` | done |
| 439 | lemma | `notin_hs_notdomE2_mh` |  | `notin_hs_notdomE2_mh` | done |
| 449 | lemma | `m_mh_addh` |  | `m_mh_addh` | done |
| 465 | lemma | `m_mh_updh` |  | `m_mh_updh` | done |
| 487 | lemma | `m_mh_addh_addm` |  | `m_mh_addh_addm` | done |
| 508 | lemma | `mi_mhi_addh_addmi` |  | `mi_mhi_addh_addmi` | done |
| 529 | lemma | `inv_mh_inv_Pm` |  | `inv_mh_inv_Pm` | done |
| 544 | lemma | `inv_incl_none` |  | `inv_incl_none` | done |
| 563 | lemma | `huniq_addh` |  | `huniq_addh` | done |
| 576 | lemma | `hs_addh` |  | `hs_addh` | done |
| 591 | lemma | `hs_updh` |  | `hs_updh` | done |
| 610 | lemma | `mh_addh` |  | `mh_addh` | done |
| 623 | lemma | `inv_addm` |  | `inv_addm` | done |
| 637 | lemma | `incl_addm` |  | `incl_addm` | done |
| 643 | op | `getflag` |  | `getflag` | def |
| 646 | lemma | `getflagP_none` |  | `getflagP_none` | done |
| 650 | lemma | `getflagP_some` |  | `getflagP_some` | done |
| 666 | lemma | `build_hpath_prefix` |  | `build_hpath_prefix` | done |
| 676 | lemma | `build_hpath_up` |  | `build_hpath_up` | done |
| 688 | lemma | `build_hpath_down` |  | `build_hpath_down` | done |
| 702 | lemma | `known_path_uniq` |  | `known_path_uniq` | done |
| 716 | lemma | `path_split` |  | `path_split` | done |
| 742 | lemma | `lemma1` |  | `lemma1` | done |
| 849 | lemma | `lemma1'` |  | `lemma1'` | done |
| 955 | lemma | `lemma2` |  | `lemma2` | done |
| 1053 | lemma | `lemma2'` |  | `lemma2'` | done |
| 1165 | lemma | `lemma3` |  | `lemma3` | done |
| 1247 | lemma | `m_mh_None` |  | `m_mh_None` | done |
| 1257 | lemma | `build_hpath_None` |  | `build_hpath_None` | done |
| 1261 | lemma | `build_hpath_upd_ch` |  | `build_hpath_upd_ch` | done |
| 1282 | lemma | `build_hpath_up_None` |  | `build_hpath_up_None` | done |
| 1309 | lemma | `build_hpath_upd_ch_iff` |  | `build_hpath_upd_ch_iff` | done |
| 1326 | lemma | `lemma4` |  | `lemma4` | done |
| 1349 | equiv | `eq_fi` |  | `eq_fi` | stated |
| 1488 | equiv | `eq_f` |  | `eq_f` | stated |
| 1815 | lemma | `head_nth` |  | `head_nth` | done |
| 1818 | lemma | `drop_add` |  | `drop_add` | done |
| 1824 | lemma | `behead_drop` |  | `behead_drop` | done |
| 1827 | lemma | `incl_upd_nin` |  | `incl_upd_nin` | done |
| 1836 | lemma | `lemma5` |  | `lemma5` | done |
| 1863 | lemma | `lemma5'` |  | `lemma5'` | done |
| 1895 | equiv | `PFf_Cf` |  | `PFf_Cf` | stated |
| 2589 | declare module | `D` | section AUX. | `D` (section variable) | def |
| 2591 | declare axiom | `D_ll` | section AUX. | `D_ll` (hypothesis) | def |
| 2595 | equiv | `CF_G1` | section AUX. | `CF_G1` | stated |
| 2697 | declare module | `D` | section . | `D` (section variable) | def |
| 2699 | declare axiom | `D_ll` | section . | `D_ll` (hypothesis) | def |
| 2703 | lemma | `Real_G1` | section . | `Real_G1` | stated |

## `proof/smart_counter/Gcol.eca`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Gcol.lean`, namespace `GaudisCrypt.SHA3.Gcol`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 9 | clone export | `Handle` |  | `open Handle` | def |
| 14 | lemma | `c_gt0r` |  | `c_gt0r` | done |
| 17 | lemma | `c_ge0r` |  | `c_ge0r` | done |
| 20 | lemma | `eps_ge0` |  | `eps_ge0` | done |
| 27 | declare module | `D` | section PROOF. | `D` (section variable) | def |
| 29 | declare axiom | `D_ll` | section PROOF. | `D_ll` (hypothesis) | def |
| 33 | local module | `Gcol` | section PROOF. | `Gcol.sample_c`, `Gcol.M`, `Gcol.S` (modules), `Gcol` (`D` a Lean parameter); variable: lens `Gcol_count`, E6 | def |
| 49 | module | `M` | section PROOF. | `Gcol.M` | def |
| 78 | module | `S` | section PROOF. | `Gcol.S` | def |
| 181 | lemma | `card_rng_set` | section PROOF. | `card_rng_set` | done |
| 190 | lemma | `hinv_image` | section PROOF. | `hinv_image` | done |
| 199 | local lemma | `Pr_col` | section PROOF. | `Pr_col` | done |
| 220 | local equiv | `G1_col` | section PROOF. | `G1_col` (oracle steps `S_f_col`, `S_fi_col`, `M_f_col`, wrappers `DPRestr_f_col`, `DPRestr_fi_col`, `DFRestr_f_col`; invariant `colInv`) | done |
| 348 | lemma | `Pr_G1col` | section PROOF. | `Pr_G1col` | done |

## `proof/smart_counter/Gext.eca`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Gext.lean`, namespace `GaudisCrypt.SHA3.Gext`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 9 | clone export | `Gcol` |  | `open Gcol` | def |
| 11 | op | `bad_ext` |  | `bad_ext` | def |
| 15 | op | `hinvc` |  | `hinvc` | def |
| 18 | module | `G2` |  | `G2.M`, `G2.S` (functors of `HS`), `G2` (`D` a Lean parameter) | def |
| 20 | module | `M` |  | `G2.M` | def |
| 48 | module | `S` |  | `G2.S` | def |
| 156 | clone include | `EagerCore` |  | `Eager`, `RRO`, `RRO.resample` | def |
| 160 | declare module | `D` | section . | `D` (section variable) | def |
| 162 | op | `inv_ext` | section . | `inv_ext` | def |
| 165 | op | `inv_ext1` | section . | `inv_ext1` | def |
| 168 | lemma | `rng_restr` | section . | `rng_restr` | done |
| 175 | equiv | `G1_G2` | section . | `G1_G2` (oracle steps `S_f_G12`, `S_fi_G12`, `M_f_G12`, wrappers `DPRestr_f_G12`, `DPRestr_fi_G12`, `DFRestr_f_G12`; invariant `g12Inv`) | done |
| 318 | declare module | `D` | section EXT. | `D` (section variable) | def |
| 320 | local module | `ReSample` | section EXT. | `ReSample` (variable: lens `ReSample_count`, E6) | def |
| 345 | local module | `Gext` | section EXT. | `Gext.resample`, `Gext.M`, `Gext.S` (modules), `Gext` (`D` a Lean parameter) | def |
| 351 | module | `M` | section EXT. | `Gext.M` | def |
| 379 | module | `S` | section EXT. | `Gext.S` | def |
| 492 | op | `inv_lt` | section EXT. | `inv_lt` | def |
| 497 | op | `inv_le` | section EXT. | `inv_le` | def |
| 502 | lemma | `fset0_eqP` | section EXT. | `fset0_eqP` | done |
| 508 | lemma | `size_set` | section EXT. | `size_set` | done |
| 518 | lemma | `size_set_le` | section EXT. | `size_set_le` | done |
| 521 | lemma | `size_rem` | section EXT. | `size_rem` | done |
| 529 | lemma | `size_rem_le` | section EXT. | `size_rem_le` | done |
| 532 | lemma | `size_ge0` | section EXT. | `size_ge0` | done |
| 535 | lemma | `size0` | section EXT. | `size0` | done |
| 538 | local equiv | `RROset_inv_lt` | section EXT. | `RROset_inv_lt` (hypothesis `GcolFresh ReSample_count`) | done (exc E6) |
| 546 | local lemma | `Pr_ext` | section EXT. | `Pr_ext` (`fel` as the supermartingale `Gext_potential`, steps `ReSample_f_potential`, `ReSample_f1_potential`) | done |
| 585 | local equiv | `EG2_Gext` | section EXT. | `EG2_Gext` (oracle steps `S_f_ext`, `S_fi_ext`, `M_f_ext`, wrappers `DPRestr_f_ext`, `DPRestr_fi_ext`, `DFRestr_f_ext`; invariant `extInv`) | done (exc E6) |
| 698 | declare axiom | `D_ll` | section EXT. | `D_ll` (hypothesis) | def |
| 702 | lemma | `Real_G2` | section EXT. | `Real_G2` (`ReSample.count` chosen fresh; `Eager_1_2` by `Eager.main2_eq_main1`, side conditions from `fvP_G2`) | done |

## `proof/smart_counter/Gconcl.ec`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Gconcl.lean`, namespace `GaudisCrypt.SHA3.Gconcl`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 9 | module | `IF` |  | `IF` (definition, `T.mk`) | def |
| 14 | module | `S` |  | `S` | def |
| 67 | declare module | `D` | section . | `D` (section variable) | def |
| 68 | local clone import | `Gext` | section . | `open Gext` | def |
| 71 | local module | `G3` | section . | `G3.M`, `G3.S` (functors of `RO`), `G3` (`D` a Lean parameter; `distinguish (_u : Unit)`, an `F.RO_Distinguisher`) | def |
| 73 | module | `M` | section . | `G3.M` | def |
| 104 | module | `S` | section . | `G3.S` | def |
| 206 | local equiv | `G2_G3` | section . | `G2_G3` (+ `Gext0Fresh D`; oracle steps `DFRestr_f_G23`, `DPRestr_f_G23`, `DPRestr_fi_G23`, invariant `colEq`; `sfGuard`) | exc |
| 253 | local module | `G4` | section . | `G4.C`, `G4.S` (functors of `RO`), `G4` (`D` a Lean parameter; `distinguish (_u : Unit)`, an `F.RO_Distinguisher`) | def |
| 255 | module | `C` | section . | `G4.C` | def |
| 270 | module | `S` | section . | `G4.S` | def |
| 326 | local equiv | `G3_G4` | section . | `G3_G4` (+ `Gext0Fresh D`; oracle steps `DFRestr_f_G34`, `DPRestr_f_G34`, `DPRestr_fi_G34`, invariant `g34Inv`) | exc |
| 350 | local equiv | `G4_Ideal` | section . | `G4_Ideal` (+ `Gext0Fresh D`; oracle steps `DFRestr_f_G4I`, `DPRestr_f_G4I`, `DPRestr_fi_G4I`, invariant `g4Inv`) | exc |
| 363 | declare axiom | `D_ll` | section . | `D_ll` (hypothesis) | def |
| 369 | lemma | `Real_Ideal` | section . | `Real_Ideal` (+ `Gext0Fresh D`; `fvP_G3`, `fvP_G4` for `RO_LRO_D`) | exc |

## `proof/BlockSponge.ec`

Lean: `GaudisCrypt/Examples/SHA3/BlockSponge.lean`, namespace `GaudisCrypt.SHA3.BlockSponge`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 9 | clone include | `Indifferentiability` |  | `PRIMITIVE` … `IdealIndif` (abbreviations) | def |
| 21 | clone import | `IRO` |  | `BIRO` (namespace) | def |
| 29 | op | `format` |  | `format` | def |
| 30 | op | `parse` |  | `parse` (field of `Params`) | def |
| 32 | axiom | `formatK` |  | `formatK` (field of `Params`) | def |
| 33 | axiom | `parseK` |  | `parseK` (field of `Params`) | def |
| 34 | axiom | `parse_nil` |  | `parse_nil` (field of `Params`) | def |
| 36 | lemma | `parse_injective` |  | `parse_injective` | done |
| 41 | lemma | `parse_valid` |  | `parse_valid` | done |
| 56 | module | `C` |  | `C` | def |
| 63 | module | `FC` |  | `FC` | def |
| 76 | module | `PC` |  | `PC` | def |
| 98 | module | `DRestr` |  | `DRestr` (`D` a Lean parameter) | def |
| 110 | module | `Last` |  | `Last` (with `Last.init` separate) | def |
| 119 | module | `` |  | `` | def |
| 123 | module | `` |  | `` | def |

## `proof/smart_counter/Gconcl_list.ec`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Gconcl_list.lean`, namespace `GaudisCrypt.SHA3.Gconcl_list`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 11 | op | `valid` |  | `valid` | def |
| 12 | axiom | `valid_spec` |  | `valid_spec` (field of `Params`) | def |
| 13 | axiom | `parse_gt0` |  | `parse_gt0` (field of `Params`) | def |
| 14 | axiom | `parse_not_valid` |  | `parse_not_valid` (field of `Params`) | def |
| 17 | axiom | `parse_twice` |  | `parse_twice` (field of `Params`) | def |
| 19 | axiom | `valid_uniq` |  | `valid_uniq` (field of `Params`) | def |
| 23 | clone export | `Handle` |  | `open Handle` | def |
| 25 | module | `DSqueeze` |  | `DSqueeze` | def |
| 46 | module | `Squeeze` |  | `Squeeze` (Lean function, `T.mk`), `Squeeze.init_` | def |
| 55 | module | `A` |  | `A` (`D` a Lean parameter; `P` is `SLCommon.DPRIMITIVE`, repackaged with `mk` for `D`) | def |
| 67 | module | `NIndif` |  | `NIndif` | def |
| 80 | module | `P` |  | `P` (abbreviation of `Perm`) | def |
| 82 | clone | `IRO` |  | `BIRO2` (namespace) | def |
| 88 | module | `Valid` |  | `Valid` | def |
| 102 | module | `SimLast` |  | `SimLast` (`S` a Lean parameter; aliases wrapped, E5) | def |
| 111 | clone | `F` |  | `F2` (namespace) | def |
| 116 | op | `(<=)` | section Ideal. | `«<=»` | def |
| 119 | local lemma | `leq_add_nin` | section Ideal. | `leq_add_nin` | done |
| 128 | local lemma | `leq_add_in` | section Ideal. | `leq_add_in` | done |
| 136 | local lemma | `leq_nin_dom` | section Ideal. | `leq_nin_dom` | done |
| 141 | local lemma | `prefix_leq1` | section Ideal. | `prefix_leq1` | done |
| 159 | local lemma | `prefix_le1` | section Ideal. | `prefix_le1` | done |
| 171 | local lemma | `leq_add2` | section Ideal. | `leq_add2` | done |
| 177 | local equiv | `ideal_equiv` | section Ideal. | `ideal_equiv` (oracle steps `FC_DSqueeze_DFRestr_f`, `PC_DPRestr_f`, `PC_DPRestr_fi`, `IF_f_ie`; invariant `ieInv`; no `splitwhile`: one loop invariant) | done |
| 296 | local module | `IF'` | section Ideal. | `IF'` (Lean function), `IF'.f_` | def |
| 315 | local module | `L` | section Ideal. | `L` (Lean function) | def |
| 319 | local module | `Valid2` | section Ideal. | `Valid2` (Lean function), `Valid2.f_` | def |
| 330 | local module | `L2` | section Ideal. | `L2` (Lean function) | def |
| 334 | local equiv | `Ideal_equiv_valid` | section Ideal. | `Ideal_equiv_valid` (oracle steps `IF'_Valid2_f`, generic `FC_f_sInv`, `S_f_sInv`, `S_fi_sInv`, `PC_f_sInv`, `PC_fi_sInv`; invariant `idInv`) | done |
| 365 | local equiv | `ideal_equiv2` | section Ideal. | `ideal_equiv2` (inner step `Valid2_IF_f`) | done |
| 388 | inductive | `inv_L_L3` | section Ideal. | `inv_L_L3` | def |
| 393 | local module | `IF2` | section Ideal. | `IF2` | def |
| 421 | local module | `L3` | section Ideal. | `L3` (Lean function) | def |
| 425 | local lemma | `lemma1` | section Ideal. | `lemma1` | done |
| 440 | local lemma | `lemma2` | section Ideal. | `lemma2` | done |
| 452 | local lemma | `incl_dom` | section Ideal. | `incl_dom` | done |
| 461 | local lemma | `lemma3` | section Ideal. | `lemma3` | done |
| 476 | local equiv | `Ideal_equiv3` | section Ideal. | `Ideal_equiv3` (inner step `IF'_IF2_f`; invariant `L3Inv`; `inv_L_L3.dom_valid` … `set_valid`) | done |
| 599 | local module | `D2` | section Ideal. | `D2` (Lean function) | def |
| 603 | local module | `D3` | section Ideal. | `D3` (Lean function) | def |
| 608 | module | `DSqueeze2` | section Ideal. | `DSqueeze2` | def |
| 647 | local module | `FValid` | section Ideal. | `FValid` | def |
| 657 | local module | `DValid` | section Ideal. | `DValid` (`D` a Lean parameter; E5) | def |
| 659 | local module | `S2` | section Ideal. | `S2` (call wrapper, E5) | def |
| 661 | local module | `L4` | section Ideal. | `L4` (Lean function) | def |
| 665 | local equiv | `equiv_L3_L4` | section Ideal. | `equiv_L3_L4` | stated |
| 788 | op | `inv_map` | section Ideal. | `inv_map` | def |
| 794 | inductive | `INV_L4_ideal` | section Ideal. | `INV_L4_ideal` | def |
| 801 | local lemma | `lemma5` | section Ideal. | `lemma5` | done |
| 819 | local lemma | `lemma5bis` | section Ideal. | `lemma5bis` | done |
| 843 | local equiv | `equiv_L4_ideal` | section Ideal. | `equiv_L4_ideal` (oracle steps `FC_FValid_f`, `PC_f_sInv S2_SimLast_f`, `PC_fi_sInv S2_SimLast_fi`; inner step `DSqueeze2_Valid_f` via `Last_f_L4`; invariant `L4Inv`) | done |
| 916 | local module | `D5` | section Ideal. | `D5` (Lean function) | def |
| 919 | local module | `D6` | section Ideal. | `D6` (Lean function) | def |
| 922 | lemma | `equiv_ideal` | section Ideal. | `equiv_ideal` | stated |
| 973 | inductive | `m_p` | section Real. | `m_p` | def |
| 979 | inductive | `INV_Real` | section Real. | `INV_Real` | def |
| 987 | local lemma | `INV_Real_incr` | section Real. | `INV_Real_incr` | done |
| 992 | local lemma | `INV_Real_addm_mi` | section Real. | `INV_Real_addm_mi` | done |
| 1004 | local lemma | `invmC'` | section Real. | `invmC'` | done |
| 1008 | local lemma | `invmC` | section Real. | `invmC` | done |
| 1012 | local lemma | `invm_dom_rng` | section Real. | `invm_dom_rng` | done |
| 1021 | local lemma | `all_prefixes_of_INV_real` | section Real. | `all_prefixes_of_INV_real` | done |
| 1029 | local lemma | `lemma2'` | section Real. | `lemma2'` | done |
| 1075 | local lemma | `take_nseq` | section Real. | `take_nseq` | done |
| 1086 | local lemma | `take_format` | section Real. | `take_format` | done |
| 1100 | local lemma | `equiv_sponge` | section Real. | `equiv_sponge` | stated |
| 1437 | local lemma | `lemma4` | section Real. | `lemma4` | done |
| 1463 | local lemma | `lemma_3` | section Real. | `lemma_3` | done |
| 1493 | local lemma | `squeeze_squeezeless` | section Real. | `squeeze_squeezeless` | stated |
| 1748 | lemma | `pr_real` | section Real. | `pr_real` | stated |
| 1763 | declare module | `D` | section Real_Ideal. | `D` (section variable) | def |
| 1765 | declare axiom | `D_lossless` | section Real_Ideal. | `D_lossless` (abbreviation; hypothesis) | def |
| 1770 | lemma | `A_lossless` | section Real_Ideal. | `A_lossless` | stated |
| 1786 | lemma | `concl` | section Real_Ideal. | `concl` | stated |
| 1809 | declare module | `D` | section Real_Ideal_Abs. | `D` (section variable) | def |
| 1811 | declare axiom | `D_lossless` | section Real_Ideal_Abs. | `D_lossless` (abbreviation; hypothesis) | def |
| 1816 | local module | `Neg_D` | section Real_Ideal_Abs. | `Real_Ideal_Abs.Neg_D` | def |
| 1825 | local lemma | `Neg_D_lossless` | section Real_Ideal_Abs. | `Real_Ideal_Abs.Neg_D_lossless` | stated |
| 1833 | local lemma | `useful` | section Real_Ideal_Abs. | `Real_Ideal_Abs.useful` | done |
| 1853 | local lemma | `invmC` | section Real_Ideal_Abs. | `Real_Ideal_Abs.invmC` | done |
| 1858 | local lemma | `Real_lossless` | section Real_Ideal_Abs. | `Real_Ideal_Abs.Real_lossless` | stated |
| 1887 | local lemma | `Ideal_lossless` | section Real_Ideal_Abs. | `Real_Ideal_Abs.Ideal_lossless` | stated |
| 1905 | local lemma | `neg_D_concl` | section Real_Ideal_Abs. | `Real_Ideal_Abs.neg_D_concl` | stated |
| 1924 | lemma | `Inefficient_Real_Ideal` | section Real_Ideal_Abs. | `Inefficient_Real_Ideal` | stated |
| 1946 | module | `Simulator` |  | `Simulator` | def |
| 2010 | declare module | `D` | section Simplify_Simulator. | `D` (section variable) | def |
| 2012 | declare axiom | `D_lossless` | section Simplify_Simulator. | `D_lossless` (abbreviation; hypothesis) | def |
| 2016 | local clone import | `PROM.FullRO` | section Simplify_Simulator. | `Simplify_Simulator.IRO2` (variable: lens `IRO2_RO_m`, E6) | def |
| 2024 | local module | `Simu` | section Simplify_Simulator. | `Simplify_Simulator.Simu` (`FRO` a Lean parameter) | def |
| 2081 | local module | `L` | section Simplify_Simulator. | `Simplify_Simulator.L` (Lean function) | def |
| 2085 | local lemma | `equal1` | section Simplify_Simulator. | `Simplify_Simulator.equal1` | stated |
| 2158 | local lemma | `equal2` | section Simplify_Simulator. | `Simplify_Simulator.equal2` | stated |
| 2186 | lemma | `Simplify_simulator` | section Simplify_Simulator. | `Simplify_simulator` | stated |
| 2202 | declare module | `D` | section Real_Ideal. | `D` (section variable) | def |
| 2204 | declare axiom | `D_lossless` | section Real_Ideal. | `D_lossless` (abbreviation; hypothesis) | def |
| 2209 | lemma | `Real_Ideal` | section Real_Ideal. | `Real_Ideal` | stated |

## `proof/Sponge.ec`

Lean: `GaudisCrypt/Examples/SHA3/Sponge.lean`, namespace `GaudisCrypt.SHA3.Sponge`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 10 | clone include | `Indifferentiability` |  | `PRIMITIVE` … `IdealIndif` (abbreviations) | def |
| 22 | clone import | `IRO` |  | `BIRO` (namespace) | def |
| 30 | module | `StdSponge` |  | `StdSponge` | def |
| 58 | module | `Sponge` |  | `Sponge` | def |
| 85 | lemma | `loop_cond` |  | `loop_cond` | done |
| 99 | equiv | `Sponge_is_StdSponge` |  | `Sponge_is_StdSponge` | done |
| 131 | module | `LowerFun` |  | `LowerFun` | def |
| 146 | module | `RaiseFun` |  | `RaiseFun` | def |
| 155 | module | `LowerDist` |  | `LowerDist` (call-wrapped alias, E5) | def |
| 158 | module | `RaiseSim` |  | `RaiseSim` (`Module.comp`) | def |
| 258 | module type | `HYBRID_IRO` |  | `HybridIRO.HYBRID_IRO` | def |
| 268 | module type | `HYBRID_IRO_DIST` |  | `HybridIRO.HYBRID_IRO_DIST` (with `.holes`, `.ext`) | def |
| 274 | module | `HybridIROExper` |  | `HybridIRO.HybridIROExper` | def |
| 285 | module | `HybridIROLazy` |  | `HybridIRO.HybridIROLazy` (`.asHI` its `HYBRID_IRO` view) | def |
| 320 | module | `HybridIROEager` |  | `HybridIRO.HybridIROEager` (`.asHI` its `HYBRID_IRO` view) | def |
| 369 | declare module | `D` | section . | `D` (parameter of the section's lemmas, with `DRestrictions`) | def |
| 371 | local clone import | `PROM.FullRO` | section . | `HybridIRO.ERO` (namespace; variables are lens parameters, E6) | def |
| 378 | local module | `EROExper` | section . | `HybridIRO.EROExper` | def |
| 387 | local lemma | `LRO_RO` | section . | `HybridIRO.LRO_RO` | done (exc E8) |
| 398 | local module | `HIRO` | section . | `HybridIRO.HIRO` | def |
| 424 | local lemma | `HybridIROLazy_HIRO_LRO_init` | section . | `HybridIRO.HybridIROLazy_HIRO_LRO_init` | done |
| 429 | local lemma | `HybridIROLazy_fill_in_LRO_get` | section . | `HybridIRO.HybridIROLazy_fill_in_LRO_get` | done |
| 442 | local lemma | `HybridIROLazy_HIRO_LRO_f` | section . | `HybridIRO.HybridIROLazy_HIRO_LRO_f` | done |
| 456 | local lemma | `HIRO_RO_HybridIROEager_init` | section . | `HybridIRO.HIRO_RO_HybridIROEager_init` | done |
| 461 | local lemma | `RO_get_HybridIROEager_fill_in` | section . | `HybridIRO.RO_get_HybridIROEager_fill_in` | done |
| 474 | local lemma | `RO_sample_HybridIROEager_fill_in` | section . | `HybridIRO.RO_sample_HybridIROEager_fill_in` | done |
| 487 | local lemma | `HIRO_RO_HybridIROEager_f` | section . | `HybridIRO.HIRO_RO_HybridIROEager_f` | done |
| 503 | local module | `RODist` | section . | `HybridIRO.RODist` | def |
| 511 | local lemma | `Exper_HybridIROLazy_LRO` | section . | `HybridIRO.Exper_HybridIROLazy_LRO` | done (exc E8) |
| 522 | local lemma | `Exper_RO_HybridIROEager` | section . | `HybridIRO.Exper_RO_HybridIROEager` | done (exc E8) |
| 533 | lemma | `HybridIROExper_Lazy_Eager'` | section . | `HybridIRO.HybridIROExper_Lazy_Eager'` | done (exc E6) |
| 544 | lemma | `HybridIROExper_Lazy_Eager` |  | `HybridIRO.HybridIROExper_Lazy_Eager` | done (exc E6) |
| 553 | module | `RaiseHybridIRO` |  | `HybridIRO.RaiseHybridIRO` | def |
| 568 | module | `LowerHybridIRO` |  | `HybridIRO.LowerHybridIRO` | def |
| 579 | pred | `lazy_invar` |  | `HybridIRO.lazy_invar` | def |
| 590 | lemma | `lazy_invar0` |  | `HybridIRO.lazy_invar0` | done |
| 597 | lemma | `lazy_invar_mem_pad2blocks_l2r` |  | `HybridIRO.lazy_invar_mem_pad2blocks_l2r` | done |
| 605 | lemma | `lazy_invar_mem_pad2blocks_r2l` |  | `HybridIRO.lazy_invar_mem_pad2blocks_r2l` | done |
| 613 | lemma | `lazy_invar_vb` |  | `HybridIRO.lazy_invar_vb` | done |
| 621 | lemma | `lazy_invar_lookup_eq` |  | `HybridIRO.lazy_invar_lookup_eq` | done |
| 629 | lemma | `lazy_invar_upd_mem_dom_iff` |  | `HybridIRO.lazy_invar_upd_mem_dom_iff` | done |
| 648 | lemma | `lazy_invar_upd2_vb` |  | `HybridIRO.lazy_invar_upd2_vb` | done |
| 662 | lemma | `lazy_invar_upd_lu_eq` |  | `HybridIRO.lazy_invar_upd_lu_eq` | done |
| 685 | lemma | `LowerFun_IRO_HybridIROLazy_f` |  | `HybridIRO.LowerFun_IRO_HybridIROLazy_f` | done |
| 729 | lemma | `IRO_RaiseHybridIRO_HybridIROLazy_f` |  | `HybridIRO.IRO_RaiseHybridIRO_HybridIROLazy_f` | done |
| 765 | pred | `eager_invar` |  | `HybridIRO.eager_invar` | def |
| 777 | pred | `block_bits_all_in_dom` |  | `HybridIRO.block_bits_all_in_dom` | def |
| 781 | pred | `block_bits_all_out_dom` |  | `HybridIRO.block_bits_all_out_dom` | def |
| 785 | pred | `block_bits_dom_all_in_or_out` |  | `HybridIRO.block_bits_dom_all_in_or_out` | def |
| 789 | lemma | `eager_inv_mem_mp1_ge0` |  | `HybridIRO.eager_inv_mem_mp1_ge0` | done |
| 796 | lemma | `eager_inv_mem_mp2_ge0` |  | `HybridIRO.eager_inv_mem_mp2_ge0` | done |
| 808 | lemma | `eager_invar0` |  | `HybridIRO.eager_invar0` | done |
| 811 | lemma | `eager_inv_imp_block_bits_dom` |  | `HybridIRO.eager_inv_imp_block_bits_dom` | done |
| 835 | lemma | `eager_inv_mem_dom1` |  | `HybridIRO.eager_inv_mem_dom1` | done |
| 848 | lemma | `eager_inv_not_mem_dom1` |  | `HybridIRO.eager_inv_not_mem_dom1` | done |
| 865 | lemma | `block_bits_dom_first_in_imp_all_in` |  | `HybridIRO.block_bits_dom_first_in_imp_all_in` | done |
| 871 | lemma | `block_bits_dom_first_out_imp_all_out` |  | `HybridIRO.block_bits_dom_first_out_imp_all_out` | done |
| 877 | lemma | `Lower_HybridIROEager_f` |  | `HybridIRO.Lower_HybridIROEager_f` | done |
| 904 | module | `HybridIROEagerTrans` |  | `HybridIRO.HybridIROEagerTrans` | def |
| 962 | pred | `eager_eq_except` |  | `HybridIRO.eager_eq_except` | def |
| 968 | lemma | `eager_eq_except_mem_iff` |  | `HybridIRO.eager_eq_except_mem_iff` | done |
| 976 | lemma | `eager_eq_except_upd1_eq_in` |  | `HybridIRO.eager_eq_except_upd1_eq_in` | done |
| 987 | lemma | `eager_eq_except_upd2_eq_in` |  | `HybridIRO.eager_eq_except_upd2_eq_in` | done |
| 998 | lemma | `eager_eq_except_maps_eq` |  | `HybridIRO.eager_eq_except_maps_eq` | done |
| 1012 | lemma | `eager_invar_eq_except_upd1` |  | `HybridIRO.eager_invar_eq_except_upd1` | done |
| 1079 | lemma | `HybridIROEagerTrans_next_block_split` |  | `HybridIRO.HybridIROEagerTrans_next_block_split` | done |
| 1188 | module | `BlockSpongeTrans` |  | `HybridIRO.BlockSpongeTrans` | def |
| 1215 | clone | `Program` |  | `HybridIRO.Prog` (namespace) | def |
| 1221 | lemma | `PrLoopSnoc_sample` |  | `HybridIRO.PrLoopSnoc_sample` | done |
| 1235 | lemma | `iter_mul_one_half_pos` |  | `HybridIRO.iter_mul_one_half_pos` | done |
| 1250 | module | `BlockGen` |  | `HybridIRO.BlockGen` | def |
| 1269 | lemma | `BlockGen_loop_direct` |  | `HybridIRO.BlockGen_loop_direct` | done |
| 1307 | lemma | `HybridIROEagerTrans_BlockSpongeTrans_next_block` |  | `HybridIRO.HybridIROEagerTrans_BlockSpongeTrans_next_block` | done |
| 1507 | lemma | `HybridIROEagerTrans_BlockSpongeTrans_loop` |  | `HybridIRO.HybridIROEagerTrans_BlockSpongeTrans_loop` | done |
| 1614 | lemma | `HybridIROEager_f_BlockIRO_f` |  | `HybridIRO.HybridIROEager_f_BlockIRO_f` | done |
| 1873 | lemma | `HybridIROEager_BlockIRO_f` |  | `HybridIRO.HybridIROEager_BlockIRO_f` | done |
| 1915 | declare module | `BlockSim` | section . | `BlockSim` (parameter, with `hS`, `Restrictions`) | def |
| 1916 | declare module | `Dist` | section . | `Dist` (parameter, with `hD`, `Restrictions`) | def |
| 1918 | local clone | `HybridIRO` | section . | `HybridIRO` at lens parameters `HIRO_Lazy_mp`, `HIRO_Eager_mp` (`HIRO_fresh`, E6) | def |
| 1922 | local lemma | `Sponge_Raise_BlockSponge_f` | section . | `Sponge_Raise_BlockSponge_f` | done |
| 1953 | local lemma | `RealIndif_Sponge_BlockSponge` | section . | `RealIndif_Sponge_BlockSponge` | done |
| 1970 | local lemma | `Ideal_IRO_Experiment_HybridLazy` | section . | `Ideal_IRO_Experiment_HybridLazy` | done |
| 2008 | local module | `HybridIRODist` | section . | `HybridIRODist` (EC-like by `HybridIRODist.ecModule`) | def |
| 2021 | local lemma | `Experiment_HybridIROExper_Lazy` | section . | `Experiment_HybridIROExper_Lazy` | done |
| 2036 | local lemma | `HybridIROExper_Experiment_Eager` | section . | `HybridIROExper_Experiment_Eager` | done |
| 2053 | local lemma | `Experiment_Hybrid_Lazy_Eager` | section . | `Experiment_Hybrid_Lazy_Eager` | done |
| 2070 | local lemma | `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` | section . | `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` (from `…_inv`, its proof, without `={glob BlockSim}`) | done |
| 2094 | local lemma | `Experiment_HybridEager_Ideal_BlockIRO` | section . | `Experiment_HybridEager_Ideal_BlockIRO` | done |
| 2128 | local lemma | `IdealIndif_IRO_BlockIRO` | section . | `IdealIndif_IRO_BlockIRO` | done |
| 2138 | lemma | `conclu` | section . | `conclu` | done |
| 2153 | lemma | `conclusion` |  | `conclusion` | done |

## `proof/SHA3Indiff.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3Indiff.lean`, namespace `GaudisCrypt.SHA3.SHA3Indiff`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 12 | op | `limit` |  | `limit` | def |
| 17 | type | `state` |  | `state` | def |
| 18 | op | `parse` |  | `parse` | def |
| 19 | op | `valid` |  | `valid` | def |
| 22 | module | `Simulator` |  | `Simulator` | def |
| 88 | module | `Cntr` |  | `Cntr` | def |
| 96 | module | `FC` |  | `FC` | def |
| 116 | module | `PC` |  | `PC` | def |
| 137 | module | `DRestr` |  | `DRestr` (`D` a Lean parameter) | def |
| 148 | declare module | `Dist` | section . | `Dist` (parameter, with `hD`, `DistRestrictions`) | def |
| 151 | declare axiom | `Dist_lossless` | section . | `Dist_lossless` (hypothesis of `security`) | def |
| 155 | lemma | `drestr_commute1` | section . | `drestr_commute1` | stated |
| 185 | lemma | `drestr_commute2` | section . | `drestr_commute2` | stated |
| 223 | op | `wit_pair` | section . | `wit_pair` | def |
| 225 | local equiv | `equiv_sim_f` | section . | `equiv_sim_f` | stated |
| 245 | local equiv | `equiv_sim_fi` | section . | `equiv_sim_fi` | stated |
| 255 | local lemma | `replace_simulator` | section . | `replace_simulator` | stated |
| 270 | lemma | `security` | section . | `security` | stated |
| 309 | lemma | `SHA3Indiff` |  | `SHA3Indiff` | stated |

## `proof/SHA3_OIndiff.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3_OIndiff.lean`, namespace `GaudisCrypt.SHA3.SHA3_OIndiff`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 16 | clone import | `OptionIndifferentiability` |  | `OIndif` (namespace of abbreviations, opened) | def |
| 23 | module | `FSome` |  | `FSome` (`init` call-wrapped, E5) | def |
| 32 | module | `PSome` |  | `PSome` (Lean function; `PSome.own`) | def |
| 46 | module | `Poget` |  | `Poget` | def |
| 59 | module | `CSome` |  | `CSome` (`Module.comp`) | def |
| 61 | module | `OSimulator` |  | `OSimulator` | def |
| 115 | module | `Counter` |  | `Counter` | def |
| 122 | op | `increase_counter` |  | `increase_counter` | def |
| 126 | module | `OFC` |  | `OFC` | def |
| 140 | module | `OPC` |  | `OPC` | def |
| 161 | module | `ODRestr` |  | `ODRestr` (`D` a Lean parameter) | def |
| 171 | declare module | `Dist` | section . | unused (`SHA3OIndiff` quantifies its own `Dist`) | def |
| 175 | local module | `DFSome` | section . | `DFSome` | def |
| 183 | module | `DPSome` | section . | `DPSome` | def |
| 196 | local module | `OD` | section . | `OD` (`D` a Lean parameter) | def |
| 205 | lemma | `SHA3OIndiff` | section . | `SHA3OIndiff` | stated |

## `proof/SecureHash.eca`

Lean: `GaudisCrypt/Examples/SHA3/SecureHash.lean`, namespace `GaudisCrypt.SHA3.SecureHash`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 4 | type | `from` |  | `«from»`, `«to»`, `block` (section variables) | def |
| 7 | clone import | `OptionIndifferentiability` |  | `OptionIndifferentiability` at `block «from» «to»` | def |
| 14 | op | `sampleto` |  | `sampleto` (section variable) | def |
| 16 | op | `bound` |  | `bound` (section variable) | def |
| 17 | axiom | `bound_ge0` |  | `Axioms.bound_ge0` | def |
| 19 | axiom | `sampleto_ll` |  | `Axioms.sampleto_ll` | def |
| 20 | axiom | `sampleto_full` |  | `Axioms.sampleto_full` | def |
| 21 | axiom | `sampleto_fu` |  | `Axioms.sampleto_fu` | def |
| 29 | op | `increase_counter` |  | `increase_counter` (section variable) | def |
| 30 | axiom | `increase_counter_spec` |  | `Axioms.increase_counter_spec` | def |
| 49 | module | `Bounder` |  | `Bounder` (variable: lens parameter `Bounder_bounder`) | def |
| 56 | module | `FBounder` |  | `FBounder` | def |
| 72 | module | `PBounder` |  | `PBounder` | def |
| 95 | module type | `AdvPreimage` |  | `AdvPreimage` | def |
| 99 | module | `Preimage` |  | `Preimage` | def |
| 113 | module type | `AdvSecondPreimage` |  | `AdvSecondPreimage` | def |
| 117 | module | `SecondPreimage` |  | `SecondPreimage` | def |
| 131 | module type | `AdvCollision` |  | `AdvCollision` | def |
| 135 | module | `Collision` |  | `Collision` | def |

## `proof/SecureRO.eca`

Lean: `GaudisCrypt/Examples/SHA3/SecureRO.lean`, namespace `GaudisCrypt.SHA3.SecureRO`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 7 | type | `from` |  | `«from»`, `«to»` (section variables) | def |
| 9 | op | `sampleto` |  | `sampleto` (section variable) | def |
| 11 | op | `bound` |  | `bound` (section variable) | def |
| 12 | axiom | `bound_gt0` |  | `Axioms.bound_gt0` | def |
| 14 | axiom | `sampleto_ll` |  | `Axioms.sampleto_ll` | def |
| 15 | axiom | `sampleto_full` |  | `Axioms.sampleto_full` | def |
| 16 | axiom | `sampleto_fu` |  | `Axioms.sampleto_fu` | def |
| 18 | clone import | `PROM.FullRO` |  | `PROM.FullRO` at lens parameters `RO_m`, `FRO_m` (`RO.RO_T`, `RO.RO`, `RO.LRO`) | def |
| 26 | op | `increase_counter` |  | `increase_counter` (section variable) | def |
| 27 | axiom | `increase_counter_spec` |  | `Axioms.increase_counter_spec` | def |
| 29 | op | `bound_counter` |  | `bound_counter` (section variable) | def |
| 30 | axiom | `bound_counter_ge0` |  | `Axioms.bound_counter_ge0` | def |
| 32 | module | `Counter` |  | `Counter` (variable: lens parameter `Counter_c`) | def |
| 39 | module type | `RF` |  | `RF` | def |
| 44 | module | `Bounder` |  | `Bounder` (variable: lens parameter `Bounder_bounder`) | def |
| 65 | module type | `Oracle` |  | `Oracle` (with `Oracle.holes`, `Oracle.ext`) | def |
| 69 | module type | `AdvPreimage` |  | `AdvPreimage` | def |
| 73 | module | `Preimage` |  | `Preimage` | def |
| 89 | declare module | `A` | section Preimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 91 | local module | `FEL` | section Preimage. | `Preimage.FEL` | def |
| 100 | local module | `Preimage2` | section Preimage. | `Preimage.Preimage2` | def |
| 112 | lemma | `RO_is_preimage_resistant` | section Preimage. | `RO_is_preimage_resistant` | done (exc E8) |
| 189 | module type | `AdvSecondPreimage` |  | `AdvSecondPreimage` | def |
| 193 | module | `SecondPreimage` |  | `SecondPreimage` | def |
| 215 | declare module | `A` | section SecondPreimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 217 | local module | `FEL` | section SecondPreimage. | `SecondPreimage.FEL` | def |
| 227 | local module | `SecondPreimage2` | section SecondPreimage. | `SecondPreimage.SecondPreimage2` (variable: lens parameter `SecondPreimage2_m2`, E6) | def |
| 246 | local module | `D1` | section SecondPreimage. | `SecondPreimage.D1` (variable: lens parameter `D1_m1`, E6; `A` a Lean parameter, so that `D1 A` is an `RO_Distinguisher`) | def |
| 255 | local module | `SecondPreimage3` | section SecondPreimage. | `SecondPreimage.SecondPreimage3` (`A` a Lean parameter, as in `D1`) | def |
| 267 | lemma | `RO_is_second_preimage_resistant` | section SecondPreimage. | `RO_is_second_preimage_resistant` | done (exc E6, E8) |
| 370 | module type | `AdvCollision` |  | `AdvCollision` | def |
| 374 | module | `Collision` |  | `Collision` | def |
| 395 | declare module | `A` | section Collision. | `A` (parameter, with `hA`, `_hAd`) | def |
| 397 | local module | `FEL` | section Collision. | `Collision.FEL` | def |
| 406 | local module | `Collision2` | section Collision. | `Collision.Collision2` | def |
| 424 | op | `collision` | section Collision. | `collision` | def |
| 427 | lemma | `RO_is_collision_resistant` | section Collision. | `RO_is_collision_resistant` | done (exc E8) |

## `proof/SecureORO.eca`

Lean: `GaudisCrypt/Examples/SHA3/SecureORO.lean`, namespace `GaudisCrypt.SHA3.SecureORO`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 7 | type | `from` |  | `«from»`, `«to»` (section variables) | def |
| 9 | op | `sampleto` |  | `sampleto` (section variable) | def |
| 11 | op | `bound` |  | `bound` (section variable) | def |
| 12 | axiom | `bound_ge0` |  | `Axioms.bound_ge0` | def |
| 14 | axiom | `sampleto_ll` |  | `Axioms.sampleto_ll` | def |
| 15 | axiom | `sampleto_full` |  | `Axioms.sampleto_full` | def |
| 16 | axiom | `sampleto_fu` |  | `Axioms.sampleto_fu` | def |
| 18 | clone import | `PROM.FullRO` |  | `PROM.FullRO` at lens parameters `RO_m`, `FRO_m` (`RO.RO_T`, `RO.RO`, `RO.LRO`) | def |
| 26 | op | `increase_counter` |  | `increase_counter` (section variable) | def |
| 27 | axiom | `increase_counter_spec` |  | `Axioms.increase_counter_spec` | def |
| 29 | module type | `RF` |  | `RF_T` (E3) | def |
| 35 | module | `RF` |  | `RF` (aliases call-wrapped, E5) | def |
| 45 | module | `Bounder` |  | `Bounder` (`sample` call-wrapped, E5; variable: lens `Bounder_bounder`) | def |
| 63 | module type | `Oracle` |  | `Oracle` (with `Oracle.holes`, `Oracle.ext`) | def |
| 67 | module type | `AdvPreimage` |  | `AdvPreimage` | def |
| 71 | module | `Preimage` |  | `Preimage` | def |
| 84 | declare module | `A` | section Preimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 86 | local module | `FEL` | section Preimage. | `Preimage.FEL` | def |
| 95 | local module | `Preimage2` | section Preimage. | `Preimage.Preimage2` (variable: lens `Preimage2_hash`, E6) | def |
| 106 | lemma | `RO_is_preimage_resistant` | section Preimage. | `RO_is_preimage_resistant` | done (exc E6, E8) |
| 185 | module type | `AdvSecondPreimage` |  | `AdvSecondPreimage` | def |
| 189 | module | `SecondPreimage` |  | `SecondPreimage` | def |
| 203 | declare module | `A` | section SecondPreimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 205 | local module | `FEL` | section SecondPreimage. | `SecondPreimage.FEL` | def |
| 215 | local module | `SecondPreimage2` | section SecondPreimage. | `SecondPreimage.SecondPreimage2` (variable: lens `SecondPreimage2_m2`, E6) | def |
| 226 | local module | `D1` | section SecondPreimage. | `SecondPreimage.D1` (variable: lens `D1_m1`, E6; `A` a Lean parameter, so that `D1 A` is an `RO_Distinguisher`) | def |
| 235 | local module | `SecondPreimage3` | section SecondPreimage. | `SecondPreimage.SecondPreimage3` (`A` a Lean parameter, as in `D1`) | def |
| 247 | lemma | `RO_is_second_preimage_resistant` | section SecondPreimage. | `RO_is_second_preimage_resistant` | done (exc E6, E8) |
| 349 | module type | `AdvCollision` |  | `AdvCollision` | def |
| 353 | module | `Collision` |  | `Collision` | def |
| 366 | declare module | `A` | section Collision. | `A` (parameter, with `hA`, `_hAd`) | def |
| 368 | local module | `FEL` | section Collision. | `Collision.FEL` | def |
| 377 | local module | `Collision2` | section Collision. | `Collision.Collision2` | def |
| 387 | op | `collision` | section Collision. | `collision` | def |
| 390 | lemma | `RO_is_collision_resistant` | section Collision. | `RO_is_collision_resistant` | done (exc E8) |

## `proof/IndifRO_is_secure.ec`

Lean: `GaudisCrypt/Examples/SHA3/IndifRO_is_secure.lean`, namespace `GaudisCrypt.SHA3.IndifRO_is_secure`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 5 | type | `block` |  | `block` (section variable) | def |
| 6 | type | `f_in` |  | `f_in` (section variable) | def |
| 7 | type | `f_out` |  | `f_out` (section variable) | def |
| 9 | op | `sampleto` |  | `sampleto` (section variable) | def |
| 10 | axiom | `sampleto_ll` |  | `Axioms.sampleto_ll` | def |
| 11 | axiom | `sampleto_fu` |  | `Axioms.sampleto_fu` | def |
| 12 | axiom | `sampleto_full` |  | `Axioms.sampleto_full` | def |
| 14 | op | `limit` |  | `limit` (section variable) | def |
| 15 | axiom | `limit_gt0` |  | `Axioms.limit_gt0` | def |
| 17 | op | `bound` |  | `bound` (section variable) | def |
| 20 | op | `bound_counter` |  | `bound_counter` (section variable) | def |
| 21 | axiom | `bound_counter_ge0` |  | `Axioms.bound_counter_ge0` | def |
| 23 | op | `increase_counter` |  | `increase_counter` (section variable) | def |
| 24 | axiom | `increase_counter_spec` |  | `Axioms.increase_counter_spec` | def |
| 27 | clone import | `SecureRO` |  | `SRO` (namespace of abbreviations; variables are lens parameters `SRO_RO_m` …) | def |
| 40 | clone import | `Indifferentiability` |  | `Indifferentiability` at `block f_in f_out` (opened) | def |
| 45 | module | `RO` |  | `RO` (Lean definition of the aliases) | def |
| 50 | module | `FInit` |  | `FInit` (untyped; aliases call-wrapped, E5; `.asRF`, `.asRO`) | def |
| 59 | module | `GetF` |  | `GetF` (aliases call-wrapped, E5) | def |
| 64 | module | `SInit` |  | `SInit` (aliases call-wrapped, E5) | def |
| 75 | module | `FM` |  | `FM` (untyped; aliases call-wrapped, E5; `.asRF`, `.asRO`) | def |
| 88 | module | `DColl` |  | `DColl` (`A` a Lean parameter; alias call-wrapped, E5) | def |
| 94 | declare module | `A` | section Collision. | `A` (parameter, with `hA`, `_hAd`) | def |
| 96 | declare axiom | `D_ll` | section Collision. | `D_ll` (hypothesis `_D_ll`) | def |
| 99 | lemma | `coll_resistant_if_indifferentiable` | section Collision. | `coll_resistant_if_indifferentiable` (its two `have`s: `Collision_FM_GReal`, `GIdeal_Collision_RO`, both done) | done (exc E7, E8) |
| 128 | module | `DPre` |  | `DPre` (`A` a Lean parameter; variable: lens `DPre_h`) | def |
| 139 | declare module | `A` | section Preimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 141 | declare axiom | `D_ll` | section Preimage. | `D_ll` (hypothesis `_D_ll`) | def |
| 144 | lemma | `preimage_resistant_if_indifferentiable` | section Preimage. | `preimage_resistant_if_indifferentiable` | done (exc E7, E8) |
| 174 | module | `D2Pre` |  | `D2Pre` (`A` a Lean parameter; variable: lens `D2Pre_m2`) | def |
| 185 | declare module | `A` | section SecondPreimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 187 | declare axiom | `D_ll` | section SecondPreimage. | `D_ll` (hypothesis `_D_ll`) | def |
| 190 | lemma | `second_preimage_resistant_if_indifferentiable` | section SecondPreimage. | `second_preimage_resistant_if_indifferentiable` | done (exc E6, E7, E8) |

## `proof/SHA3Security.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3Security.lean`, namespace `GaudisCrypt.SHA3.SHA3Security`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 8 | module | `SHA3` |  | `SHA3` | def |
| 17 | op | `size_out` |  | `size_out` (field of `Params`) | def |
| 18 | axiom | `size_out_gt0` |  | `Params.size_out_gt0` | def |
| 20 | op | `sigma` |  | `sigma` (field of `Params`) | def |
| 21 | axiom | `sigma_gt0` |  | `Params.sigma_gt0` | def |
| 23 | type | `f_out` |  | `f_out` (field of `Params`) | def |
| 25 | op | `dout` |  | `dout` (field of `Params`) | def |
| 26 | axiom | `dout_ll` |  | `Params.dout_ll` | def |
| 27 | axiom | `dout_fu` |  | `Params.dout_fu` | def |
| 28 | axiom | `dout_full` |  | `Params.dout_full` | def |
| 31 | op | `to_list` |  | `to_list` (field of `Params`) | def |
| 32 | op | `of_list` |  | `of_list` (field of `Params`) | def |
| 33 | axiom | `spec_dout` |  | `Params.spec_dout` | def |
| 34 | axiom | `spec2_dout` |  | `Params.spec2_dout` | def |
| 35 | axiom | `to_list_inj` |  | `Params.to_list_inj` | def |
| 36 | axiom | `to_listK` |  | `Params.to_listK` | def |
| 38 | axiom | `dout_equal_dlist` |  | `Params.dout_equal_dlist` | def |
| 40 | lemma | `doutE1` |  | `doutE1` | done |
| 62 | module | `CSetSize` |  | `CSetSize` (alias call-wrapped, E5) | def |
| 71 | module | `FSetSize` |  | `FSetSize` (alias call-wrapped, E5) | def |
| 80 | clone import | `IndifRO_is_secure` |  | `S` (namespace of abbreviations and `global_var`s, opened; `realize`s: `S.axioms`) | def |
| 103 | module | `FGetSize` |  | `FGetSize` | def |
| 111 | module | `SimSetSize` |  | `SimSetSize` (`Module.comp`) | def |
| 113 | module | `DFSetSize` |  | `DFSetSize` | def |
| 121 | module | `DSetSize` |  | `DSetSize` (alias call-wrapped, E5) | def |
| 127 | declare module | `A` | section Preimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 129 | declare axiom | `A_ll` | section Preimage. | `A_ll` (hypothesis `_A_ll`, `IndifRO_is_secure.D_ll`) | def |
| 131 | local lemma | `invm_dom_rng` | section Preimage. | `Preimage.invm_dom_rng` | done |
| 140 | local lemma | `invmC'` | section Preimage. | `Preimage.invmC'` | done |
| 144 | local lemma | `invmC` | section Preimage. | `Preimage.invmC` | done |
| 148 | local lemma | `useful` | section Preimage. | `Preimage.useful` | done |
| 169 | local equiv | `equiv_sponge_perm` | section Preimage. | `Preimage.equiv_sponge_perm` (statement `equiv_sponge_perm.statement`) | stated |
| 194 | op | `same_ro` | section Preimage. | `same_ro` | def |
| 199 | op | `same_ro2` | section Preimage. | `same_ro2` | def |
| 204 | clone import | `Program` | section Preimage. | `Preimage.Prog.LoopSnoc.sample` | def |
| 209 | local equiv | `equiv_ro_iro` | section Preimage. | `Preimage.equiv_ro_iro` (statement `equiv_ro_iro.statement`) | stated |
| 393 | lemma | `Sponge_preimage_resistant` | section Preimage. | `Sponge_preimage_resistant` | stated |
| 481 | declare module | `A` | section SecondPreimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 483 | declare axiom | `A_ll` | section SecondPreimage. | `A_ll` (hypothesis `_A_ll`, `IndifRO_is_secure.D_ll`) | def |
| 485 | local lemma | `invm_dom_rng` | section SecondPreimage. | `SecondPreimage.invm_dom_rng` | done |
| 494 | local lemma | `invmC'` | section SecondPreimage. | `SecondPreimage.invmC'` | done |
| 498 | local lemma | `invmC` | section SecondPreimage. | `SecondPreimage.invmC` | done |
| 502 | local lemma | `useful` | section SecondPreimage. | `SecondPreimage.useful` | done |
| 523 | local equiv | `equiv_sponge_perm` | section SecondPreimage. | `SecondPreimage.equiv_sponge_perm` (statement `equiv_sponge_perm.statement`) | stated |
| 548 | clone import | `Program` | section SecondPreimage. | `SecondPreimage.Prog2.LoopSnoc.sample` | def |
| 553 | local equiv | `equiv_ro_iro` | section SecondPreimage. | `SecondPreimage.equiv_ro_iro` (statement `equiv_ro_iro.statement`) | stated |
| 737 | lemma | `Sponge_second_preimage_resistant` | section SecondPreimage. | `Sponge_second_preimage_resistant` | stated |
| 871 | declare module | `A` | section Collision. | `A` (parameter, with `hA`, `_hAd`) | def |
| 873 | declare axiom | `A_ll` | section Collision. | `A_ll` (hypothesis `_A_ll`, `IndifRO_is_secure.D_ll`) | def |
| 875 | local lemma | `invm_dom_rng` | section Collision. | `Collision.invm_dom_rng` | done |
| 884 | local lemma | `invmC'` | section Collision. | `Collision.invmC'` | done |
| 888 | local lemma | `invmC` | section Collision. | `Collision.invmC` | done |
| 892 | local lemma | `useful` | section Collision. | `Collision.useful` | done |
| 913 | local equiv | `equiv_sponge_perm` | section Collision. | `Collision.equiv_sponge_perm` (statement `equiv_sponge_perm.statement`) | stated |
| 937 | clone import | `Program` | section Collision. | `Collision.Prog3.LoopSnoc.sample` | def |
| 942 | local equiv | `equiv_ro_iro` | section Collision. | `Collision.equiv_ro_iro` (statement `equiv_ro_iro.statement`) | stated |
| 1126 | lemma | `Sponge_coll_resistant` | section Collision. | `Sponge_coll_resistant` | stated |
| 1241 | module | `X` |  | `X` | def |
| 1249 | module | `AdvCollisionSHA3` |  | `AdvCollisionSHA3` (`A` a Lean parameter) | def |
| 1259 | declare module | `A` | section SHA3_Collision. | `A` (parameter, with `hA`, `_hAd`) | def |
| 1261 | declare axiom | `A_ll` | section SHA3_Collision. | `A_ll` (hypothesis `_A_ll`, `IndifRO_is_secure.D_ll`) | def |
| 1263 | lemma | `SHA3_coll_resistant` | section SHA3_Collision. | `SHA3_coll_resistant` | stated |

## `proof/SHA3OSecurity.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3OSecurity.lean`, namespace `GaudisCrypt.SHA3.SHA3OSecurity`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 20 | op | `size_out` |  | `size_out` (field of `Params`) | def |
| 21 | axiom | `size_out_gt0` |  | `Params.size_out_gt0` | def |
| 23 | op | `sigma` |  | `sigma` | def |
| 24 | axiom | `sigma_ge0` |  | `Params.sigma_ge0` | def |
| 26 | op | `limit` |  | `limit` | def |
| 28 | type | `f_out` |  | `f_out` (field of `Params`) | def |
| 30 | op | `dout` |  | `dout` (field of `Params`) | def |
| 31 | axiom | `dout_ll` |  | `Params.dout_ll` | def |
| 32 | axiom | `dout_fu` |  | `Params.dout_fu` | def |
| 33 | axiom | `dout_full` |  | `Params.dout_full` | def |
| 36 | op | `to_list` |  | `to_list` (field of `Params`) | def |
| 37 | op | `of_list` |  | `of_list` (field of `Params`) | def |
| 38 | axiom | `spec_dout` |  | `Params.spec_dout` | def |
| 39 | axiom | `spec2_dout` |  | `Params.spec2_dout` | def |
| 40 | axiom | `to_list_inj` |  | `Params.to_list_inj` | def |
| 41 | axiom | `to_listK` |  | `Params.to_listK` | def |
| 43 | axiom | `dout_equal_dlist` |  | `Params.dout_equal_dlist` | def |
| 45 | lemma | `doutE1` |  | `doutE1` | done |
| 88 | clone import | `SecureORO` |  | `SORO` (namespace of abbreviations and `global_var`s; `realize`s: `SORO.axioms`) | def |
| 105 | clone import | `SecureHash` |  | `SH` (namespace of abbreviations and `global_var`s; `realize`s: `SH.axioms`) | def |
| 143 | module | `FSetSize` |  | `FSetSize` (`init` call-wrapped, E5; `FSetSize.get`) | def |
| 154 | module | `DFSetSize` |  | `DFSetSize` | def |
| 164 | module | `FIgnoreSize` |  | `FIgnoreSize` | def |
| 173 | module | `OSponge` |  | `OSponge` (`Module.comp`) | def |
| 177 | clone import | `Program` |  | `PBool.LoopSnoc.sample` | def |
| 182 | clone import | `FullRO` |  | `Eager` (namespace of abbreviations and `global_var`s) | def |
| 192 | declare module | `A` | section Preimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 194 | local module | `FInit` | section Preimage. | `Preimage.FInit` (aliases call-wrapped, E5) | def |
| 199 | local module | `PInit` | section Preimage. | `Preimage.PInit` (aliases call-wrapped, E5) | def |
| 206 | local module | `OF` | section Preimage. | `Preimage.OF` (aliases call-wrapped, E5) | def |
| 211 | local module | `Log` | section Preimage. | `Preimage.Log_m` (variable only: a lens, E6) | def |
| 215 | local module | `ExtendOutputSize` | section Preimage. | `Preimage.ExtendOutputSize` | def |
| 237 | local module | `OFC2` | section Preimage. | `Preimage.OFC2` (`Module.comp`) | def |
| 239 | local module | `ExtendOutput` | section Preimage. | `Preimage.ExtendOutput` (`f` call-wrapped, E5; `ExtendOutput.get`) | def |
| 248 | local module | `Dist_of_P1Adv` | section Preimage. | `Preimage.Dist_of_P1Adv` (`A` a Lean parameter) | def |
| 260 | local module | `SORO_P1` | section Preimage. | `Preimage.SORO_P1` (`A` a Lean parameter; `OFC2(F)` written out) | def |
| 271 | local module | `RFList` | section Preimage. | `Preimage.RFList` (variable: lens `RFList_m`, E6) | def |
| 287 | local module | `RFWhile` | section Preimage. | `Preimage.RFWhile` | def |
| 308 | local equiv | `rw_RF_List_While` | section Preimage. | `Preimage.rw_RF_List_While` | stated |
| 331 | op | `inv` | section Preimage. | `inv` | def |
| 337 | local equiv | `eq_IRO_RFWhile` | section Preimage. | `Preimage.eq_IRO_RFWhile` | stated |
| 407 | op | `eq_extend_size` | section Preimage. | `eq_extend_size` | def |
| 415 | local module | `ExtendSample` | section Preimage. | `Preimage.ExtendSample` (aliases call-wrapped, E5) | def |
| 430 | local equiv | `eq_extend` | section Preimage. | `Preimage.eq_extend` | stated |
| 471 | local lemma | `of_listK` | section Preimage. | `Preimage.of_listK` | done |
| 476 | local module | `Fill_In` | section Preimage. | `Preimage.Fill_In` (aliases call-wrapped, E5) | def |
| 496 | local equiv | `eq_eager_ideal` | section Preimage. | `Preimage.eq_eager_ideal` | stated |
| 512 | local equiv | `eq_eager_ideal2` | section Preimage. | `Preimage.eq_eager_ideal2` | stated |
| 559 | local module | `Dist` | section Preimage. | `Preimage.Dist` (`A` a Lean parameter; alias call-wrapped, E5) | def |
| 564 | local module | `Game` | section Preimage. | `Preimage.Game` (`A` a Lean parameter) | def |
| 576 | local lemma | `eager_ideal` | section Preimage. | `Preimage.eager_ideal` | stated |
| 652 | local lemma | `rw_ideal_2` | section Preimage. | `Preimage.rw_ideal_2` | stated |
| 792 | local lemma | `rw_ideal` | section Preimage. | `Preimage.rw_ideal` | stated |
| 870 | local lemma | `leq_ideal` | section Preimage. | `Preimage.leq_ideal` | stated |
| 881 | local lemma | `rw_real` | section Preimage. | `Preimage.rw_real` | stated |
| 898 | lemma | `Sponge_preimage_resistant` | section Preimage. | `Sponge_preimage_resistant` | stated |
| 923 | declare module | `A` | section SecondPreimage. | `A` (parameter, with `hA`, `_hAd`) | def |
| 925 | local module | `FInit` | section SecondPreimage. | `SecondPreimage.FInit` (aliases call-wrapped, E5) | def |
| 930 | local module | `PInit` | section SecondPreimage. | `SecondPreimage.PInit` (aliases call-wrapped, E5) | def |
| 937 | local module | `OF` | section SecondPreimage. | `SecondPreimage.OF` (aliases call-wrapped, E5) | def |
| 942 | local module | `Log` | section SecondPreimage. | `SecondPreimage.Log_m` (variable only: a lens, E6) | def |
| 946 | local module | `ExtendOutputSize` | section SecondPreimage. | `SecondPreimage.ExtendOutputSize` | def |
| 968 | local module | `OFC2` | section SecondPreimage. | `SecondPreimage.OFC2` (`Module.comp`) | def |
| 970 | local module | `ExtendOutput` | section SecondPreimage. | `SecondPreimage.ExtendOutput` (`f` call-wrapped, E5; `ExtendOutput.get`) | def |
| 979 | local module | `Dist_of_P2Adv` | section SecondPreimage. | `SecondPreimage.Dist_of_P2Adv` (`A` a Lean parameter; variable: lens `Dist_of_P2Adv_m`, E6) | def |
| 992 | local module | `SORO_P2` | section SecondPreimage. | `SecondPreimage.SORO_P2` (`A` a Lean parameter; `OFC2(F)` written out) | def |
| 1004 | local module | `RFList` | section SecondPreimage. | `SecondPreimage.RFList` (variable: lens `RFList_m`, E6) | def |
| 1020 | local module | `RFWhile` | section SecondPreimage. | `SecondPreimage.RFWhile` | def |
| 1042 | local equiv | `rw_RF_List_While` | section SecondPreimage. | `SecondPreimage.rw_RF_List_While` | stated |
| 1065 | local equiv | `eq_IRO_RFWhile` | section SecondPreimage. | `SecondPreimage.eq_IRO_RFWhile` | stated |
| 1136 | local module | `ExtendSample` | section SecondPreimage. | `SecondPreimage.ExtendSample` (aliases call-wrapped, E5) | def |
| 1151 | local equiv | `eq_extend` | section SecondPreimage. | `SecondPreimage.eq_extend` | stated |
| 1193 | local lemma | `of_listK` | section SecondPreimage. | `SecondPreimage.of_listK` | done |
| 1198 | local module | `Fill_In` | section SecondPreimage. | `SecondPreimage.Fill_In` (aliases call-wrapped, E5) | def |
| 1218 | local equiv | `eq_eager_ideal` | section SecondPreimage. | `SecondPreimage.eq_eager_ideal` | stated |
| 1234 | local equiv | `eq_eager_ideal2` | section SecondPreimage. | `SecondPreimage.eq_eager_ideal2` | stated |
| 1281 | local module | `Dist` | section SecondPreimage. | `SecondPreimage.Dist` (`A` a Lean parameter; alias call-wrapped, E5) | def |
| 1286 | local module | `Game` | section SecondPreimage. | `SecondPreimage.Game` (`A` a Lean parameter) | def |
| 1298 | local lemma | `eager_ideal` | section SecondPreimage. | `SecondPreimage.eager_ideal` | stated |
| 1427 | local equiv | `toto` | section SecondPreimage. | `SecondPreimage.toto` | stated |
| 1442 | local equiv | `titi` | section SecondPreimage. | `SecondPreimage.titi` | stated |
| 1476 | local lemma | `rw_ideal_2` | section SecondPreimage. | `SecondPreimage.rw_ideal_2` | stated |
| 1638 | local lemma | `rw_ideal` | section SecondPreimage. | `SecondPreimage.rw_ideal` | stated |
| 1727 | local lemma | `leq_ideal` | section SecondPreimage. | `SecondPreimage.leq_ideal` | stated |
| 1738 | local lemma | `rw_real` | section SecondPreimage. | `SecondPreimage.rw_real` | stated |
| 1771 | local module | `TOTO` | section SecondPreimage. | `SecondPreimage.TOTO` (`A` a Lean parameter) | def |
| 1780 | lemma | `Sponge_second_preimage_resistant` | section SecondPreimage. | `Sponge_second_preimage_resistant` | stated |
| 1811 | declare module | `A` | section Collision. | `A` (parameter, with `hA`, `_hAd`) | def |
| 1813 | local module | `FInit` | section Collision. | `Collision.FInit` (aliases call-wrapped, E5) | def |
| 1818 | local module | `PInit` | section Collision. | `Collision.PInit` (aliases call-wrapped, E5) | def |
| 1825 | local module | `OF` | section Collision. | `Collision.OF` (aliases call-wrapped, E5) | def |
| 1830 | local module | `Log` | section Collision. | `Collision.Log_m` (variable only: a lens, E6) | def |
| 1834 | local module | `ExtendOutputSize` | section Collision. | `Collision.ExtendOutputSize` | def |
| 1856 | local module | `OFC2` | section Collision. | `Collision.OFC2` (`Module.comp`) | def |
| 1858 | local module | `ExtendOutput` | section Collision. | `Collision.ExtendOutput` (`f` call-wrapped, E5; `ExtendOutput.get`) | def |
| 1867 | local module | `Dist_of_CollAdv` | section Collision. | `Collision.Dist_of_CollAdv` (`A` a Lean parameter; its unused variable `m` is omitted) | def |
| 1880 | local module | `SORO_Coll` | section Collision. | `Collision.SORO_Coll` (`A` a Lean parameter; `OFC2(F)` written out) | def |
| 1891 | local module | `RFList` | section Collision. | `Collision.RFList` (variable: lens `RFList_m`, E6) | def |
| 1907 | local module | `RFWhile` | section Collision. | `Collision.RFWhile` | def |
| 1929 | local equiv | `rw_RF_List_While` | section Collision. | `Collision.rw_RF_List_While` | stated |
| 1952 | local equiv | `eq_IRO_RFWhile` | section Collision. | `Collision.eq_IRO_RFWhile` | stated |
| 2023 | local module | `ExtendSample` | section Collision. | `Collision.ExtendSample` (aliases call-wrapped, E5) | def |
| 2038 | local equiv | `eq_extend` | section Collision. | `Collision.eq_extend` | stated |
| 2077 | local lemma | `of_listK` | section Collision. | `Collision.of_listK` | done |
| 2082 | local module | `Fill_In` | section Collision. | `Collision.Fill_In` (aliases call-wrapped, E5) | def |
| 2102 | local equiv | `eq_eager_ideal` | section Collision. | `Collision.eq_eager_ideal` | stated |
| 2118 | local equiv | `eq_eager_ideal2` | section Collision. | `Collision.eq_eager_ideal2` | stated |
| 2165 | local module | `Dist` | section Collision. | `Collision.Dist` (`A` a Lean parameter; alias call-wrapped, E5) | def |
| 2170 | local module | `Game` | section Collision. | `Collision.Game` (`A` a Lean parameter) | def |
| 2182 | local lemma | `eager_ideal` | section Collision. | `Collision.eager_ideal` | stated |
| 2310 | local equiv | `toto` | section Collision. | `Collision.toto` | stated |
| 2325 | local equiv | `titi` | section Collision. | `Collision.titi` | stated |
| 2359 | local lemma | `rw_ideal_2` | section Collision. | `Collision.rw_ideal_2` | stated |
| 2512 | local lemma | `rw_ideal` | section Collision. | `Collision.rw_ideal` | stated |
| 2598 | local lemma | `leq_ideal` | section Collision. | `Collision.leq_ideal` | stated |
| 2608 | local lemma | `rw_real` | section Collision. | `Collision.rw_real` | stated |
| 2634 | lemma | `Sponge_collision_resistant` | section Collision. | `Sponge_collision_resistant` | stated |

## Library: `theories/crypto/prp_prf/Strong_RP_RF.eca`

Lean: `GaudisCrypt/Lib/EC/Strong_RP_RF.lean`, namespace `GaudisCrypt.EC.Strong_RP_RF` (only what
`ConcreteF` uses, and what its proof needs).

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 29 | module | `ARP` |  | `ARP` (variables: lenses `coll`, `m`, `mi`) | def |
| 69 | module type | `Sample_t` |  | `Sample_t` | def |
| 73 | module | `Direct` |  | `Direct` | def |
| 82 | module | `Indirect` |  | `Indirect` | def |
| 94 | module | `PRPi'` |  | `PRPi'` (`init` alias call-wrapped, E5) | def |
| 122 | lemma | `notin_supportIP` |  | — (only for `excepted_lossless`; `dexcepted_ll` instead) | omitted |
| 131 | lemma | `excepted_lossless` |  | `excepted_lossless` (with `uD_full`) | done |
| 141 | phoare | `Indirect_ll` |  | — (unused downstream) | omitted |
| 154 | lemma | `PRPi'_Indirect_f_ll` |  | — (unused downstream) | omitted |
| 162 | lemma | `PRPi'_Indirect_fi_ll` |  | — (unused downstream) | omitted |
| 188 | local module | `PRP_indirect_bad` | section Upto. | `PRP_indirect_bad` (variable: lens `PRP_indirect_bad_bad`, E6; `PRP` view `asPRP`) | def |
| 230 | local lemma | `PRPi'_Indirect_eq` | section Upto. | `PRPi'_Indirect_eq` | done |
| 237 | lemma | `pr_PRPi'_Indirect_ARP` | section Upto. | `pr_PRPi'_Indirect_ARP` (via `pr_PRPi'_Indirect_ARP_of_region`) | done (exc E7, E8, E11) |
| 311 | module | `DBounder` |  | `DBounder` (`D` a Lean parameter), `DBounder.FBounder` (variable: lens `c`) | def |
| 354 | local module | `FEL` | section CollisionProbability. | — (the potential carries its invariant) | omitted |
| 392 | lemma | `pr_PRFi_collision` | section CollisionProbability. | `pr_PRFi_collision` | done (exc E8) |
| 494 | lemma | `PartialConclusion` |  | `PartialConclusion` | done (exc E6, E7, E8) |
| 512 | local clone | `Dexcepted.TwoStepSampling` | section PRPi_PRPi'_Indirect. | `dexcepted_indirect` (`Lib/EC/Dexcepted.lean`) | done |
| 532 | equiv | `eq_Direct_Indirect` | section PRPi_PRPi'_Indirect. | `eq_Direct_Indirect` (`={glob}` kept) | done |
| 544 | local equiv | `eq_PRPi_PRPi'_f_Indirect` | section PRPi_PRPi'_Indirect. | `eq_PRPi_PRPi'_f_Indirect` | done |
| 555 | local equiv | `eq_PRPi_PRPi'_fi_Indirect` | section PRPi_PRPi'_Indirect. | `eq_PRPi_PRPi'_fi_Indirect` | done |
| 556 | lemma | `pr_PRPi_PRPi'_Indirect` | section PRPi_PRPi'_Indirect. | `pr_PRPi_PRPi'_Indirect` | done (exc E8) |
| 568 | lemma | `Conclusion` |  | `Conclusion` | done (exc E6, E7, E8) |

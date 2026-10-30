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
| 52 | lemma | `dvdz_close` |  | `dvdz_close` | stated |
| 67 | lemma | `chunk_nil'` |  | `chunk_nil'` | stated |
| 70 | lemma | `chunk_sing'` |  | `chunk_sing'` | stated |
| 78 | lemma | `b0P` |  | `b0P` | stated |
| 85 | lemma | `bits2w_inj_eq` |  | `bits2w_inj_eq` | stated |
| 89 | lemma | `last_drop_all_but_last` |  | `last_drop_all_but_last` | stated |
| 102 | clone export | `PRP` |  | `PRPSec (PRP clone, at D := block × capacity)` | def |
| 105 | clone export | `StrongPRP` |  | `PRPSec` | def |
| 107 | clone export | `RP` |  | `Perm, dD, dD_ll, PRIMITIVE` | def |
| 119 | lemma | `needed_blocks0` |  | `needed_blocks0` | stated |
| 124 | lemma | `needed_blocks_non_pos` |  | `needed_blocks_non_pos` | stated |
| 133 | lemma | `needed_blocks_suff` |  | `needed_blocks_suff` | stated |
| 142 | lemma | `needed_blocks_correct` |  | `needed_blocks_correct` | stated |
| 156 | lemma | `needed_blocks_prod_r` |  | `needed_blocks_prod_r` | stated |
| 163 | lemma | `needed_blocks_eq_div_r` |  | `needed_blocks_eq_div_r` | stated |
| 181 | lemma | `needed_blocks_succ_eq_div_r` |  | `needed_blocks_succ_eq_div_r` | stated |
| 211 | lemma | `needed_blocks_rel_div_r` |  | `needed_blocks_rel_div_r` | stated |
| 221 | op | `num0` |  | `num0` | def |
| 223 | op | `mkpad` |  | `mkpad` | def |
| 225 | op | `pad` |  | `pad` | def |
| 227 | op | `unpad` |  | `unpad` | def |
| 234 | lemma | `rev_mkpad` |  | `rev_mkpad` | stated |
| 237 | lemma | `last_mkpad` |  | `last_mkpad` | stated |
| 240 | lemma | `head_mkpad` |  | `head_mkpad` | stated |
| 243 | lemma | `last_pad` |  | `last_pad` | stated |
| 246 | lemma | `size_mkpad` |  | `size_mkpad` | stated |
| 252 | lemma | `size_pad_equiv` |  | `size_pad_equiv` | stated |
| 259 | lemma | `size_padE` |  | `size_padE` | stated |
| 263 | lemma | `size_pad` |  | `size_pad` | stated |
| 267 | lemma | `size_pad_dvd_r` |  | `size_pad_dvd_r` | stated |
| 270 | lemma | `dvd_r_num0` |  | `dvd_r_num0` | stated |
| 273 | lemma | `num0_ge0` |  | `num0_ge0` | stated |
| 276 | lemma | `num0_ltr` |  | `num0_ltr` | stated |
| 279 | lemma | `index_true_behead_mkpad` |  | `index_true_behead_mkpad` | stated |
| 286 | lemma | `padE` |  | `padE` | stated |
| 294 | lemma | `padK` |  | `padK` | stated |
| 315 | lemma | `unpadK` |  | `unpadK` | stated |
| 342 | inductive | `unpad_spec` |  | `unpad_spec` | def |
| 348 | lemma | `unpadP` |  | `unpadP` | stated |
| 361 | op | `chunk` |  | `chunk` | def |
| 363 | lemma | `size_chunk` |  | `size_chunk` | stated |
| 366 | lemma | `in_chunk_size` |  | `in_chunk_size` | stated |
| 369 | lemma | `chunkK` |  | `chunkK` | stated |
| 372 | lemma | `chunk_nil` |  | `chunk_nil` | stated |
| 375 | lemma | `chunk_sing` |  | `chunk_sing` | stated |
| 378 | lemma | `chunk_cat` |  | `chunk_cat` | stated |
| 382 | lemma | `chunk_padK` |  | `chunk_padK` | stated |
| 385 | lemma | `flattenK` |  | `flattenK` | stated |
| 391 | op | `blocks2bits` |  | `blocks2bits` | def |
| 393 | lemma | `blocks2bits_nil` |  | `blocks2bits_nil` | stated |
| 396 | lemma | `blocks2bits_sing` |  | `blocks2bits_sing` | stated |
| 399 | lemma | `blocks2bits_cat` |  | `blocks2bits_cat` | stated |
| 403 | lemma | `size_blocks2bits` |  | `size_blocks2bits` | stated |
| 411 | lemma | `size_blocks2bits_dvd_r` |  | `size_blocks2bits_dvd_r` | stated |
| 414 | op | `bits2blocks` |  | `bits2blocks` | def |
| 416 | lemma | `bits2blocks_nil` |  | `bits2blocks_nil` | stated |
| 419 | lemma | `bits2blocks_sing` |  | `bits2blocks_sing` | stated |
| 423 | lemma | `bits2blocks_cat` |  | `bits2blocks_cat` | stated |
| 430 | lemma | `blocks2bitsK` |  | `blocks2bitsK` | stated |
| 438 | lemma | `bits2blocksK` |  | `bits2blocksK` | stated |
| 454 | op | `pad2blocks` |  | `pad2blocks` | def |
| 455 | op | `unpad_blocks` |  | `unpad_blocks` | def |
| 457 | lemma | `pad2blocksK` |  | `pad2blocksK` | stated |
| 463 | lemma | `unpadBlocksK` |  | `unpadBlocksK` | stated |
| 476 | lemma | `pad2blocks_inj` |  | `pad2blocks_inj` | stated |
| 481 | lemma | `size_pad2blocks` |  | `size_pad2blocks` | stated |
| 492 | op | `extend` |  | `extend` | def |
| 495 | op | `strip` |  | `strip` | def |
| 499 | lemma | `strip_ge0` |  | `strip_ge0` | stated |
| 503 | lemma | `extendK` |  | `extendK` | stated |
| 521 | lemma | `stripK` |  | `stripK` | stated |
| 545 | op | `valid_toplevel` |  | `valid_toplevel` | def |
| 549 | op | `valid_block` |  | `valid_block` | def |
| 551 | lemma | `valid_pad2blocks` |  | `valid_pad2blocks` | stated |
| 557 | inductive | `valid_block_spec` |  | `valid_block_spec` | def |
| 562 | lemma | `valid_blockP` |  | `valid_blockP` | stated |
| 575 | lemma | `valid_block_ends_not_b0` |  | `valid_block_ends_not_b0` | stated |
| 598 | inductive | `valid_block_struct_spec` |  | `valid_block_struct_spec` | def |
| 608 | lemma | `valid_block_structP` |  | `valid_block_structP` | stated |
| 718 | op | `valid_absorb` |  | `valid_absorb` | def |
| 720 | inductive | `valid_absorb_spec` |  | `valid_absorb_spec` | def |
| 726 | lemma | `valid_absorbP` |  | `valid_absorbP` | stated |

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
| 32 | lemma | `prefix_closed_equiv` |  | `prefix_closed_equiv` | stated |
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
| 111 | lemma | `half_permutation_set` |  | `half_permutation_set` | stated |
| 122 | lemma | `pre_permutation_set` |  | `pre_permutation_set` | stated |
| 131 | op | `step_hpath` |  | `step_hpath` | def |
| 138 | op | `build_hpath` |  | `build_hpath` | def |
| 141 | inductive | `build_hpath_spec` |  | `build_hpath_spec` | def |
| 149 | lemma | `build_hpathP` |  | `build_hpathP` | stated |
| 169 | lemma | `build_hpath_map0` |  | `build_hpath_map0` | stated |
| 177 | theory | `Prefix.` | theory Prefix. | `Prefix` (namespace) | def |
| 179 | op | `prefix` | theory Prefix. | `Prefix.«prefix»` | def |
| 185 | lemma | `prefix0s` | theory Prefix. | `Prefix.prefix0s` | stated |
| 188 | lemma | `prefixs0` | theory Prefix. | `Prefix.prefixs0` | stated |
| 191 | lemma | `prefix_eq` | theory Prefix. | `Prefix.prefix_eq` | stated |
| 195 | lemma | `prefixC` | theory Prefix. | `Prefix.prefixC` | stated |
| 203 | lemma | `prefix_ge0` | theory Prefix. | `Prefix.prefix_ge0` | stated |
| 211 | lemma | `prefix_sizel` | theory Prefix. | `Prefix.prefix_sizel` | stated |
| 219 | lemma | `prefix_sizer` | theory Prefix. | `Prefix.prefix_sizer` | stated |
| 225 | lemma | `prefix_take` | theory Prefix. | `Prefix.prefix_take` | stated |
| 234 | lemma | `take_take` | theory Prefix. | `Prefix.take_take` | stated |
| 250 | lemma | `prefix_take_leq` | theory Prefix. | `Prefix.prefix_take_leq` | stated |
| 257 | lemma | `prefix_nth` | theory Prefix. | `Prefix.prefix_nth` | stated |
| 268 | op | `max_prefix` | theory Prefix. | `Prefix.max_prefix` | def |
| 274 | op | `get_max_prefix` | theory Prefix. | `Prefix.get_max_prefix` | def |
| 278 | pred | `prefix_inv` | theory Prefix. | `Prefix.prefix_inv` | def |
| 289 | pred | `all_prefixes` | theory Prefix. | `Prefix.all_prefixes` | def |
| 292 | lemma | `aux_mem_get_max_prefix` | theory Prefix. | `Prefix.aux_mem_get_max_prefix` | stated |
| 301 | lemma | `mem_get_max_prefix` | theory Prefix. | `Prefix.mem_get_max_prefix` | stated |
| 308 | lemma | `take_get_max_prefix` | theory Prefix. | `Prefix.take_get_max_prefix` | stated |
| 317 | lemma | `take_get_max_prefix2` | theory Prefix. | `Prefix.take_get_max_prefix2` | stated |
| 328 | lemma | `prefix_cat` | theory Prefix. | `Prefix.prefix_cat` | stated |
| 332 | lemma | `prefix_leq_take` | theory Prefix. | `Prefix.prefix_leq_take` | stated |
| 342 | lemma | `prefix0` | theory Prefix. | `Prefix.prefix0` | stated |
| 350 | lemma | `head_nth0` | theory Prefix. | `Prefix.head_nth0` | stated |
| 353 | lemma | `get_prefix` | theory Prefix. | `Prefix.get_prefix` | stated |
| 386 | lemma | `get_max_prefix_leq` | theory Prefix. | `Prefix.get_max_prefix_leq` | stated |
| 390 | lemma | `get_max_prefix_is_max` | theory Prefix. | `Prefix.get_max_prefix_is_max` | stated |
| 397 | lemma | `get_max_prefix_max` | theory Prefix. | `Prefix.get_max_prefix_max` | stated |
| 402 | lemma | `all_take_in` | theory Prefix. | `Prefix.all_take_in` | stated |
| 416 | lemma | `prefix_inv_leq` | theory Prefix. | `Prefix.prefix_inv_leq` | stated |
| 434 | lemma | `max_prefix_eq` | theory Prefix. | `Prefix.max_prefix_eq` | stated |
| 440 | lemma | `prefix_max_prefix_eq_size` | theory Prefix. | `Prefix.prefix_max_prefix_eq_size` | stated |
| 456 | lemma | `prefix_get_max_prefix_eq_size` | theory Prefix. | `Prefix.prefix_get_max_prefix_eq_size` | stated |
| 463 | lemma | `get_max_prefix_exists` | theory Prefix. | `Prefix.get_max_prefix_exists` | stated |
| 473 | lemma | `prefix_geq` | theory Prefix. | `Prefix.prefix_geq` | stated |
| 482 | lemma | `prefix_take_prefix` | theory Prefix. | `Prefix.prefix_take_prefix` | stated |
| 491 | lemma | `prefix_leq_prefix_cat` | theory Prefix. | `Prefix.prefix_leq_prefix_cat` | stated |
| 498 | lemma | `prefix_take_leq_prefix` | theory Prefix. | `Prefix.prefix_take_leq_prefix` | stated |
| 506 | lemma | `prefix_take_geq_prefix` | theory Prefix. | `Prefix.prefix_take_geq_prefix` | stated |
| 519 | lemma | `get_max_prefix_take` | theory Prefix. | `Prefix.get_max_prefix_take` | stated |
| 534 | lemma | `drop_prefix_neq` | theory Prefix. | `Prefix.drop_prefix_neq` | stated |
| 541 | lemma | `prefix_prefix_prefix` | theory Prefix. | `Prefix.prefix_prefix_prefix` | stated |
| 548 | lemma | `prefix_lt_size` | theory Prefix. | `Prefix.prefix_lt_size` | stated |
| 574 | lemma | `asfadst` | theory Prefix. | `Prefix.asfadst` | stated |
| 589 | lemma | `prefix_exchange_prefix_inv` | theory Prefix. | `Prefix.prefix_exchange_prefix_inv` | stated |
| 606 | lemma | `prefix_inv_nil` | theory Prefix. | `Prefix.prefix_inv_nil` | stated |
| 616 | lemma | `aux_prefix_exchange` | theory Prefix. | `Prefix.aux_prefix_exchange` | stated |
| 634 | lemma | `prefix_exchange` | theory Prefix. | `Prefix.prefix_exchange` | stated |
| 654 | pred | `all_prefixes_fset` | theory Prefix. | `Prefix.all_prefixes_fset` | def |
| 657 | pred | `inv_prefix_block` | theory Prefix. | `Prefix.inv_prefix_block` | def |
| 664 | lemma | `prefix_gt0_mem` | theory Prefix. | `Prefix.prefix_gt0_mem` | stated |
| 673 | lemma | `inv_prefix_block_mem_take` | theory Prefix. | `Prefix.inv_prefix_block_mem_take` | stated |
| 686 | lemma | `prefix_cat_leq_prefix_size` | theory Prefix. | `Prefix.prefix_cat_leq_prefix_size` | stated |
| 694 | lemma | `prefix_cat1` | theory Prefix. | `Prefix.prefix_cat1` | stated |
| 707 | lemma | `prefix_leq_prefix_cat_size` | theory Prefix. | `Prefix.prefix_leq_prefix_cat_size` | stated |
| 753 | lemma | `diff_size_prefix_leq_cat` | theory Prefix. | `Prefix.diff_size_prefix_leq_cat` | stated |
| 787 | pred | `invm` | theory Prefix. | `Prefix.invm` | def |
| 790 | lemma | `invm_set` | theory Prefix. | `Prefix.invm_set` | stated |
| 807 | module | `C` |  | `C` | def |
| 816 | module | `PC` |  | `PC` | def |
| 839 | module | `DPRestr` |  | `DPRestr` | def |
| 861 | module | `PRestr` |  | `PRestr` (Lean function, `T.mk`) | def |
| 874 | module | `FC` |  | `FC` | def |
| 893 | module | `DFRestr` |  | `DFRestr` | def |
| 910 | module | `FRestr` |  | `FRestr` (Lean function, `T.mk`) | def |
| 923 | module | `DRestr` |  | `DRestr` (`D` a Lean parameter) | def |
| 932 | lemma | `rp_ll` |  | `rp_ll` | stated |
| 935 | lemma | `rpi_ll` |  | `rpi_ll` | stated |
| 938 | lemma | `rf_ll` |  | `rf_ll` | stated |
| 941 | lemma | `DRestr_ll` |  | `DRestr_ll` | stated |
| 957 | declare module | `F` | section RESTR. | `F` | def |
| 958 | declare module | `P` | section RESTR. | `P` | def |
| 959 | declare module | `D` | section RESTR. | `D` | def |
| 961 | lemma | `swap_restr` | section RESTR. | `swap_restr` | stated |
| 974 | declare module | `P` | section COUNT. | `P` | def |
| 975 | declare module | `CO` | section COUNT. | `CO` | def |
| 976 | declare module | `D` | section COUNT. | `D` | def |
| 978 | declare axiom | `f_ll` | section COUNT. | `f_ll` (hypothesis) | def |
| 979 | declare axiom | `fi_ll` | section COUNT. | `fi_ll` (hypothesis) | def |
| 981 | declare axiom | `CO_ll` | section COUNT. | `CO_ll` (hypothesis) | def |
| 983 | declare axiom | `D_ll` | section COUNT. | `D_ll` (hypothesis) | def |
| 987 | lemma | `Pr_restr` | section COUNT. | `Pr_restr` | stated |
| 1014 | op | `hinv` |  | `hinv` | def |
| 1017 | op | `hinvK` |  | `hinvK` | def |
| 1020 | op | `huniq` |  | `huniq` | def |
| 1026 | lemma | `hinvP` |  | `hinvP` | stated |
| 1036 | lemma | `huniq_hinv` |  | `huniq_hinv` | stated |
| 1048 | lemma | `hinvKP` |  | `hinvKP` | stated |
| 1058 | lemma | `huniq_hinvK` |  | `huniq_hinvK` | stated |
| 1065 | lemma | `huniq_hinvK_h` |  | `huniq_hinvK_h` | stated |
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
| 53 | local clone import | `Strong_RP_RF` | section . | `Switching` (namespace) | def |
| 77 | lemma | `size_behead` | section . | `size_behead` | stated |
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
| 272 | lemma | `m_mh_of_INV` |  | `m_mh_of_INV` | stated |
| 281 | lemma | `mi_mhi_of_INV` |  | `mi_mhi_of_INV` | stated |
| 290 | lemma | `incl_of_INV` |  | `incl_of_INV` | stated |
| 299 | lemma | `incli_of_INV` |  | `incli_of_INV` | stated |
| 308 | lemma | `mh_of_INV` |  | `mh_of_INV` | stated |
| 316 | lemma | `pi_of_INV` |  | `pi_of_INV` | stated |
| 324 | lemma | `hs_of_INV` |  | `hs_of_INV` | stated |
| 332 | lemma | `inv_of_INV` |  | `inv_of_INV` | stated |
| 338 | lemma | `invG_of_INV` |  | `invG_of_INV` | stated |
| 348 | lemma | `m_p_of_INV` |  | `m_p_of_INV` | stated |
| 353 | lemma | `all_prefixes_of_m_p` |  | `all_prefixes_of_m_p` | stated |
| 364 | lemma | `all_prefixes_of_INV` |  | `all_prefixes_of_INV` | stated |
| 375 | lemma | `ch_gt0` |  | `ch_gt0` | stated |
| 378 | lemma | `ch_neq0` |  | `ch_neq0` | stated |
| 381 | lemma | `ch_notdomE_hs` |  | `ch_notdomE_hs` | stated |
| 386 | lemma | `Sch_notdomE_hs` |  | `Sch_notdomE_hs` | stated |
| 391 | lemma | `ch_notdomE2_mh` |  | `ch_notdomE2_mh` | stated |
| 401 | lemma | `Sch_notdomE2_mh` |  | `Sch_notdomE2_mh` | stated |
| 411 | lemma | `dom_hs_neq_ch` |  | `dom_hs_neq_ch` | stated |
| 417 | lemma | `dom_hs_neq_Sch` |  | `dom_hs_neq_Sch` | stated |
| 423 | lemma | `notin_m_notin_mh` |  | `notin_m_notin_mh` | stated |
| 433 | lemma | `notin_m_notin_Gm` |  | `notin_m_notin_Gm` | stated |
| 439 | lemma | `notin_hs_notdomE2_mh` |  | `notin_hs_notdomE2_mh` | stated |
| 449 | lemma | `m_mh_addh` |  | `m_mh_addh` | stated |
| 465 | lemma | `m_mh_updh` |  | `m_mh_updh` | stated |
| 487 | lemma | `m_mh_addh_addm` |  | `m_mh_addh_addm` | stated |
| 508 | lemma | `mi_mhi_addh_addmi` |  | `mi_mhi_addh_addmi` | stated |
| 529 | lemma | `inv_mh_inv_Pm` |  | `inv_mh_inv_Pm` | stated |
| 544 | lemma | `inv_incl_none` |  | `inv_incl_none` | stated |
| 563 | lemma | `huniq_addh` |  | `huniq_addh` | stated |
| 576 | lemma | `hs_addh` |  | `hs_addh` | stated |
| 591 | lemma | `hs_updh` |  | `hs_updh` | stated |
| 610 | lemma | `mh_addh` |  | `mh_addh` | stated |
| 623 | lemma | `inv_addm` |  | `inv_addm` | stated |
| 637 | lemma | `incl_addm` |  | `incl_addm` | stated |
| 643 | op | `getflag` |  | `getflag` | def |
| 646 | lemma | `getflagP_none` |  | `getflagP_none` | stated |
| 650 | lemma | `getflagP_some` |  | `getflagP_some` | stated |
| 666 | lemma | `build_hpath_prefix` |  | `build_hpath_prefix` | stated |
| 676 | lemma | `build_hpath_up` |  | `build_hpath_up` | stated |
| 688 | lemma | `build_hpath_down` |  | `build_hpath_down` | stated |
| 702 | lemma | `known_path_uniq` |  | `known_path_uniq` | stated |
| 716 | lemma | `path_split` |  | `path_split` | stated |
| 742 | lemma | `lemma1` |  | `lemma1` | stated |
| 849 | lemma | `lemma1'` |  | `lemma1'` | stated |
| 955 | lemma | `lemma2` |  | `lemma2` | stated |
| 1053 | lemma | `lemma2'` |  | `lemma2'` | stated |
| 1165 | lemma | `lemma3` |  | `lemma3` | stated |
| 1247 | lemma | `m_mh_None` |  | `m_mh_None` | stated |
| 1257 | lemma | `build_hpath_None` |  | `build_hpath_None` | stated |
| 1261 | lemma | `build_hpath_upd_ch` |  | `build_hpath_upd_ch` | stated |
| 1282 | lemma | `build_hpath_up_None` |  | `build_hpath_up_None` | stated |
| 1309 | lemma | `build_hpath_upd_ch_iff` |  | `build_hpath_upd_ch_iff` | stated |
| 1326 | lemma | `lemma4` |  | `lemma4` | stated |
| 1349 | equiv | `eq_fi` |  | `eq_fi` | stated |
| 1488 | equiv | `eq_f` |  | `eq_f` | stated |
| 1815 | lemma | `head_nth` |  | `head_nth` | stated |
| 1818 | lemma | `drop_add` |  | `drop_add` | stated |
| 1824 | lemma | `behead_drop` |  | `behead_drop` | stated |
| 1827 | lemma | `incl_upd_nin` |  | `incl_upd_nin` | stated |
| 1836 | lemma | `lemma5` |  | `lemma5` | stated |
| 1863 | lemma | `lemma5'` |  | `lemma5'` | stated |
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
| 14 | lemma | `c_gt0r` |  | `c_gt0r` | stated |
| 17 | lemma | `c_ge0r` |  | `c_ge0r` | stated |
| 20 | lemma | `eps_ge0` |  | `eps_ge0` | stated |
| 27 | declare module | `D` | section PROOF. | `D` (section variable) | def |
| 29 | declare axiom | `D_ll` | section PROOF. | `D_ll` (hypothesis) | def |
| 33 | local module | `Gcol` | section PROOF. | `Gcol.sample_c`, `Gcol.M`, `Gcol.S` (modules), `Gcol` (`D` a Lean parameter) | def |
| 49 | module | `M` | section PROOF. | `Gcol.M` | def |
| 78 | module | `S` | section PROOF. | `Gcol.S` | def |
| 181 | lemma | `card_rng_set` | section PROOF. | `card_rng_set` | stated |
| 190 | lemma | `hinv_image` | section PROOF. | `hinv_image` | stated |
| 199 | local lemma | `Pr_col` | section PROOF. | `Pr_col` | stated |
| 220 | local equiv | `G1_col` | section PROOF. | `G1_col` | stated |
| 348 | lemma | `Pr_G1col` | section PROOF. | `Pr_G1col` | stated |

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
| 168 | lemma | `rng_restr` | section . | `rng_restr` | stated |
| 175 | equiv | `G1_G2` | section . | `G1_G2` | stated |
| 318 | declare module | `D` | section EXT. | `D` (section variable) | def |
| 320 | local module | `ReSample` | section EXT. | `ReSample` | def |
| 345 | local module | `Gext` | section EXT. | `Gext.resample`, `Gext.M`, `Gext.S` (modules), `Gext` (`D` a Lean parameter) | def |
| 351 | module | `M` | section EXT. | `Gext.M` | def |
| 379 | module | `S` | section EXT. | `Gext.S` | def |
| 492 | op | `inv_lt` | section EXT. | `inv_lt` | def |
| 497 | op | `inv_le` | section EXT. | `inv_le` | def |
| 502 | lemma | `fset0_eqP` | section EXT. | `fset0_eqP` | stated |
| 508 | lemma | `size_set` | section EXT. | `size_set` | stated |
| 518 | lemma | `size_set_le` | section EXT. | `size_set_le` | stated |
| 521 | lemma | `size_rem` | section EXT. | `size_rem` | stated |
| 529 | lemma | `size_rem_le` | section EXT. | `size_rem_le` | stated |
| 532 | lemma | `size_ge0` | section EXT. | `size_ge0` | stated |
| 535 | lemma | `size0` | section EXT. | `size0` | stated |
| 538 | local equiv | `RROset_inv_lt` | section EXT. | `RROset_inv_lt` | stated |
| 546 | local lemma | `Pr_ext` | section EXT. | `Pr_ext` | stated |
| 585 | local equiv | `EG2_Gext` | section EXT. | `EG2_Gext` | stated |
| 698 | declare axiom | `D_ll` | section EXT. | `D_ll` (hypothesis) | def |
| 702 | lemma | `Real_G2` | section EXT. | `Real_G2` | stated |

## `proof/smart_counter/Gconcl.ec`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Gconcl.lean`, namespace `GaudisCrypt.SHA3.Gconcl`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 9 | module | `IF` |  | `IF` | — |
| 14 | module | `S` |  | `S` | — |
| 67 | declare module | `D` | section . | `D` | — |
| 68 | local clone import | `Gext` | section . | `Gext` | — |
| 71 | local module | `G3` | section . | `G3` | — |
| 73 | module | `M` | section . | `M` | — |
| 104 | module | `S` | section . | `S` | — |
| 206 | local equiv | `G2_G3` | section . | `G2_G3` | — |
| 253 | local module | `G4` | section . | `G4` | — |
| 255 | module | `C` | section . | `C` | — |
| 270 | module | `S` | section . | `S` | — |
| 326 | local equiv | `G3_G4` | section . | `G3_G4` | — |
| 350 | local equiv | `G4_Ideal` | section . | `G4_Ideal` | — |
| 363 | declare axiom | `D_ll` | section . | `D_ll` | — |
| 369 | lemma | `Real_Ideal` | section . | `Real_Ideal` | — |

## `proof/BlockSponge.ec`

Lean: `GaudisCrypt/Examples/SHA3/BlockSponge.lean`, namespace `GaudisCrypt.SHA3.BlockSponge`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 9 | clone include | `Indifferentiability` |  | `Indifferentiability` | — |
| 21 | clone import | `IRO` |  | `IRO` | — |
| 29 | op | `format` |  | `format` | — |
| 30 | op | `parse` |  | `parse` | — |
| 32 | axiom | `formatK` |  | `formatK` | — |
| 33 | axiom | `parseK` |  | `parseK` | — |
| 34 | axiom | `parse_nil` |  | `parse_nil` | — |
| 36 | lemma | `parse_injective` |  | `parse_injective` | — |
| 41 | lemma | `parse_valid` |  | `parse_valid` | — |
| 56 | module | `C` |  | `C` | — |
| 63 | module | `FC` |  | `FC` | — |
| 76 | module | `PC` |  | `PC` | — |
| 98 | module | `DRestr` |  | `DRestr` | — |
| 110 | module | `Last` |  | `Last` | — |
| 119 | module | `` |  | `` | — |
| 123 | module | `` |  | `` | — |

## `proof/smart_counter/Gconcl_list.ec`

Lean: `GaudisCrypt/Examples/SHA3/SmartCounter/Gconcl_list.lean`, namespace `GaudisCrypt.SHA3.Gconcl_list`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 11 | op | `valid` |  | `valid` | — |
| 12 | axiom | `valid_spec` |  | `valid_spec` | — |
| 13 | axiom | `parse_gt0` |  | `parse_gt0` | — |
| 14 | axiom | `parse_not_valid` |  | `parse_not_valid` | — |
| 17 | axiom | `parse_twice` |  | `parse_twice` | — |
| 19 | axiom | `valid_uniq` |  | `valid_uniq` | — |
| 23 | clone export | `Handle` |  | `Handle` | — |
| 25 | module | `DSqueeze` |  | `DSqueeze` | — |
| 46 | module | `` |  | `` | — |
| 55 | module | `` |  | `` | — |
| 67 | module | `NIndif` |  | `NIndif` | — |
| 80 | module | `P` |  | `P` | — |
| 82 | clone | `IRO` |  | `IRO` | — |
| 88 | module | `Valid` |  | `Valid` | — |
| 102 | module | `SimLast` |  | `SimLast` | — |
| 111 | clone | `F` |  | `F` | — |
| 116 | op | `` | section Ideal. | `` | — |
| 119 | local lemma | `leq_add_nin` | section Ideal. | `leq_add_nin` | — |
| 128 | local lemma | `leq_add_in` | section Ideal. | `leq_add_in` | — |
| 136 | local lemma | `leq_nin_dom` | section Ideal. | `leq_nin_dom` | — |
| 141 | local lemma | `prefix_leq1` | section Ideal. | `prefix_leq1` | — |
| 159 | local lemma | `prefix_le1` | section Ideal. | `prefix_le1` | — |
| 171 | local lemma | `leq_add2` | section Ideal. | `leq_add2` | — |
| 177 | local equiv | `ideal_equiv` | section Ideal. | `ideal_equiv` | — |
| 296 | local module | `IF'` | section Ideal. | `IF'` | — |
| 315 | local module | `` | section Ideal. | `` | — |
| 319 | local module | `Valid2` | section Ideal. | `Valid2` | — |
| 330 | local module | `` | section Ideal. | `` | — |
| 334 | local equiv | `Ideal_equiv_valid` | section Ideal. | `Ideal_equiv_valid` | — |
| 365 | local equiv | `ideal_equiv2` | section Ideal. | `ideal_equiv2` | — |
| 388 | inductive | `inv_L_L3` | section Ideal. | `inv_L_L3` | — |
| 393 | local module | `IF2` | section Ideal. | `IF2` | — |
| 421 | local module | `` | section Ideal. | `` | — |
| 425 | local lemma | `lemma1` | section Ideal. | `lemma1` | — |
| 440 | local lemma | `lemma2` | section Ideal. | `lemma2` | — |
| 452 | local lemma | `incl_dom` | section Ideal. | `incl_dom` | — |
| 461 | local lemma | `lemma3` | section Ideal. | `lemma3` | — |
| 476 | local equiv | `Ideal_equiv3` | section Ideal. | `Ideal_equiv3` | — |
| 599 | local module | `D2` | section Ideal. | `D2` | — |
| 603 | local module | `D3` | section Ideal. | `D3` | — |
| 608 | module | `DSqueeze2` | section Ideal. | `DSqueeze2` | — |
| 647 | local module | `FValid` | section Ideal. | `FValid` | — |
| 657 | local module | `DValid` | section Ideal. | `DValid` | — |
| 659 | local module | `S2` | section Ideal. | `S2` | — |
| 661 | local module | `L4` | section Ideal. | `L4` | — |
| 665 | local equiv | `equiv_L3_L4` | section Ideal. | `equiv_L3_L4` | — |
| 788 | op | `inv_map` | section Ideal. | `inv_map` | — |
| 794 | inductive | `INV_L4_ideal` | section Ideal. | `INV_L4_ideal` | — |
| 801 | local lemma | `lemma5` | section Ideal. | `lemma5` | — |
| 819 | local lemma | `lemma5bis` | section Ideal. | `lemma5bis` | — |
| 843 | local equiv | `equiv_L4_ideal` | section Ideal. | `equiv_L4_ideal` | — |
| 916 | local module | `D5` | section Ideal. | `D5` | — |
| 919 | local module | `D6` | section Ideal. | `D6` | — |
| 922 | lemma | `equiv_ideal` | section Ideal. | `equiv_ideal` | — |
| 973 | inductive | `m_p` | section Real. | `m_p` | — |
| 979 | inductive | `INV_Real` | section Real. | `INV_Real` | — |
| 987 | local lemma | `INV_Real_incr` | section Real. | `INV_Real_incr` | — |
| 992 | local lemma | `INV_Real_addm_mi` | section Real. | `INV_Real_addm_mi` | — |
| 1004 | local lemma | `invmC'` | section Real. | `invmC'` | — |
| 1008 | local lemma | `invmC` | section Real. | `invmC` | — |
| 1012 | local lemma | `invm_dom_rng` | section Real. | `invm_dom_rng` | — |
| 1021 | local lemma | `all_prefixes_of_INV_real` | section Real. | `all_prefixes_of_INV_real` | — |
| 1029 | local lemma | `lemma2'` | section Real. | `lemma2'` | — |
| 1075 | local lemma | `take_nseq` | section Real. | `take_nseq` | — |
| 1086 | local lemma | `take_format` | section Real. | `take_format` | — |
| 1100 | local lemma | `equiv_sponge` | section Real. | `equiv_sponge` | — |
| 1101 | equiv | `` | section Real. | `` | — |
| 1437 | local lemma | `lemma4` | section Real. | `lemma4` | — |
| 1463 | local lemma | `lemma_3` | section Real. | `lemma_3` | — |
| 1493 | local lemma | `squeeze_squeezeless` | section Real. | `squeeze_squeezeless` | — |
| 1494 | equiv | `` | section Real. | `` | — |
| 1748 | lemma | `pr_real` | section Real. | `pr_real` | — |
| 1763 | declare module | `D` | section Real_Ideal. | `D` | — |
| 1765 | declare axiom | `D_lossless` | section Real_Ideal. | `D_lossless` | — |
| 1770 | lemma | `A_lossless` | section Real_Ideal. | `A_lossless` | — |
| 1786 | lemma | `concl` | section Real_Ideal. | `concl` | — |
| 1809 | declare module | `D` | section Real_Ideal_Abs. | `D` | — |
| 1811 | declare axiom | `D_lossless` | section Real_Ideal_Abs. | `D_lossless` | — |
| 1816 | local module | `Neg_D` | section Real_Ideal_Abs. | `Neg_D` | — |
| 1825 | local lemma | `Neg_D_lossless` | section Real_Ideal_Abs. | `Neg_D_lossless` | — |
| 1833 | local lemma | `useful` | section Real_Ideal_Abs. | `useful` | — |
| 1853 | local lemma | `invmC` | section Real_Ideal_Abs. | `invmC` | — |
| 1858 | local lemma | `Real_lossless` | section Real_Ideal_Abs. | `Real_lossless` | — |
| 1887 | local lemma | `Ideal_lossless` | section Real_Ideal_Abs. | `Ideal_lossless` | — |
| 1905 | local lemma | `neg_D_concl` | section Real_Ideal_Abs. | `neg_D_concl` | — |
| 1924 | lemma | `Inefficient_Real_Ideal` | section Real_Ideal_Abs. | `Inefficient_Real_Ideal` | — |
| 1946 | module | `Simulator` |  | `Simulator` | — |
| 2010 | declare module | `D` | section Simplify_Simulator. | `D` | — |
| 2012 | declare axiom | `D_lossless` | section Simplify_Simulator. | `D_lossless` | — |
| 2016 | local clone import | `PROM.FullRO` | section Simplify_Simulator. | `PROM.FullRO` | — |
| 2024 | local module | `Simu` | section Simplify_Simulator. | `Simu` | — |
| 2081 | local module | `L` | section Simplify_Simulator. | `L` | — |
| 2085 | local lemma | `equal1` | section Simplify_Simulator. | `equal1` | — |
| 2158 | local lemma | `equal2` | section Simplify_Simulator. | `equal2` | — |
| 2186 | lemma | `Simplify_simulator` | section Simplify_Simulator. | `Simplify_simulator` | — |
| 2202 | declare module | `D` | section Real_Ideal. | `D` | — |
| 2204 | declare axiom | `D_lossless` | section Real_Ideal. | `D_lossless` | — |
| 2209 | lemma | `Real_Ideal` | section Real_Ideal. | `Real_Ideal` | — |

## `proof/Sponge.ec`

Lean: `GaudisCrypt/Examples/SHA3/Sponge.lean`, namespace `GaudisCrypt.SHA3.Sponge`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 10 | clone include | `Indifferentiability` |  | `Indifferentiability` | — |
| 22 | clone import | `IRO` |  | `IRO` | — |
| 30 | module | `StdSponge` |  | `StdSponge` | — |
| 58 | module | `` |  | `` | — |
| 85 | lemma | `loop_cond` |  | `loop_cond` | — |
| 99 | equiv | `Sponge_is_StdSponge` |  | `Sponge_is_StdSponge` | — |
| 131 | module | `LowerFun` |  | `LowerFun` | — |
| 146 | module | `RaiseFun` |  | `RaiseFun` | — |
| 155 | module | `LowerDist` |  | `LowerDist` | — |
| 158 | module | `RaiseSim` |  | `RaiseSim` | — |
| 258 | module type | `HYBRID_IRO` |  | `HYBRID_IRO` | — |
| 268 | module type | `HYBRID_IRO_DIST` |  | `HYBRID_IRO_DIST` | — |
| 274 | module | `HybridIROExper` |  | `HybridIROExper` | — |
| 285 | module | `HybridIROLazy` |  | `HybridIROLazy` | — |
| 320 | module | `HybridIROEager` |  | `HybridIROEager` | — |
| 369 | declare module | `D` | section . | `D` | — |
| 371 | local clone import | `PROM.FullRO` | section . | `PROM.FullRO` | — |
| 378 | local module | `EROExper` | section . | `EROExper` | — |
| 387 | local lemma | `LRO_RO` | section . | `LRO_RO` | — |
| 398 | local module | `HIRO` | section . | `HIRO` | — |
| 424 | local lemma | `HybridIROLazy_HIRO_LRO_init` | section . | `HybridIROLazy_HIRO_LRO_init` | — |
| 425 | equiv | `` | section . | `` | — |
| 429 | local lemma | `HybridIROLazy_fill_in_LRO_get` | section . | `HybridIROLazy_fill_in_LRO_get` | — |
| 430 | equiv | `` | section . | `` | — |
| 442 | local lemma | `HybridIROLazy_HIRO_LRO_f` | section . | `HybridIROLazy_HIRO_LRO_f` | — |
| 443 | equiv | `` | section . | `` | — |
| 456 | local lemma | `HIRO_RO_HybridIROEager_init` | section . | `HIRO_RO_HybridIROEager_init` | — |
| 457 | equiv | `` | section . | `` | — |
| 461 | local lemma | `RO_get_HybridIROEager_fill_in` | section . | `RO_get_HybridIROEager_fill_in` | — |
| 462 | equiv | `` | section . | `` | — |
| 474 | local lemma | `RO_sample_HybridIROEager_fill_in` | section . | `RO_sample_HybridIROEager_fill_in` | — |
| 475 | equiv | `` | section . | `` | — |
| 487 | local lemma | `HIRO_RO_HybridIROEager_f` | section . | `HIRO_RO_HybridIROEager_f` | — |
| 488 | equiv | `` | section . | `` | — |
| 503 | local module | `RODist` | section . | `RODist` | — |
| 511 | local lemma | `Exper_HybridIROLazy_LRO` | section . | `Exper_HybridIROLazy_LRO` | — |
| 522 | local lemma | `Exper_RO_HybridIROEager` | section . | `Exper_RO_HybridIROEager` | — |
| 533 | lemma | `HybridIROExper_Lazy_Eager'` | section . | `HybridIROExper_Lazy_Eager'` | — |
| 544 | lemma | `HybridIROExper_Lazy_Eager` |  | `HybridIROExper_Lazy_Eager` | — |
| 553 | module | `RaiseHybridIRO` |  | `RaiseHybridIRO` | — |
| 568 | module | `LowerHybridIRO` |  | `LowerHybridIRO` | — |
| 579 | pred | `lazy_invar` |  | `lazy_invar` | — |
| 590 | lemma | `lazy_invar0` |  | `lazy_invar0` | — |
| 597 | lemma | `lazy_invar_mem_pad2blocks_l2r` |  | `lazy_invar_mem_pad2blocks_l2r` | — |
| 605 | lemma | `lazy_invar_mem_pad2blocks_r2l` |  | `lazy_invar_mem_pad2blocks_r2l` | — |
| 613 | lemma | `lazy_invar_vb` |  | `lazy_invar_vb` | — |
| 621 | lemma | `lazy_invar_lookup_eq` |  | `lazy_invar_lookup_eq` | — |
| 629 | lemma | `lazy_invar_upd_mem_dom_iff` |  | `lazy_invar_upd_mem_dom_iff` | — |
| 648 | lemma | `lazy_invar_upd2_vb` |  | `lazy_invar_upd2_vb` | — |
| 662 | lemma | `lazy_invar_upd_lu_eq` |  | `lazy_invar_upd_lu_eq` | — |
| 685 | lemma | `LowerFun_IRO_HybridIROLazy_f` |  | `LowerFun_IRO_HybridIROLazy_f` | — |
| 686 | equiv | `` |  | `` | — |
| 729 | lemma | `IRO_RaiseHybridIRO_HybridIROLazy_f` |  | `IRO_RaiseHybridIRO_HybridIROLazy_f` | — |
| 730 | equiv | `` |  | `` | — |
| 765 | pred | `eager_invar` |  | `eager_invar` | — |
| 777 | pred | `block_bits_all_in_dom` |  | `block_bits_all_in_dom` | — |
| 781 | pred | `block_bits_all_out_dom` |  | `block_bits_all_out_dom` | — |
| 785 | pred | `block_bits_dom_all_in_or_out` |  | `block_bits_dom_all_in_or_out` | — |
| 789 | lemma | `eager_inv_mem_mp1_ge0` |  | `eager_inv_mem_mp1_ge0` | — |
| 796 | lemma | `eager_inv_mem_mp2_ge0` |  | `eager_inv_mem_mp2_ge0` | — |
| 808 | lemma | `eager_invar0` |  | `eager_invar0` | — |
| 811 | lemma | `eager_inv_imp_block_bits_dom` |  | `eager_inv_imp_block_bits_dom` | — |
| 835 | lemma | `eager_inv_mem_dom1` |  | `eager_inv_mem_dom1` | — |
| 848 | lemma | `eager_inv_not_mem_dom1` |  | `eager_inv_not_mem_dom1` | — |
| 865 | lemma | `block_bits_dom_first_in_imp_all_in` |  | `block_bits_dom_first_in_imp_all_in` | — |
| 871 | lemma | `block_bits_dom_first_out_imp_all_out` |  | `block_bits_dom_first_out_imp_all_out` | — |
| 877 | lemma | `Lower_HybridIROEager_f` |  | `Lower_HybridIROEager_f` | — |
| 878 | equiv | `` |  | `` | — |
| 904 | module | `HybridIROEagerTrans` |  | `HybridIROEagerTrans` | — |
| 962 | pred | `eager_eq_except` |  | `eager_eq_except` | — |
| 968 | lemma | `eager_eq_except_mem_iff` |  | `eager_eq_except_mem_iff` | — |
| 976 | lemma | `eager_eq_except_upd1_eq_in` |  | `eager_eq_except_upd1_eq_in` | — |
| 987 | lemma | `eager_eq_except_upd2_eq_in` |  | `eager_eq_except_upd2_eq_in` | — |
| 998 | lemma | `eager_eq_except_maps_eq` |  | `eager_eq_except_maps_eq` | — |
| 1012 | lemma | `eager_invar_eq_except_upd1` |  | `eager_invar_eq_except_upd1` | — |
| 1079 | lemma | `HybridIROEagerTrans_next_block_split` |  | `HybridIROEagerTrans_next_block_split` | — |
| 1080 | equiv | `` |  | `` | — |
| 1188 | module | `BlockSpongeTrans` |  | `BlockSpongeTrans` | — |
| 1215 | clone | `Program` |  | `Program` | — |
| 1221 | lemma | `PrLoopSnoc_sample` |  | `PrLoopSnoc_sample` | — |
| 1235 | lemma | `iter_mul_one_half_pos` |  | `iter_mul_one_half_pos` | — |
| 1250 | module | `BlockGen` |  | `BlockGen` | — |
| 1269 | lemma | `BlockGen_loop_direct` |  | `BlockGen_loop_direct` | — |
| 1270 | equiv | `` |  | `` | — |
| 1307 | lemma | `HybridIROEagerTrans_BlockSpongeTrans_next_block` |  | `HybridIROEagerTrans_BlockSpongeTrans_next_block` | — |
| 1308 | equiv | `` |  | `` | — |
| 1507 | lemma | `HybridIROEagerTrans_BlockSpongeTrans_loop` |  | `HybridIROEagerTrans_BlockSpongeTrans_loop` | — |
| 1508 | equiv | `` |  | `` | — |
| 1614 | lemma | `HybridIROEager_f_BlockIRO_f` |  | `HybridIROEager_f_BlockIRO_f` | — |
| 1615 | equiv | `` |  | `` | — |
| 1873 | lemma | `HybridIROEager_BlockIRO_f` |  | `HybridIROEager_BlockIRO_f` | — |
| 1874 | equiv | `` |  | `` | — |
| 1915 | declare module | `BlockSim` | section . | `BlockSim` | — |
| 1916 | declare module | `Dist` | section . | `Dist` | — |
| 1918 | local clone | `HybridIRO` | section . | `HybridIRO` | — |
| 1922 | local lemma | `Sponge_Raise_BlockSponge_f` | section . | `Sponge_Raise_BlockSponge_f` | — |
| 1923 | equiv | `` | section . | `` | — |
| 1953 | local lemma | `RealIndif_Sponge_BlockSponge` | section . | `RealIndif_Sponge_BlockSponge` | — |
| 1970 | local lemma | `Ideal_IRO_Experiment_HybridLazy` | section . | `Ideal_IRO_Experiment_HybridLazy` | — |
| 2008 | local module | `` | section . | `` | — |
| 2021 | local lemma | `Experiment_HybridIROExper_Lazy` | section . | `Experiment_HybridIROExper_Lazy` | — |
| 2036 | local lemma | `HybridIROExper_Experiment_Eager` | section . | `HybridIROExper_Experiment_Eager` | — |
| 2053 | local lemma | `Experiment_Hybrid_Lazy_Eager` | section . | `Experiment_Hybrid_Lazy_Eager` | — |
| 2070 | local lemma | `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` | section . | `RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f` | — |
| 2071 | equiv | `` | section . | `` | — |
| 2094 | local lemma | `Experiment_HybridEager_Ideal_BlockIRO` | section . | `Experiment_HybridEager_Ideal_BlockIRO` | — |
| 2128 | local lemma | `IdealIndif_IRO_BlockIRO` | section . | `IdealIndif_IRO_BlockIRO` | — |
| 2138 | lemma | `conclu` | section . | `conclu` | — |
| 2153 | lemma | `conclusion` |  | `conclusion` | — |

## `proof/SHA3Indiff.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3Indiff.lean`, namespace `GaudisCrypt.SHA3.SHA3Indiff`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 12 | op | `limit` |  | `limit` | — |
| 17 | type | `state` |  | `state` | — |
| 18 | op | `parse` |  | `parse` | — |
| 19 | op | `valid` |  | `valid` | — |
| 22 | module | `Simulator` |  | `Simulator` | — |
| 88 | module | `Cntr` |  | `Cntr` | — |
| 96 | module | `FC` |  | `FC` | — |
| 116 | module | `PC` |  | `PC` | — |
| 137 | module | `DRestr` |  | `DRestr` | — |
| 148 | declare module | `Dist` | section . | `Dist` | — |
| 151 | declare axiom | `Dist_lossless` | section . | `Dist_lossless` | — |
| 155 | lemma | `drestr_commute1` | section . | `drestr_commute1` | — |
| 185 | lemma | `drestr_commute2` | section . | `drestr_commute2` | — |
| 223 | op | `wit_pair` | section . | `wit_pair` | — |
| 225 | local equiv | `equiv_sim_f` | section . | `equiv_sim_f` | — |
| 245 | local equiv | `equiv_sim_fi` | section . | `equiv_sim_fi` | — |
| 255 | local lemma | `replace_simulator` | section . | `replace_simulator` | — |
| 270 | lemma | `security` | section . | `security` | — |
| 309 | lemma | `SHA3Indiff` |  | `SHA3Indiff` | — |

## `proof/SHA3_OIndiff.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3_OIndiff.lean`, namespace `GaudisCrypt.SHA3.SHA3_OIndiff`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 16 | clone import | `OptionIndifferentiability` |  | `OptionIndifferentiability` | — |
| 23 | module | `FSome` |  | `FSome` | — |
| 32 | module | `PSome` |  | `PSome` | — |
| 46 | module | `Poget` |  | `Poget` | — |
| 59 | module | `` |  | `` | — |
| 61 | module | `OSimulator` |  | `OSimulator` | — |
| 115 | module | `Counter` |  | `Counter` | — |
| 122 | op | `increase_counter` |  | `increase_counter` | — |
| 126 | module | `OFC` |  | `OFC` | — |
| 140 | module | `OPC` |  | `OPC` | — |
| 161 | module | `ODRestr` |  | `ODRestr` | — |
| 171 | declare module | `Dist` | section . | `Dist` | — |
| 175 | local module | `DFSome` | section . | `DFSome` | — |
| 183 | module | `DPSome` | section . | `DPSome` | — |
| 196 | local module | `` | section . | `` | — |
| 205 | lemma | `SHA3OIndiff` | section . | `SHA3OIndiff` | — |

## `proof/SecureHash.eca`

Lean: `GaudisCrypt/Examples/SHA3/SecureHash.lean`, namespace `GaudisCrypt.SHA3.SecureHash`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 4 | type | `from` |  | `from` | — |
| 7 | clone import | `OptionIndifferentiability` |  | `OptionIndifferentiability` | — |
| 14 | op | `sampleto` |  | `sampleto` | — |
| 16 | op | `bound` |  | `bound` | — |
| 17 | axiom | `bound_ge0` |  | `bound_ge0` | — |
| 19 | axiom | `sampleto_ll` |  | `sampleto_ll` | — |
| 20 | axiom | `sampleto_full` |  | `sampleto_full` | — |
| 21 | axiom | `sampleto_fu` |  | `sampleto_fu` | — |
| 29 | op | `increase_counter` |  | `increase_counter` | — |
| 30 | axiom | `increase_counter_spec` |  | `increase_counter_spec` | — |
| 49 | module | `Bounder` |  | `Bounder` | — |
| 56 | module | `FBounder` |  | `FBounder` | — |
| 72 | module | `PBounder` |  | `PBounder` | — |
| 95 | module type | `AdvPreimage` |  | `AdvPreimage` | — |
| 99 | module | `Preimage` |  | `Preimage` | — |
| 113 | module type | `AdvSecondPreimage` |  | `AdvSecondPreimage` | — |
| 117 | module | `SecondPreimage` |  | `SecondPreimage` | — |
| 131 | module type | `AdvCollision` |  | `AdvCollision` | — |
| 135 | module | `Collision` |  | `Collision` | — |

## `proof/SecureRO.eca`

Lean: `GaudisCrypt/Examples/SHA3/SecureRO.lean`, namespace `GaudisCrypt.SHA3.SecureRO`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 7 | type | `from` |  | `from` | — |
| 9 | op | `sampleto` |  | `sampleto` | — |
| 11 | op | `bound` |  | `bound` | — |
| 12 | axiom | `bound_gt0` |  | `bound_gt0` | — |
| 14 | axiom | `sampleto_ll` |  | `sampleto_ll` | — |
| 15 | axiom | `sampleto_full` |  | `sampleto_full` | — |
| 16 | axiom | `sampleto_fu` |  | `sampleto_fu` | — |
| 18 | clone import | `PROM.FullRO` |  | `PROM.FullRO` | — |
| 26 | op | `increase_counter` |  | `increase_counter` | — |
| 27 | axiom | `increase_counter_spec` |  | `increase_counter_spec` | — |
| 29 | op | `bound_counter` |  | `bound_counter` | — |
| 30 | axiom | `bound_counter_ge0` |  | `bound_counter_ge0` | — |
| 32 | module | `Counter` |  | `Counter` | — |
| 39 | module type | `RF` |  | `RF` | — |
| 44 | module | `Bounder` |  | `Bounder` | — |
| 65 | module type | `Oracle` |  | `Oracle` | — |
| 69 | module type | `AdvPreimage` |  | `AdvPreimage` | — |
| 73 | module | `Preimage` |  | `Preimage` | — |
| 89 | declare module | `A` | section Preimage. | `A` | — |
| 91 | local module | `FEL` | section Preimage. | `FEL` | — |
| 100 | local module | `Preimage2` | section Preimage. | `Preimage2` | — |
| 112 | lemma | `RO_is_preimage_resistant` | section Preimage. | `RO_is_preimage_resistant` | — |
| 189 | module type | `AdvSecondPreimage` |  | `AdvSecondPreimage` | — |
| 193 | module | `SecondPreimage` |  | `SecondPreimage` | — |
| 215 | declare module | `A` | section SecondPreimage. | `A` | — |
| 217 | local module | `FEL` | section SecondPreimage. | `FEL` | — |
| 227 | local module | `SecondPreimage2` | section SecondPreimage. | `SecondPreimage2` | — |
| 246 | local module | `D1` | section SecondPreimage. | `D1` | — |
| 255 | local module | `SecondPreimage3` | section SecondPreimage. | `SecondPreimage3` | — |
| 267 | lemma | `RO_is_second_preimage_resistant` | section SecondPreimage. | `RO_is_second_preimage_resistant` | — |
| 370 | module type | `AdvCollision` |  | `AdvCollision` | — |
| 374 | module | `Collision` |  | `Collision` | — |
| 395 | declare module | `A` | section Collision. | `A` | — |
| 397 | local module | `FEL` | section Collision. | `FEL` | — |
| 406 | local module | `Collision2` | section Collision. | `Collision2` | — |
| 424 | op | `collision` | section Collision. | `collision` | — |
| 427 | lemma | `RO_is_collision_resistant` | section Collision. | `RO_is_collision_resistant` | — |

## `proof/SecureORO.eca`

Lean: `GaudisCrypt/Examples/SHA3/SecureORO.lean`, namespace `GaudisCrypt.SHA3.SecureORO`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 7 | type | `from` |  | `from` | — |
| 9 | op | `sampleto` |  | `sampleto` | — |
| 11 | op | `bound` |  | `bound` | — |
| 12 | axiom | `bound_ge0` |  | `bound_ge0` | — |
| 14 | axiom | `sampleto_ll` |  | `sampleto_ll` | — |
| 15 | axiom | `sampleto_full` |  | `sampleto_full` | — |
| 16 | axiom | `sampleto_fu` |  | `sampleto_fu` | — |
| 18 | clone import | `PROM.FullRO` |  | `PROM.FullRO` | — |
| 26 | op | `increase_counter` |  | `increase_counter` | — |
| 27 | axiom | `increase_counter_spec` |  | `increase_counter_spec` | — |
| 29 | module type | `RF` |  | `RF` | — |
| 35 | module | `RF` |  | `RF` | — |
| 45 | module | `Bounder` |  | `Bounder` | — |
| 63 | module type | `Oracle` |  | `Oracle` | — |
| 67 | module type | `AdvPreimage` |  | `AdvPreimage` | — |
| 71 | module | `Preimage` |  | `Preimage` | — |
| 84 | declare module | `A` | section Preimage. | `A` | — |
| 86 | local module | `FEL` | section Preimage. | `FEL` | — |
| 95 | local module | `Preimage2` | section Preimage. | `Preimage2` | — |
| 106 | lemma | `RO_is_preimage_resistant` | section Preimage. | `RO_is_preimage_resistant` | — |
| 185 | module type | `AdvSecondPreimage` |  | `AdvSecondPreimage` | — |
| 189 | module | `SecondPreimage` |  | `SecondPreimage` | — |
| 203 | declare module | `A` | section SecondPreimage. | `A` | — |
| 205 | local module | `FEL` | section SecondPreimage. | `FEL` | — |
| 215 | local module | `SecondPreimage2` | section SecondPreimage. | `SecondPreimage2` | — |
| 226 | local module | `D1` | section SecondPreimage. | `D1` | — |
| 235 | local module | `SecondPreimage3` | section SecondPreimage. | `SecondPreimage3` | — |
| 247 | lemma | `RO_is_second_preimage_resistant` | section SecondPreimage. | `RO_is_second_preimage_resistant` | — |
| 349 | module type | `AdvCollision` |  | `AdvCollision` | — |
| 353 | module | `Collision` |  | `Collision` | — |
| 366 | declare module | `A` | section Collision. | `A` | — |
| 368 | local module | `FEL` | section Collision. | `FEL` | — |
| 377 | local module | `Collision2` | section Collision. | `Collision2` | — |
| 387 | op | `collision` | section Collision. | `collision` | — |
| 390 | lemma | `RO_is_collision_resistant` | section Collision. | `RO_is_collision_resistant` | — |

## `proof/IndifRO_is_secure.ec`

Lean: `GaudisCrypt/Examples/SHA3/IndifRO_is_secure.lean`, namespace `GaudisCrypt.SHA3.IndifRO_is_secure`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 5 | type | `block.` |  | `block.` | — |
| 6 | type | `f_in.` |  | `f_in.` | — |
| 7 | type | `f_out.` |  | `f_out.` | — |
| 9 | op | `sampleto` |  | `sampleto` | — |
| 10 | axiom | `sampleto_ll` |  | `sampleto_ll` | — |
| 11 | axiom | `sampleto_fu` |  | `sampleto_fu` | — |
| 12 | axiom | `sampleto_full` |  | `sampleto_full` | — |
| 14 | op | `limit` |  | `limit` | — |
| 15 | axiom | `limit_gt0` |  | `limit_gt0` | — |
| 17 | op | `bound` |  | `bound` | — |
| 20 | op | `bound_counter` |  | `bound_counter` | — |
| 21 | axiom | `bound_counter_ge0` |  | `bound_counter_ge0` | — |
| 23 | op | `increase_counter` |  | `increase_counter` | — |
| 24 | axiom | `increase_counter_spec` |  | `increase_counter_spec` | — |
| 27 | clone import | `SecureRO` |  | `SecureRO` | — |
| 40 | clone import | `Indifferentiability` |  | `Indifferentiability` | — |
| 45 | module | `RO` |  | `RO` | — |
| 50 | module | `FInit` |  | `FInit` | — |
| 59 | module | `GetF` |  | `GetF` | — |
| 64 | module | `SInit` |  | `SInit` | — |
| 75 | module | `FM` |  | `FM` | — |
| 88 | module | `DColl` |  | `DColl` | — |
| 94 | declare module | `A` | section Collision. | `A` | — |
| 96 | declare axiom | `D_ll` | section Collision. | `D_ll` | — |
| 99 | lemma | `coll_resistant_if_indifferentiable` | section Collision. | `coll_resistant_if_indifferentiable` | — |
| 128 | module | `DPre` |  | `DPre` | — |
| 139 | declare module | `A` | section Preimage. | `A` | — |
| 141 | declare axiom | `D_ll` | section Preimage. | `D_ll` | — |
| 144 | lemma | `preimage_resistant_if_indifferentiable` | section Preimage. | `preimage_resistant_if_indifferentiable` | — |
| 174 | module | `D2Pre` |  | `D2Pre` | — |
| 185 | declare module | `A` | section SecondPreimage. | `A` | — |
| 187 | declare axiom | `D_ll` | section SecondPreimage. | `D_ll` | — |
| 190 | lemma | `second_preimage_resistant_if_indifferentiable` | section SecondPreimage. | `second_preimage_resistant_if_indifferentiable` | — |

## `proof/SHA3Security.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3Security.lean`, namespace `GaudisCrypt.SHA3.SHA3Security`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 8 | module | `SHA3` |  | `SHA3` | — |
| 17 | op | `size_out` |  | `size_out` | — |
| 18 | axiom | `size_out_gt0` |  | `size_out_gt0` | — |
| 20 | op | `sigma` |  | `sigma` | — |
| 21 | axiom | `sigma_gt0` |  | `sigma_gt0` | — |
| 23 | type | `f_out.` |  | `f_out.` | — |
| 25 | op | `dout` |  | `dout` | — |
| 26 | axiom | `dout_ll` |  | `dout_ll` | — |
| 27 | axiom | `dout_fu` |  | `dout_fu` | — |
| 28 | axiom | `dout_full` |  | `dout_full` | — |
| 31 | op | `to_list` |  | `to_list` | — |
| 32 | op | `of_list` |  | `of_list` | — |
| 33 | axiom | `spec_dout` |  | `spec_dout` | — |
| 34 | axiom | `spec2_dout` |  | `spec2_dout` | — |
| 35 | axiom | `to_list_inj` |  | `to_list_inj` | — |
| 36 | axiom | `to_listK` |  | `to_listK` | — |
| 38 | axiom | `dout_equal_dlist` |  | `dout_equal_dlist` | — |
| 40 | lemma | `doutE1` |  | `doutE1` | — |
| 62 | module | `CSetSize` |  | `CSetSize` | — |
| 71 | module | `FSetSize` |  | `FSetSize` | — |
| 80 | clone import | `IndifRO_is_secure` |  | `IndifRO_is_secure` | — |
| 103 | module | `FGetSize` |  | `FGetSize` | — |
| 111 | module | `SimSetSize` |  | `SimSetSize` | — |
| 113 | module | `DFSetSize` |  | `DFSetSize` | — |
| 121 | module | `` |  | `` | — |
| 127 | declare module | `A` | section Preimage. | `A` | — |
| 129 | declare axiom | `A_ll` | section Preimage. | `A_ll` | — |
| 131 | local lemma | `invm_dom_rng` | section Preimage. | `invm_dom_rng` | — |
| 140 | local lemma | `invmC'` | section Preimage. | `invmC'` | — |
| 144 | local lemma | `invmC` | section Preimage. | `invmC` | — |
| 148 | local lemma | `useful` | section Preimage. | `useful` | — |
| 169 | local equiv | `equiv_sponge_perm` | section Preimage. | `equiv_sponge_perm` | — |
| 194 | op | `same_ro` | section Preimage. | `same_ro` | — |
| 199 | op | `same_ro2` | section Preimage. | `same_ro2` | — |
| 204 | clone import | `Program` | section Preimage. | `Program` | — |
| 209 | local equiv | `equiv_ro_iro` | section Preimage. | `equiv_ro_iro` | — |
| 393 | lemma | `Sponge_preimage_resistant` | section Preimage. | `Sponge_preimage_resistant` | — |
| 481 | declare module | `A` | section SecondPreimage. | `A` | — |
| 483 | declare axiom | `A_ll` | section SecondPreimage. | `A_ll` | — |
| 485 | local lemma | `invm_dom_rng` | section SecondPreimage. | `invm_dom_rng` | — |
| 494 | local lemma | `invmC'` | section SecondPreimage. | `invmC'` | — |
| 498 | local lemma | `invmC` | section SecondPreimage. | `invmC` | — |
| 502 | local lemma | `useful` | section SecondPreimage. | `useful` | — |
| 523 | local equiv | `equiv_sponge_perm` | section SecondPreimage. | `equiv_sponge_perm` | — |
| 548 | clone import | `Program` | section SecondPreimage. | `Program` | — |
| 553 | local equiv | `equiv_ro_iro` | section SecondPreimage. | `equiv_ro_iro` | — |
| 737 | lemma | `Sponge_second_preimage_resistant` | section SecondPreimage. | `Sponge_second_preimage_resistant` | — |
| 871 | declare module | `A` | section Collision. | `A` | — |
| 873 | declare axiom | `A_ll` | section Collision. | `A_ll` | — |
| 875 | local lemma | `invm_dom_rng` | section Collision. | `invm_dom_rng` | — |
| 884 | local lemma | `invmC'` | section Collision. | `invmC'` | — |
| 888 | local lemma | `invmC` | section Collision. | `invmC` | — |
| 892 | local lemma | `useful` | section Collision. | `useful` | — |
| 913 | local equiv | `equiv_sponge_perm` | section Collision. | `equiv_sponge_perm` | — |
| 937 | clone import | `Program` | section Collision. | `Program` | — |
| 942 | local equiv | `equiv_ro_iro` | section Collision. | `equiv_ro_iro` | — |
| 1126 | lemma | `Sponge_coll_resistant` | section Collision. | `Sponge_coll_resistant` | — |
| 1241 | module | `X` |  | `X` | — |
| 1249 | module | `AdvCollisionSHA3` |  | `AdvCollisionSHA3` | — |
| 1259 | declare module | `A` | section SHA3_Collision. | `A` | — |
| 1261 | declare axiom | `A_ll` | section SHA3_Collision. | `A_ll` | — |
| 1263 | lemma | `SHA3_coll_resistant` | section SHA3_Collision. | `SHA3_coll_resistant` | — |

## `proof/SHA3OSecurity.ec`

Lean: `GaudisCrypt/Examples/SHA3/SHA3OSecurity.lean`, namespace `GaudisCrypt.SHA3.SHA3OSecurity`.

| EC line | kind | EC name | context | Lean name | status |
|---:|---|---|---|---|---|
| 20 | op | `size_out` |  | `size_out` | — |
| 21 | axiom | `size_out_gt0` |  | `size_out_gt0` | — |
| 23 | op | `sigma` |  | `sigma` | — |
| 24 | axiom | `sigma_ge0` |  | `sigma_ge0` | — |
| 26 | op | `limit` |  | `limit` | — |
| 28 | type | `f_out.` |  | `f_out.` | — |
| 30 | op | `dout` |  | `dout` | — |
| 31 | axiom | `dout_ll` |  | `dout_ll` | — |
| 32 | axiom | `dout_fu` |  | `dout_fu` | — |
| 33 | axiom | `dout_full` |  | `dout_full` | — |
| 36 | op | `to_list` |  | `to_list` | — |
| 37 | op | `of_list` |  | `of_list` | — |
| 38 | axiom | `spec_dout` |  | `spec_dout` | — |
| 39 | axiom | `spec2_dout` |  | `spec2_dout` | — |
| 40 | axiom | `to_list_inj` |  | `to_list_inj` | — |
| 41 | axiom | `to_listK` |  | `to_listK` | — |
| 43 | axiom | `dout_equal_dlist` |  | `dout_equal_dlist` | — |
| 45 | lemma | `doutE1` |  | `doutE1` | — |
| 88 | clone import | `SecureORO` |  | `SecureORO` | — |
| 105 | clone import | `SecureHash` |  | `SecureHash` | — |
| 143 | module | `FSetSize` |  | `FSetSize` | — |
| 154 | module | `DFSetSize` |  | `DFSetSize` | — |
| 164 | module | `FIgnoreSize` |  | `FIgnoreSize` | — |
| 173 | module | `` |  | `` | — |
| 177 | clone import | `Program` |  | `Program` | — |
| 182 | clone import | `FullRO` |  | `FullRO` | — |
| 192 | declare module | `A` | section Preimage. | `A` | — |
| 194 | local module | `FInit` | section Preimage. | `FInit` | — |
| 199 | local module | `PInit` | section Preimage. | `PInit` | — |
| 206 | local module | `OF` | section Preimage. | `OF` | — |
| 211 | local module | `Log` | section Preimage. | `Log` | — |
| 215 | local module | `ExtendOutputSize` | section Preimage. | `ExtendOutputSize` | — |
| 237 | local module | `OFC2` | section Preimage. | `OFC2` | — |
| 239 | local module | `ExtendOutput` | section Preimage. | `ExtendOutput` | — |
| 248 | local module | `` | section Preimage. | `` | — |
| 260 | local module | `` | section Preimage. | `` | — |
| 271 | local module | `RFList` | section Preimage. | `RFList` | — |
| 287 | local module | `RFWhile` | section Preimage. | `RFWhile` | — |
| 308 | local equiv | `rw_RF_List_While` | section Preimage. | `rw_RF_List_While` | — |
| 331 | op | `inv` | section Preimage. | `inv` | — |
| 337 | local equiv | `eq_IRO_RFWhile` | section Preimage. | `eq_IRO_RFWhile` | — |
| 407 | op | `eq_extend_size` | section Preimage. | `eq_extend_size` | — |
| 415 | local module | `ExtendSample` | section Preimage. | `ExtendSample` | — |
| 430 | local equiv | `eq_extend` | section Preimage. | `eq_extend` | — |
| 471 | local lemma | `of_listK` | section Preimage. | `of_listK` | — |
| 476 | local module | `Fill_In` | section Preimage. | `Fill_In` | — |
| 496 | local equiv | `eq_eager_ideal` | section Preimage. | `eq_eager_ideal` | — |
| 512 | local equiv | `eq_eager_ideal2` | section Preimage. | `eq_eager_ideal2` | — |
| 559 | local module | `Dist` | section Preimage. | `Dist` | — |
| 564 | local module | `Game` | section Preimage. | `Game` | — |
| 576 | local lemma | `eager_ideal` | section Preimage. | `eager_ideal` | — |
| 652 | local lemma | `rw_ideal_2` | section Preimage. | `rw_ideal_2` | — |
| 792 | local lemma | `rw_ideal` | section Preimage. | `rw_ideal` | — |
| 870 | local lemma | `leq_ideal` | section Preimage. | `leq_ideal` | — |
| 881 | local lemma | `rw_real` | section Preimage. | `rw_real` | — |
| 898 | lemma | `Sponge_preimage_resistant` | section Preimage. | `Sponge_preimage_resistant` | — |
| 923 | declare module | `A` | section SecondPreimage. | `A` | — |
| 925 | local module | `FInit` | section SecondPreimage. | `FInit` | — |
| 930 | local module | `PInit` | section SecondPreimage. | `PInit` | — |
| 937 | local module | `OF` | section SecondPreimage. | `OF` | — |
| 942 | local module | `Log` | section SecondPreimage. | `Log` | — |
| 946 | local module | `ExtendOutputSize` | section SecondPreimage. | `ExtendOutputSize` | — |
| 968 | local module | `OFC2` | section SecondPreimage. | `OFC2` | — |
| 970 | local module | `ExtendOutput` | section SecondPreimage. | `ExtendOutput` | — |
| 979 | local module | `` | section SecondPreimage. | `` | — |
| 992 | local module | `` | section SecondPreimage. | `` | — |
| 1004 | local module | `RFList` | section SecondPreimage. | `RFList` | — |
| 1020 | local module | `RFWhile` | section SecondPreimage. | `RFWhile` | — |
| 1042 | local equiv | `rw_RF_List_While` | section SecondPreimage. | `rw_RF_List_While` | — |
| 1065 | local equiv | `eq_IRO_RFWhile` | section SecondPreimage. | `eq_IRO_RFWhile` | — |
| 1136 | local module | `ExtendSample` | section SecondPreimage. | `ExtendSample` | — |
| 1151 | local equiv | `eq_extend` | section SecondPreimage. | `eq_extend` | — |
| 1193 | local lemma | `of_listK` | section SecondPreimage. | `of_listK` | — |
| 1198 | local module | `Fill_In` | section SecondPreimage. | `Fill_In` | — |
| 1218 | local equiv | `eq_eager_ideal` | section SecondPreimage. | `eq_eager_ideal` | — |
| 1234 | local equiv | `eq_eager_ideal2` | section SecondPreimage. | `eq_eager_ideal2` | — |
| 1281 | local module | `Dist` | section SecondPreimage. | `Dist` | — |
| 1286 | local module | `Game` | section SecondPreimage. | `Game` | — |
| 1298 | local lemma | `eager_ideal` | section SecondPreimage. | `eager_ideal` | — |
| 1427 | local equiv | `toto` | section SecondPreimage. | `toto` | — |
| 1442 | local equiv | `titi` | section SecondPreimage. | `titi` | — |
| 1476 | local lemma | `rw_ideal_2` | section SecondPreimage. | `rw_ideal_2` | — |
| 1638 | local lemma | `rw_ideal` | section SecondPreimage. | `rw_ideal` | — |
| 1727 | local lemma | `leq_ideal` | section SecondPreimage. | `leq_ideal` | — |
| 1738 | local lemma | `rw_real` | section SecondPreimage. | `rw_real` | — |
| 1771 | local module | `TOTO` | section SecondPreimage. | `TOTO` | — |
| 1780 | lemma | `Sponge_second_preimage_resistant` | section SecondPreimage. | `Sponge_second_preimage_resistant` | — |
| 1811 | declare module | `A` | section Collision. | `A` | — |
| 1813 | local module | `FInit` | section Collision. | `FInit` | — |
| 1818 | local module | `PInit` | section Collision. | `PInit` | — |
| 1825 | local module | `OF` | section Collision. | `OF` | — |
| 1830 | local module | `Log` | section Collision. | `Log` | — |
| 1834 | local module | `ExtendOutputSize` | section Collision. | `ExtendOutputSize` | — |
| 1856 | local module | `OFC2` | section Collision. | `OFC2` | — |
| 1858 | local module | `ExtendOutput` | section Collision. | `ExtendOutput` | — |
| 1867 | local module | `` | section Collision. | `` | — |
| 1880 | local module | `` | section Collision. | `` | — |
| 1891 | local module | `RFList` | section Collision. | `RFList` | — |
| 1907 | local module | `RFWhile` | section Collision. | `RFWhile` | — |
| 1929 | local equiv | `rw_RF_List_While` | section Collision. | `rw_RF_List_While` | — |
| 1952 | local equiv | `eq_IRO_RFWhile` | section Collision. | `eq_IRO_RFWhile` | — |
| 2023 | local module | `ExtendSample` | section Collision. | `ExtendSample` | — |
| 2038 | local equiv | `eq_extend` | section Collision. | `eq_extend` | — |
| 2077 | local lemma | `of_listK` | section Collision. | `of_listK` | — |
| 2082 | local module | `Fill_In` | section Collision. | `Fill_In` | — |
| 2102 | local equiv | `eq_eager_ideal` | section Collision. | `eq_eager_ideal` | — |
| 2118 | local equiv | `eq_eager_ideal2` | section Collision. | `eq_eager_ideal2` | — |
| 2165 | local module | `Dist` | section Collision. | `Dist` | — |
| 2170 | local module | `Game` | section Collision. | `Game` | — |
| 2182 | local lemma | `eager_ideal` | section Collision. | `eager_ideal` | — |
| 2310 | local equiv | `toto` | section Collision. | `toto` | — |
| 2325 | local equiv | `titi` | section Collision. | `titi` | — |
| 2359 | local lemma | `rw_ideal_2` | section Collision. | `rw_ideal_2` | — |
| 2512 | local lemma | `rw_ideal` | section Collision. | `rw_ideal` | — |
| 2598 | local lemma | `leq_ideal` | section Collision. | `leq_ideal` | — |
| 2608 | local lemma | `rw_real` | section Collision. | `rw_real` | — |
| 2634 | lemma | `Sponge_collision_resistant` | section Collision. | `Sponge_collision_resistant` | — |

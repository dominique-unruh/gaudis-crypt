# SHA-3: dependency graph

The files of the development in dependency order, each with the files it `require`s:

```
proof/Common.ec                        <- 
proof/Indifferentiability.eca          <- 
proof/OptionIndifferentiability.eca    <- 
proof/IRO.eca                          <- 
proof/smart_counter/SLCommon.ec        <- Common.ec, Indifferentiability.eca
proof/smart_counter/ConcreteF.eca      <- Common.ec, SLCommon.ec
proof/smart_counter/Handle.eca         <- Common.ec, ConcreteF.eca, SLCommon.ec
proof/smart_counter/Gcol.eca           <- Common.ec, Handle.eca, SLCommon.ec
proof/smart_counter/Gext.eca           <- Common.ec, Gcol.eca, SLCommon.ec
proof/smart_counter/Gconcl.ec          <- Common.ec, Gext.eca, SLCommon.ec
proof/BlockSponge.ec                   <- Common.ec, Gconcl.ec, IRO.eca, Indifferentiability.eca, SLCommon.ec
proof/smart_counter/Gconcl_list.ec     <- BlockSponge.ec, Common.ec, Gconcl.ec, Handle.eca, SLCommon.ec
proof/Sponge.ec                        <- BlockSponge.ec, Common.ec, IRO.eca
proof/SHA3Indiff.ec                    <- BlockSponge.ec, Common.ec, Gconcl_list.ec, SLCommon.ec, Sponge.ec
proof/SHA3_OIndiff.ec                  <- BlockSponge.ec, Common.ec, Gconcl_list.ec, OptionIndifferentiability.eca, SHA3Indiff.ec, SLCommon.ec, Sponge.ec
proof/SecureHash.eca                   <- OptionIndifferentiability.eca
proof/SecureRO.eca                     <- 
proof/SecureORO.eca                    <- 
proof/IndifRO_is_secure.ec             <- Indifferentiability.eca, SecureRO.eca
proof/SHA3Security.ec                  <- Common.ec, IndifRO_is_secure.ec, SHA3Indiff.ec, SLCommon.ec, Sponge.ec
proof/SHA3OSecurity.ec                 <- Common.ec, SHA3_OIndiff.ec, SLCommon.ec, SecureHash.eca, SecureORO.eca, Sponge.ec
```

EasyCrypt standard-library theories `require`d directly:

`AdvAbsVal`, `AllCore`, `BitEncoding`, `BitWord`, `Bool`, `Core`, `DBool`, `DList`, `DProd`, `Dexcepted`, `Distr`, `FMap`, `FSet`, `FelTactic`, `FinType`, `Int`, `IntDiv`, `List`, `Monoid`, `Mu_mem`, `PROM`, `PRP`, `Real`, `Ring`, `StdBigop`, `StdOrder`, `StdRing`, `Strong_RP_RF`

// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: Lean.Meta.Tactic.Grind.Attr Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Canon Lean.Meta.Tactic.Grind.MarkNestedProofs Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Proof Lean.Meta.Tactic.Grind.Propagate Lean.Meta.Tactic.Grind.PP Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Ctor Lean.Meta.Tactic.Grind.Parser Lean.Meta.Tactic.Grind.EMatchTheorem Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Main Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Arith Lean.Meta.Tactic.Grind.Ext Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.Diseq Lean.Meta.Tactic.Grind.MBTC Lean.Meta.Tactic.Grind.Lookahead
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1340_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_41_;
static lean_object* l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_744_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1599_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1562_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_859_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_970_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_896_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_263_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_337_;
static lean_object* l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_744_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_374_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1488_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1081_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_820_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_189_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_933_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1525_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1044_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1118_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_300_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1451_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1118_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_859_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_782_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1562_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_782_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_933_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1451_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1007_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1562_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1414_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1377_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_559_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1155_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_933_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1192_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1525_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_448_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1229_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1636_(lean_object*);
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1599_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1192_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_374_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_411_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_226_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_411_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_115_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1303_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_896_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1599_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_670_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_411_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_633_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_485_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1451_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1044_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_41_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_522_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1303_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_263_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1081_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1340_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_670_;
static lean_object* l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1414_(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_820_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_300_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1155_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_189_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_707_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_337_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1340_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_896_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1266_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_596_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1414_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_374_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_115_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_970_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_744_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_226_;
static lean_object* l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_559_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1155_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_707_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_;
static lean_object* l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_78_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1636_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1192_;
static lean_object* l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_633_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_933_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_970_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_522_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_448_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_300_;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1414_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_707_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1007_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_152_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_337_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_633_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1599_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1673_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1081_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_152_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1488_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_782_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1673_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_896_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1562_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1636_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1525_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1007_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1118_;
static lean_object* l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_41_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_115_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1044_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1488_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_970_;
static lean_object* l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_670_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_485_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1451_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1044_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1229_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_78_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1192_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1673_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1636_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_522_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1081_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1229_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1266_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_820_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596_(lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_596_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_744_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1303_(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1266_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind___hyg_4_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1007_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1118_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485_(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1229_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_859_;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522_(lean_object*);
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_2 = l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_41_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_41_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_41_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_41_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_41_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_41_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_78_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_78_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(78u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_78_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_78_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_115_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqc", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_115_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_115_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_115_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(115u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_115_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_115_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_152_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_152_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(152u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_152_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_152_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ematch", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_189_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_189_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(189u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pattern", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_226_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_226_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(226u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_226_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_226_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instance", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_263_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_263_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(263u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_263_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_263_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_300_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assignment", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_300_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_300_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_300_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(300u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_300_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_300_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_337_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqResolution", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_337_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_337_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_337_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(337u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_337_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_337_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_374_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_374_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_374_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_374_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(374u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_374_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_374_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_411_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_411_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_411_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_411_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(411u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_411_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_411_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_448_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_448_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(448u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_448_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_448_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("candidate", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_485_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_485_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(485u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_485_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_485_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_522_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resolved", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_522_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_522_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_522_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(522u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_522_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_522_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_559_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_559_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(559u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_559_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_559_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mbtc", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_596_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_596_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(596u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_596_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_596_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ext", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_633_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_633_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(633u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_633_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_633_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_633_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_670_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_670_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(670u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_670_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_670_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_670_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lookahead", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_707_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_707_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(707u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_707_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_707_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_707_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_744_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_744_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_744_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_744_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(744u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_744_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_744_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_744_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_782_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_782_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_782_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_782_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(782u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_782_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_782_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_820_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_820_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(820u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_820_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_820_;
x_3 = lean_box(1);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_820_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(859u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_859_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_896_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proofs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_896_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_896_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_896_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(896u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_896_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_896_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_896_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_933_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_933_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_933_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_933_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(933u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_933_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_933_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_933_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_970_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proof", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_970_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_970_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_970_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(970u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_970_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_970_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_970_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1007_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1007_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1007_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1007_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1007u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1007_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1007_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1007_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1044_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parent", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1044_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1044_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1044_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1044u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1044_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1044_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1044_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1081_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("final", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1081_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1081_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1081_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1081u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1081_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1081_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1081_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1118_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forallPropagator", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1118_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1118_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1118_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1118u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1118_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1118_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1118_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1155_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1155_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1155u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1155_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1155_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1155_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1192_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canon", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1192_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1192_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1192_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1192u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1192_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1192_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1229_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("activate", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1229_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1229_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1229_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1229u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1229_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1229_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1229_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1266_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1266_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1266u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1266_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1266_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1266_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1303_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1303_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1303u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1303_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1303_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1303_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1340_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1340_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1340u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1340_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1340_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1340_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1377_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1377_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1377u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1377_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1414_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lambda", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1414_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1414_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1414_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1414u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1414_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1414_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1414_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1451_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proveFalse", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1451_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1451_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_4 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1451_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1451u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1451_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1451_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1451_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1488_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1488_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1488u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1488_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1488_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1488_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1525_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1525_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1525u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1525_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1525_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1525_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1562_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proveEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1562_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1562_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1562_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1562u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1562_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1562_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1562_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1599_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pushNewFact", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1599_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1599_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1599_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1599u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1599_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1599_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1599_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1636_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("appMap", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1636_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1636_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1636_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1636u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1636_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1636_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1636_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1673_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_;
x_3 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1673_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1673u);
x_2 = l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1673_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1673_;
x_3 = lean_box(0);
x_4 = l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1673_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Propagate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__7____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__8____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__9____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__10____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__11____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__12____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__13____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__14____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__15____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__16____x40_Lean_Meta_Tactic_Grind___hyg_4_);
l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind___hyg_4_ = _init_l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__17____x40_Lean_Meta_Tactic_Grind___hyg_4_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_41_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_41_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_41_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_41_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_41_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_41_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_41_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_41_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_78_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_78_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_78_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_78_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_78_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_78_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_78_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_78_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_115_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_115_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_115_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_115_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_115_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_115_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_115_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_115_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_152_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_152_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_152_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_152_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_152_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_152_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_152_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_152_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_189_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_189_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_189_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_189_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_189_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_189_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_189_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_226_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_226_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_226_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_226_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_226_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_226_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_226_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_226_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_263_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_263_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_263_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_263_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_263_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_263_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_263_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_263_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_300_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_300_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_300_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_300_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_300_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_300_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_300_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_300_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_300_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_300_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_337_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_337_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_337_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_337_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_337_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_337_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_337_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_337_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_337_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_337_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_374_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_374_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_374_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_374_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_374_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_374_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_374_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_374_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_374_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_374_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_411_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_411_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_411_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_411_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_411_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_411_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_411_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_411_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_411_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_411_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_448_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_448_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_448_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_448_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_448_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_448_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_448_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_448_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_485_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_485_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_485_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_485_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_485_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_485_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_485_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_485_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_522_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_522_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_522_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_522_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_522_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_522_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_522_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_522_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_522_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_522_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_559_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_559_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_559_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_559_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_559_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_559_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_559_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_559_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_596_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_596_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_596_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_596_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_596_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_596_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_596_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_596_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_633_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_633_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_633_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_633_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_633_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_633_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_633_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_633_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_670_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_670_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_670_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_670_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_670_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_670_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_670_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_707_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_707_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_707_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_707_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_707_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_707_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_707_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_707_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_744_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_744_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_744_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_744_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_744_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_744_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_744_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_744_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_744_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_744_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_782_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_782_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_782_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_782_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_782_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_782_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_782_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_782_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_782_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_782_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_820_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_820_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_820_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_820_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_820_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_820_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_820_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_859_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_859_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_859_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_859_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_859_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_859_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_859_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_859_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_896_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_896_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_896_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_896_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_896_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_896_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_896_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_896_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_896_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_896_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_933_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_933_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_933_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_933_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_933_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_933_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_933_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_933_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_933_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_933_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_970_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_970_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_970_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_970_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_970_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_970_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_970_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_970_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_970_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_970_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1007_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1007_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1007_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1007_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1007_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1007_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1007_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1007_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1007_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1007_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1044_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1044_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1044_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1044_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1044_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1044_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1044_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1044_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1044_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1044_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1081_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1081_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1081_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1081_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1081_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1081_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1081_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1081_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1081_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1081_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1118_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1118_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1118_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1118_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1118_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1118_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1118_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1118_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1118_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1118_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1155_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1155_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1155_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1155_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1155_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1155_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1155_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1192_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1192_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1192_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1192_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1192_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1192_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1192_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1192_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1192_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1229_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1229_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1229_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1229_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1229_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1229_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1229_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1229_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1229_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1229_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1266_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1266_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1266_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1266_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1266_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1266_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1266_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1303_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1303_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1303_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1303_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1303_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1303_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1303_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1340_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1340_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1340_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1340_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1340_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1340_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1340_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1377_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1377_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1377_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1377_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1377_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1377_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1377_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1377_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1414_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1414_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1414_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1414_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1414_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1414_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1414_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1414_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1414_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1414_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1451_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1451_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1451_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1451_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1451_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1451_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1451_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1451_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1451_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1451_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1488_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1488_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1488_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1488_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1488_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1488_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1488_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1525_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1525_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1525_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1525_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1525_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1525_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1525_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1562_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1562_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1562_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1562_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1562_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1562_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1562_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1562_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1562_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1562_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1599_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1599_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1599_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1599_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1599_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1599_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1599_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1599_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1599_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1599_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1636_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1636_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1636_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1636_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1636_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1636_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1636_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1636_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Tactic_Grind___hyg_1636_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1636_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1673_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1673_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Tactic_Grind___hyg_1673_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1673_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1673_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Tactic_Grind___hyg_1673_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind___hyg_1673_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

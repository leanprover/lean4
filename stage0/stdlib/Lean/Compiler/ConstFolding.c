// Lean compiler output
// Module: Lean.Compiler.ConstFolding
// Imports: Init Lean.Expr
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__24;
static lean_object* l_Lean_Compiler_unFoldFns___closed__3;
static lean_object* l_Lean_Compiler_boolFoldFns___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___boxed(lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__18;
static lean_object* l_Lean_Compiler_mkNatLt___closed__1;
static lean_object* l_Lean_Compiler_mkNatEq___closed__4;
static lean_object* l_Lean_Compiler_mkUIntTypeName___closed__1;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__25;
static lean_object* l_Lean_Compiler_mkLcProof___closed__3;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__6;
static lean_object* l_Lean_Compiler_unFoldFns___closed__11;
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__6;
static lean_object* l_Lean_Compiler_natFoldFns___closed__34;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__21;
static lean_object* l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__5;
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn(lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__26;
static lean_object* l_Lean_Compiler_mkNatLt___closed__5;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__3;
static lean_object* l_Lean_Compiler_boolFoldFns___closed__8;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__17;
static lean_object* l_Lean_Compiler_foldNatDiv___rarg___closed__1;
static lean_object* l_Lean_Compiler_natFoldFns___closed__35;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__15;
static lean_object* l_Lean_Compiler_foldUIntSub___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_boolFoldFns;
static lean_object* l_Lean_Compiler_natFoldFns___closed__50;
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn(lean_object*);
static lean_object* l_Lean_Compiler_mkNatLe___closed__2;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldUIntAdd___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__43;
static lean_object* l_Lean_Compiler_natFoldFns___closed__36;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default___boxed(lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__25;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__1;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd(uint8_t);
lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__29;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLe(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__17;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldNatDecLt___closed__1;
static lean_object* l_Lean_Compiler_natFoldFns___closed__11;
static lean_object* l_Lean_Compiler_natFoldFns___closed__37;
static lean_object* l_Lean_Compiler_boolFoldFns___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow(uint8_t);
static lean_object* l_Lean_Compiler_foldNatBeq___rarg___closed__1;
static lean_object* l_Lean_Compiler_mkNatLt___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv(uint8_t);
static lean_object* l_Lean_Compiler_natFoldFns___closed__18;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__8;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq(uint8_t);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__28;
static lean_object* l_Lean_Compiler_natFoldFns___closed__23;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__4;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_natFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldNatDecLe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__15;
uint8_t l_List_any___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_binFoldFns___closed__2;
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatEq___closed__1;
static lean_object* l_Lean_Compiler_foldNatBinBoolPred___closed__1;
static lean_object* l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___boxed(lean_object*);
static lean_object* l_Lean_Compiler_mkNatLe___closed__3;
static lean_object* l_Lean_Compiler_boolFoldFns___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___boxed(lean_object*);
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul(uint8_t);
static lean_object* l_Lean_Compiler_mkNatLe___closed__1;
static lean_object* l_Lean_Compiler_boolFoldFns___closed__10;
static lean_object* l_Lean_Compiler_natFoldFns___closed__47;
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat(lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__32;
static lean_object* l_Lean_Compiler_foldNatMod___rarg___closed__1;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___boxed(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__28;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_unFoldFns___closed__10;
static lean_object* l_Lean_Compiler_natFoldFns___closed__46;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_unFoldFns___closed__8;
static lean_object* l_Lean_Compiler_foldNatDecEq___closed__2;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__22;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_uintBinFoldFns;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatLe___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__40;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__14;
LEAN_EXPORT lean_object* lean_fold_bin_op(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinOp(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__13;
static lean_object* l_Lean_Compiler_unFoldFns___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_boolFoldFns___closed__3;
static lean_object* l_Lean_Compiler_natFoldFns___closed__3;
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__2;
static lean_object* l_Lean_Compiler_natFoldFns___closed__7;
static lean_object* l_Lean_Compiler_unFoldFns___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_preUIntBinFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatEq___closed__5;
static lean_object* l_Lean_Compiler_mkNatEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__23;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__18;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit(lean_object*);
static lean_object* l_Lean_Compiler_mkNatEq___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_numScalarTypes;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_unFoldFns___closed__1;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__27;
static lean_object* l_Lean_Compiler_natFoldFns___closed__42;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___boxed(lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Compiler_natFoldFns___closed__31;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatLt___closed__10;
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat(lean_object*);
static lean_object* l_Lean_Compiler_foldNatBinBoolPred___closed__2;
static lean_object* l_Lean_Compiler_natFoldFns___closed__5;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__11;
static lean_object* l_Lean_Compiler_mkLcProof___closed__2;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__9;
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__26;
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr(uint8_t, lean_object*, uint8_t);
extern lean_object* l_System_Platform_numBits;
static lean_object* l_Lean_Compiler_natFoldFns___closed__16;
static lean_object* l_Lean_Compiler_mkNatLt___closed__6;
static lean_object* l_Lean_Compiler_natFoldFns___closed__2;
static lean_object* l_Lean_Compiler_natFoldFns___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__41;
static lean_object* l_Lean_Compiler_foldCharOfNat___closed__2;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__20;
static lean_object* l_Lean_Compiler_natFoldFns___closed__44;
static lean_object* l_Lean_Compiler_mkNatLe___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt(uint8_t);
static lean_object* l_Lean_Compiler_natFoldFns___closed__24;
static lean_object* l_Lean_Compiler_natFoldFns___closed__12;
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_fold_un_op(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___boxed(lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__51;
static lean_object* l_Lean_Compiler_unFoldFns___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default(lean_object*);
static lean_object* l_Lean_Compiler_mkNatLe___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_uintFoldToNatFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldNatDecLe___closed__2;
LEAN_EXPORT lean_object* lean_get_num_lit(lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatEq___closed__2;
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__33;
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_boolFoldFns___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Compiler_uintBinFoldFns___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal(lean_object*);
static lean_object* l_Lean_Compiler_boolFoldFns___closed__1;
static lean_object* l_Lean_Compiler_foldNatAdd___rarg___closed__1;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__1;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinBoolPred(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_boolFoldFns___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_natPowThreshold;
static lean_object* l_Lean_Compiler_natFoldFns___closed__39;
static lean_object* l_Lean_Compiler_getBoolLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_binFoldFns;
static lean_object* l_Lean_Compiler_natFoldFns___closed__49;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__8;
static lean_object* l_Lean_Compiler_natFoldFns___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn___boxed(lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__9;
static lean_object* l_Lean_Compiler_foldUIntDiv___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Nat_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatEq___closed__7;
static lean_object* l_Lean_Compiler_mkNatLt___closed__9;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__38;
static lean_object* l_Lean_Compiler_unFoldFns___closed__5;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___boxed(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_id___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit___boxed(lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__10;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_boolFoldFns___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___rarg(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatEq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___boxed(lean_object*);
static lean_object* l_Lean_Compiler_binFoldFns___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__3;
static lean_object* l_Lean_Compiler_mkNatLe___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit(lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__20;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldNatDecEq___closed__1;
static lean_object* l_Lean_Compiler_foldNatDecLt___closed__2;
extern lean_object* l_Lean_levelOne;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__7;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___boxed(lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__21;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__21;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___rarg(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Compiler_unFoldFns___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcProof___closed__1;
static lean_object* l_Lean_Compiler_natFoldFns___closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat(uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__7;
static lean_object* l_Lean_Compiler_mkNatEq___closed__6;
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___boxed(lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__13;
static lean_object* l_Lean_Compiler_natFoldFns___closed__27;
static lean_object* l_Lean_Compiler_natFoldFns___closed__25;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUnOp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default(lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__16;
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__3;
static lean_object* l_Lean_Compiler_foldCharOfNat___closed__1;
static lean_object* l_Lean_Compiler_mkNatLt___closed__7;
static lean_object* l_Lean_Compiler_natFoldFns___closed__48;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__14;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__2;
static lean_object* l_Lean_Compiler_natFoldFns___closed__22;
static lean_object* l_Lean_Compiler_mkNatLt___closed__8;
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__5;
static lean_object* l_Lean_Compiler_mkNatEq___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_unFoldFns;
static lean_object* l_Lean_Compiler_natFoldFns___closed__30;
static lean_object* l_Lean_Compiler_numScalarTypes___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_natFoldFns___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntTypeName(lean_object*);
static lean_object* l_Lean_Compiler_foldUIntMod___closed__1;
static lean_object* l_Lean_Compiler_mkNatLt___closed__3;
static lean_object* l_Lean_Compiler_natFoldFns___closed__45;
static lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__23;
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default(lean_object*);
static lean_object* l_Lean_Compiler_unFoldFns___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkNatLt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mod___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldUIntMul___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Compiler_numScalarTypes___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getBoolLit___closed__2;
static lean_object* l_Lean_Compiler_toDecidableExpr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_foldNatMul___rarg___closed__1;
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcProof", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcProof___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcProof___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkLcProof___closed__3;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkUIntTypeName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UInt", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntTypeName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_Compiler_mkUIntTypeName___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l_Lean_Name_str___override(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_id___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toNat", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_NumScalarTypeInfo_size___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__1;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__1;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__1;
x_3 = l_Lean_Compiler_numScalarTypes___closed__2;
x_4 = l_Lean_Compiler_numScalarTypes___closed__3;
x_5 = lean_unsigned_to_nat(256u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__5;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__5;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__5;
x_3 = l_Lean_Compiler_numScalarTypes___closed__6;
x_4 = l_Lean_Compiler_numScalarTypes___closed__7;
x_5 = lean_unsigned_to_nat(65536u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__9;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__9;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__9;
x_3 = l_Lean_Compiler_numScalarTypes___closed__10;
x_4 = l_Lean_Compiler_numScalarTypes___closed__11;
x_5 = lean_cstr_to_nat("4294967296");
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__13;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__13;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__13;
x_3 = l_Lean_Compiler_numScalarTypes___closed__14;
x_4 = l_Lean_Compiler_numScalarTypes___closed__15;
x_5 = l_Lean_Compiler_numScalarTypes___closed__16;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("USize", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__19;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__19;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_System_Platform_numBits;
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_System_Platform_numBits;
x_2 = l_Lean_Compiler_numScalarTypes___closed__19;
x_3 = l_Lean_Compiler_numScalarTypes___closed__20;
x_4 = l_Lean_Compiler_numScalarTypes___closed__21;
x_5 = l_Lean_Compiler_numScalarTypes___closed__22;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__17;
x_2 = l_Lean_Compiler_numScalarTypes___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__12;
x_2 = l_Lean_Compiler_numScalarTypes___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__8;
x_2 = l_Lean_Compiler_numScalarTypes___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__4;
x_2 = l_Lean_Compiler_numScalarTypes___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__28;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_isOfNat___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_List_any___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_isOfNat___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isOfNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_isToNat___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_List_any___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_isToNat___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isToNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_name_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getInfoFromFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Compiler_numScalarTypes;
x_5 = l_Lean_Compiler_getInfoFromFn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_getInfoFromVal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_get_num_lit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_isOfNat(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
case 9:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
default: 
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_mod(x_2, x_6);
lean_dec(x_6);
x_8 = l_Lean_mkRawNatLit(x_7);
x_9 = l_Lean_Expr_app___override(x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_mkUIntLit(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_numScalarTypes___closed__12;
x_3 = l_Lean_Compiler_mkUIntLit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_mkUInt32Lit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_get_num_lit(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_getInfoFromVal(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_box(x_2);
lean_inc(x_14);
x_16 = lean_apply_4(x_1, x_14, x_15, x_7, x_10);
x_17 = l_Lean_Compiler_mkUIntLit(x_14, x_16);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(x_2);
lean_inc(x_18);
x_20 = lean_apply_4(x_1, x_18, x_19, x_7, x_10);
x_21 = l_Lean_Compiler_mkUIntLit(x_18, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldBinUInt(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_add(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntAdd___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntAdd___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntAdd___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntAdd(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mul(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMul___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntMul___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntMul___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntMul(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_div(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntDiv___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntDiv___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntDiv___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntDiv(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mod(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMod___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntMod___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntMod___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntMod(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntSub___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntSub___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntSub___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntSub(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("add", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntAdd___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__2;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mul", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMul___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__6;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("div", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntDiv___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__10;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mod", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMod___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__14;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sub", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntSub___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__18;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__16;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__12;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__8;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__4;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__25;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Compiler_uintBinFoldFns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_Name_append(x_10, x_9);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = l_Lean_Name_append(x_16, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_18);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = l_Lean_Name_append(x_25, x_22);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_21;
x_3 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l_Lean_Compiler_preUIntBinFoldFns;
x_7 = l_List_mapTR_loop___at_Lean_Compiler_uintBinFoldFns___spec__1(x_3, x_6, x_5);
x_8 = l_List_appendTR___rarg(x_1, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_uintBinFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinOp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = l_Lean_mkRawNatLit(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_apply_2(x_1, x_6, x_13);
x_15 = l_Lean_mkRawNatLit(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_foldNatAdd___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_add___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatAdd___rarg___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatAdd___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatAdd(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatMul___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatMul___rarg___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMul___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatMul(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDiv___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatDiv___rarg___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDiv___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatDiv(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatMod___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mod___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatMod___rarg___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMod___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatMod(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natPowThreshold() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Compiler_natPowThreshold;
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_pow(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Lean_mkRawNatLit(x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_Compiler_natPowThreshold;
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_5);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_nat_pow(x_5, x_15);
lean_dec(x_15);
lean_dec(x_5);
x_20 = l_Lean_mkRawNatLit(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatPow___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatPow(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__2;
x_2 = l_Lean_Compiler_mkNatEq___closed__3;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatEq___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatEq___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__8;
x_2 = l_Lean_Compiler_mkNatEq___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_mkNatEq___closed__9;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Compiler_mkNatEq___closed__4;
x_7 = l_Lean_mkAppN(x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LT", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__1;
x_2 = l_Lean_Compiler_mkNatLt___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__3;
x_2 = l_Lean_Compiler_mkNatLt___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_mkNatLt___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatLt___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__8;
x_2 = l_Lean_Compiler_mkNatEq___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__9;
x_2 = l_Lean_Compiler_mkNatLt___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_mkNatLt___closed__10;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Compiler_mkNatLt___closed__5;
x_7 = l_Lean_mkAppN(x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LE", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLe___closed__1;
x_2 = l_Lean_Compiler_mkNatLe___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLe___closed__3;
x_2 = l_Lean_Compiler_mkNatLt___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_mkNatLe___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatLe___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__9;
x_2 = l_Lean_Compiler_mkNatLe___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_mkNatLe___closed__7;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Compiler_mkNatLe___closed__4;
x_7 = l_Lean_mkAppN(x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_toDecidableExpr___closed__1;
x_2 = l_Lean_Compiler_toDecidableExpr___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_toDecidableExpr___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_toDecidableExpr___closed__1;
x_2 = l_Lean_Compiler_toDecidableExpr___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_toDecidableExpr___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_toDecidableExpr___closed__4;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_toDecidableExpr___closed__7;
return x_5;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = l_Lean_Compiler_mkLcProof(x_2);
x_7 = l_Lean_mkDecIsFalse(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_8 = l_Lean_Compiler_mkLcProof(x_2);
x_9 = l_Lean_mkDecIsTrue(x_2, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Compiler_toDecidableExpr(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_get_num_lit(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_5);
x_9 = lean_get_num_lit(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_apply_2(x_1, x_4, x_5);
x_14 = lean_apply_2(x_2, x_8, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Lean_Compiler_toDecidableExpr(x_3, x_13, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_apply_2(x_1, x_4, x_5);
x_19 = lean_apply_2(x_2, x_8, x_17);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l_Lean_Compiler_toDecidableExpr(x_3, x_18, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Compiler_foldNatBinPred(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatEq), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_foldNatDecEq___closed__1;
x_5 = l_Lean_Compiler_foldNatDecEq___closed__2;
x_6 = l_Lean_Compiler_foldNatBinPred(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecEq(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatLt), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_foldNatDecLt___closed__1;
x_5 = l_Lean_Compiler_foldNatDecLt___closed__2;
x_6 = l_Lean_Compiler_foldNatBinPred(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecLt(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatLe), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLe___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_foldNatDecLe___closed__1;
x_5 = l_Lean_Compiler_foldNatDecLe___closed__2;
x_6 = l_Lean_Compiler_foldNatBinPred(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecLe(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatBinBoolPred___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_toDecidableExpr___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatBinBoolPred___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_toDecidableExpr___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_2(x_1, x_6, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_foldNatBinBoolPred___closed__1;
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_foldNatBinBoolPred___closed__2;
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_foldNatBeq___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatBeq___rarg___closed__1;
x_4 = l_Lean_Compiler_foldNatBinBoolPred(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBeq___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatBeq(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatDecLt___closed__2;
x_4 = l_Lean_Compiler_foldNatBinBoolPred(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBle___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatBle(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatDecLe___closed__2;
x_4 = l_Lean_Compiler_foldNatBinBoolPred(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBlt___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatBlt(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatAdd___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__1;
x_2 = l_Lean_Compiler_natFoldFns___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMul___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__4;
x_2 = l_Lean_Compiler_natFoldFns___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDiv___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__7;
x_2 = l_Lean_Compiler_natFoldFns___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__13;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMod___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__10;
x_2 = l_Lean_Compiler_natFoldFns___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pow", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__13;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatPow___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__14;
x_2 = l_Lean_Compiler_natFoldFns___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decEq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecEq___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__18;
x_2 = l_Lean_Compiler_natFoldFns___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decLt", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__21;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLt___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__22;
x_2 = l_Lean_Compiler_natFoldFns___closed__23;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decLe", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__25;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLe___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__26;
x_2 = l_Lean_Compiler_natFoldFns___closed__27;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("beq", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__29;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBeq___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__30;
x_2 = l_Lean_Compiler_natFoldFns___closed__31;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("blt", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__33;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBlt___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__34;
x_2 = l_Lean_Compiler_natFoldFns___closed__35;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ble", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_natFoldFns___closed__37;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBle___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__38;
x_2 = l_Lean_Compiler_natFoldFns___closed__39;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_natFoldFns___closed__40;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__36;
x_2 = l_Lean_Compiler_natFoldFns___closed__41;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__32;
x_2 = l_Lean_Compiler_natFoldFns___closed__42;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__28;
x_2 = l_Lean_Compiler_natFoldFns___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__24;
x_2 = l_Lean_Compiler_natFoldFns___closed__44;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__20;
x_2 = l_Lean_Compiler_natFoldFns___closed__45;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__16;
x_2 = l_Lean_Compiler_natFoldFns___closed__46;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__12;
x_2 = l_Lean_Compiler_natFoldFns___closed__47;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__9;
x_2 = l_Lean_Compiler_natFoldFns___closed__48;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__6;
x_2 = l_Lean_Compiler_natFoldFns___closed__49;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__3;
x_2 = l_Lean_Compiler_natFoldFns___closed__50;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_natFoldFns___closed__51;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_getBoolLit___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_getBoolLit___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Compiler_toDecidableExpr___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Compiler_toDecidableExpr___closed__5;
x_11 = lean_string_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_toDecidableExpr___closed__2;
x_13 = lean_string_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_getBoolLit___closed__1;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_getBoolLit___closed__2;
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_getBoolLit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getBoolLit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_getBoolLit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
}
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictAnd___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldStrictAnd(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getBoolLit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_getBoolLit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictOr___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldStrictOr(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("strictOr", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_boolFoldFns___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictOr___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__2;
x_2 = l_Lean_Compiler_boolFoldFns___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("strictAnd", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_boolFoldFns___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictAnd___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__6;
x_2 = l_Lean_Compiler_boolFoldFns___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_boolFoldFns___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__4;
x_2 = l_Lean_Compiler_boolFoldFns___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns;
x_2 = l_Lean_Compiler_uintBinFoldFns;
x_3 = l_List_appendTR___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_binFoldFns___closed__1;
x_2 = l_Lean_Compiler_natFoldFns;
x_3 = l_List_appendTR___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_binFoldFns___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_mkRawNatLit(x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_mkRawNatLit(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatSucc___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatSucc(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_foldCharOfNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_mkUInt32Lit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_foldCharOfNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_foldCharOfNat___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_uint32_of_nat(x_6);
x_8 = 55296;
x_9 = lean_uint32_dec_lt(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 57343;
x_11 = lean_uint32_dec_lt(x_10, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_3);
lean_dec(x_6);
x_12 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 1114112;
x_14 = lean_uint32_dec_lt(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_3);
lean_dec(x_6);
x_15 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_mkUInt32Lit(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_mkUInt32Lit(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; uint32_t x_19; uint32_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_uint32_of_nat(x_18);
x_20 = 55296;
x_21 = lean_uint32_dec_lt(x_19, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 57343;
x_23 = lean_uint32_dec_lt(x_22, x_19);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
x_24 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_24;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 1114112;
x_26 = lean_uint32_dec_lt(x_19, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_18);
x_27 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Compiler_mkUInt32Lit(x_18);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Compiler_mkUInt32Lit(x_18);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_2);
x_32 = lean_box(0);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_foldCharOfNat(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_mkRawNatLit(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_mkRawNatLit(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldToNat___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldToNat(x_2);
return x_3;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldToNat___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_8);
x_1 = x_2;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_uintFoldToNatFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__5;
x_2 = l_Lean_Compiler_unFoldFns___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatSucc___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__2;
x_2 = l_Lean_Compiler_unFoldFns___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Char", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__5;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldCharOfNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__6;
x_2 = l_Lean_Compiler_unFoldFns___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_unFoldFns___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__4;
x_2 = l_Lean_Compiler_unFoldFns___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__10;
x_2 = l_Lean_Compiler_uintFoldToNatFns;
x_3 = l_List_appendTR___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_unFoldFns___closed__11;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_binFoldFns;
x_3 = l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_findBinFoldFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_unFoldFns;
x_3 = l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_findUnFoldFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_fold_bin_op(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Compiler_binFoldFns;
x_7 = l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(x_5, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(x_1);
x_11 = lean_apply_3(x_9, x_10, x_3, x_4);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_fold_bin_op(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_fold_un_op(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_unFoldFns;
x_6 = l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(x_4, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(x_1);
x_10 = lean_apply_2(x_8, x_9, x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUnOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_fold_un_op(x_4, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ConstFolding(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_mkLcProof___closed__1 = _init_l_Lean_Compiler_mkLcProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__1);
l_Lean_Compiler_mkLcProof___closed__2 = _init_l_Lean_Compiler_mkLcProof___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__2);
l_Lean_Compiler_mkLcProof___closed__3 = _init_l_Lean_Compiler_mkLcProof___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkLcProof___closed__3);
l_Lean_Compiler_mkUIntTypeName___closed__1 = _init_l_Lean_Compiler_mkUIntTypeName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkUIntTypeName___closed__1);
l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1 = _init_l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default___closed__1);
l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1 = _init_l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1);
l_Lean_Compiler_numScalarTypes___closed__1 = _init_l_Lean_Compiler_numScalarTypes___closed__1();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__1);
l_Lean_Compiler_numScalarTypes___closed__2 = _init_l_Lean_Compiler_numScalarTypes___closed__2();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__2);
l_Lean_Compiler_numScalarTypes___closed__3 = _init_l_Lean_Compiler_numScalarTypes___closed__3();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__3);
l_Lean_Compiler_numScalarTypes___closed__4 = _init_l_Lean_Compiler_numScalarTypes___closed__4();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__4);
l_Lean_Compiler_numScalarTypes___closed__5 = _init_l_Lean_Compiler_numScalarTypes___closed__5();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__5);
l_Lean_Compiler_numScalarTypes___closed__6 = _init_l_Lean_Compiler_numScalarTypes___closed__6();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__6);
l_Lean_Compiler_numScalarTypes___closed__7 = _init_l_Lean_Compiler_numScalarTypes___closed__7();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__7);
l_Lean_Compiler_numScalarTypes___closed__8 = _init_l_Lean_Compiler_numScalarTypes___closed__8();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__8);
l_Lean_Compiler_numScalarTypes___closed__9 = _init_l_Lean_Compiler_numScalarTypes___closed__9();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__9);
l_Lean_Compiler_numScalarTypes___closed__10 = _init_l_Lean_Compiler_numScalarTypes___closed__10();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__10);
l_Lean_Compiler_numScalarTypes___closed__11 = _init_l_Lean_Compiler_numScalarTypes___closed__11();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__11);
l_Lean_Compiler_numScalarTypes___closed__12 = _init_l_Lean_Compiler_numScalarTypes___closed__12();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__12);
l_Lean_Compiler_numScalarTypes___closed__13 = _init_l_Lean_Compiler_numScalarTypes___closed__13();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__13);
l_Lean_Compiler_numScalarTypes___closed__14 = _init_l_Lean_Compiler_numScalarTypes___closed__14();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__14);
l_Lean_Compiler_numScalarTypes___closed__15 = _init_l_Lean_Compiler_numScalarTypes___closed__15();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__15);
l_Lean_Compiler_numScalarTypes___closed__16 = _init_l_Lean_Compiler_numScalarTypes___closed__16();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__16);
l_Lean_Compiler_numScalarTypes___closed__17 = _init_l_Lean_Compiler_numScalarTypes___closed__17();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__17);
l_Lean_Compiler_numScalarTypes___closed__18 = _init_l_Lean_Compiler_numScalarTypes___closed__18();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__18);
l_Lean_Compiler_numScalarTypes___closed__19 = _init_l_Lean_Compiler_numScalarTypes___closed__19();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__19);
l_Lean_Compiler_numScalarTypes___closed__20 = _init_l_Lean_Compiler_numScalarTypes___closed__20();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__20);
l_Lean_Compiler_numScalarTypes___closed__21 = _init_l_Lean_Compiler_numScalarTypes___closed__21();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__21);
l_Lean_Compiler_numScalarTypes___closed__22 = _init_l_Lean_Compiler_numScalarTypes___closed__22();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__22);
l_Lean_Compiler_numScalarTypes___closed__23 = _init_l_Lean_Compiler_numScalarTypes___closed__23();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__23);
l_Lean_Compiler_numScalarTypes___closed__24 = _init_l_Lean_Compiler_numScalarTypes___closed__24();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__24);
l_Lean_Compiler_numScalarTypes___closed__25 = _init_l_Lean_Compiler_numScalarTypes___closed__25();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__25);
l_Lean_Compiler_numScalarTypes___closed__26 = _init_l_Lean_Compiler_numScalarTypes___closed__26();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__26);
l_Lean_Compiler_numScalarTypes___closed__27 = _init_l_Lean_Compiler_numScalarTypes___closed__27();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__27);
l_Lean_Compiler_numScalarTypes___closed__28 = _init_l_Lean_Compiler_numScalarTypes___closed__28();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__28);
l_Lean_Compiler_numScalarTypes = _init_l_Lean_Compiler_numScalarTypes();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes);
l_Lean_Compiler_foldUIntAdd___closed__1 = _init_l_Lean_Compiler_foldUIntAdd___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntAdd___closed__1);
l_Lean_Compiler_foldUIntMul___closed__1 = _init_l_Lean_Compiler_foldUIntMul___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntMul___closed__1);
l_Lean_Compiler_foldUIntDiv___closed__1 = _init_l_Lean_Compiler_foldUIntDiv___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntDiv___closed__1);
l_Lean_Compiler_foldUIntMod___closed__1 = _init_l_Lean_Compiler_foldUIntMod___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntMod___closed__1);
l_Lean_Compiler_foldUIntSub___closed__1 = _init_l_Lean_Compiler_foldUIntSub___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntSub___closed__1);
l_Lean_Compiler_preUIntBinFoldFns___closed__1 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__1);
l_Lean_Compiler_preUIntBinFoldFns___closed__2 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__2);
l_Lean_Compiler_preUIntBinFoldFns___closed__3 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__3);
l_Lean_Compiler_preUIntBinFoldFns___closed__4 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__4);
l_Lean_Compiler_preUIntBinFoldFns___closed__5 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__5);
l_Lean_Compiler_preUIntBinFoldFns___closed__6 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__6);
l_Lean_Compiler_preUIntBinFoldFns___closed__7 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__7);
l_Lean_Compiler_preUIntBinFoldFns___closed__8 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__8);
l_Lean_Compiler_preUIntBinFoldFns___closed__9 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__9);
l_Lean_Compiler_preUIntBinFoldFns___closed__10 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__10);
l_Lean_Compiler_preUIntBinFoldFns___closed__11 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__11();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__11);
l_Lean_Compiler_preUIntBinFoldFns___closed__12 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__12();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__12);
l_Lean_Compiler_preUIntBinFoldFns___closed__13 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__13();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__13);
l_Lean_Compiler_preUIntBinFoldFns___closed__14 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__14();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__14);
l_Lean_Compiler_preUIntBinFoldFns___closed__15 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__15();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__15);
l_Lean_Compiler_preUIntBinFoldFns___closed__16 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__16();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__16);
l_Lean_Compiler_preUIntBinFoldFns___closed__17 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__17();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__17);
l_Lean_Compiler_preUIntBinFoldFns___closed__18 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__18();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__18);
l_Lean_Compiler_preUIntBinFoldFns___closed__19 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__19();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__19);
l_Lean_Compiler_preUIntBinFoldFns___closed__20 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__20();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__20);
l_Lean_Compiler_preUIntBinFoldFns___closed__21 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__21();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__21);
l_Lean_Compiler_preUIntBinFoldFns___closed__22 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__22();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__22);
l_Lean_Compiler_preUIntBinFoldFns___closed__23 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__23();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__23);
l_Lean_Compiler_preUIntBinFoldFns___closed__24 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__24();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__24);
l_Lean_Compiler_preUIntBinFoldFns___closed__25 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__25();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__25);
l_Lean_Compiler_preUIntBinFoldFns = _init_l_Lean_Compiler_preUIntBinFoldFns();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns);
l_Lean_Compiler_uintBinFoldFns = _init_l_Lean_Compiler_uintBinFoldFns();
lean_mark_persistent(l_Lean_Compiler_uintBinFoldFns);
l_Lean_Compiler_foldNatAdd___rarg___closed__1 = _init_l_Lean_Compiler_foldNatAdd___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatAdd___rarg___closed__1);
l_Lean_Compiler_foldNatMul___rarg___closed__1 = _init_l_Lean_Compiler_foldNatMul___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatMul___rarg___closed__1);
l_Lean_Compiler_foldNatDiv___rarg___closed__1 = _init_l_Lean_Compiler_foldNatDiv___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDiv___rarg___closed__1);
l_Lean_Compiler_foldNatMod___rarg___closed__1 = _init_l_Lean_Compiler_foldNatMod___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatMod___rarg___closed__1);
l_Lean_Compiler_natPowThreshold = _init_l_Lean_Compiler_natPowThreshold();
lean_mark_persistent(l_Lean_Compiler_natPowThreshold);
l_Lean_Compiler_mkNatEq___closed__1 = _init_l_Lean_Compiler_mkNatEq___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__1);
l_Lean_Compiler_mkNatEq___closed__2 = _init_l_Lean_Compiler_mkNatEq___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__2);
l_Lean_Compiler_mkNatEq___closed__3 = _init_l_Lean_Compiler_mkNatEq___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__3);
l_Lean_Compiler_mkNatEq___closed__4 = _init_l_Lean_Compiler_mkNatEq___closed__4();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__4);
l_Lean_Compiler_mkNatEq___closed__5 = _init_l_Lean_Compiler_mkNatEq___closed__5();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__5);
l_Lean_Compiler_mkNatEq___closed__6 = _init_l_Lean_Compiler_mkNatEq___closed__6();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__6);
l_Lean_Compiler_mkNatEq___closed__7 = _init_l_Lean_Compiler_mkNatEq___closed__7();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__7);
l_Lean_Compiler_mkNatEq___closed__8 = _init_l_Lean_Compiler_mkNatEq___closed__8();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__8);
l_Lean_Compiler_mkNatEq___closed__9 = _init_l_Lean_Compiler_mkNatEq___closed__9();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__9);
l_Lean_Compiler_mkNatLt___closed__1 = _init_l_Lean_Compiler_mkNatLt___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__1);
l_Lean_Compiler_mkNatLt___closed__2 = _init_l_Lean_Compiler_mkNatLt___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__2);
l_Lean_Compiler_mkNatLt___closed__3 = _init_l_Lean_Compiler_mkNatLt___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__3);
l_Lean_Compiler_mkNatLt___closed__4 = _init_l_Lean_Compiler_mkNatLt___closed__4();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__4);
l_Lean_Compiler_mkNatLt___closed__5 = _init_l_Lean_Compiler_mkNatLt___closed__5();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__5);
l_Lean_Compiler_mkNatLt___closed__6 = _init_l_Lean_Compiler_mkNatLt___closed__6();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__6);
l_Lean_Compiler_mkNatLt___closed__7 = _init_l_Lean_Compiler_mkNatLt___closed__7();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__7);
l_Lean_Compiler_mkNatLt___closed__8 = _init_l_Lean_Compiler_mkNatLt___closed__8();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__8);
l_Lean_Compiler_mkNatLt___closed__9 = _init_l_Lean_Compiler_mkNatLt___closed__9();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__9);
l_Lean_Compiler_mkNatLt___closed__10 = _init_l_Lean_Compiler_mkNatLt___closed__10();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__10);
l_Lean_Compiler_mkNatLe___closed__1 = _init_l_Lean_Compiler_mkNatLe___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__1);
l_Lean_Compiler_mkNatLe___closed__2 = _init_l_Lean_Compiler_mkNatLe___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__2);
l_Lean_Compiler_mkNatLe___closed__3 = _init_l_Lean_Compiler_mkNatLe___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__3);
l_Lean_Compiler_mkNatLe___closed__4 = _init_l_Lean_Compiler_mkNatLe___closed__4();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__4);
l_Lean_Compiler_mkNatLe___closed__5 = _init_l_Lean_Compiler_mkNatLe___closed__5();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__5);
l_Lean_Compiler_mkNatLe___closed__6 = _init_l_Lean_Compiler_mkNatLe___closed__6();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__6);
l_Lean_Compiler_mkNatLe___closed__7 = _init_l_Lean_Compiler_mkNatLe___closed__7();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__7);
l_Lean_Compiler_toDecidableExpr___closed__1 = _init_l_Lean_Compiler_toDecidableExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__1);
l_Lean_Compiler_toDecidableExpr___closed__2 = _init_l_Lean_Compiler_toDecidableExpr___closed__2();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__2);
l_Lean_Compiler_toDecidableExpr___closed__3 = _init_l_Lean_Compiler_toDecidableExpr___closed__3();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__3);
l_Lean_Compiler_toDecidableExpr___closed__4 = _init_l_Lean_Compiler_toDecidableExpr___closed__4();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__4);
l_Lean_Compiler_toDecidableExpr___closed__5 = _init_l_Lean_Compiler_toDecidableExpr___closed__5();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__5);
l_Lean_Compiler_toDecidableExpr___closed__6 = _init_l_Lean_Compiler_toDecidableExpr___closed__6();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__6);
l_Lean_Compiler_toDecidableExpr___closed__7 = _init_l_Lean_Compiler_toDecidableExpr___closed__7();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__7);
l_Lean_Compiler_foldNatDecEq___closed__1 = _init_l_Lean_Compiler_foldNatDecEq___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDecEq___closed__1);
l_Lean_Compiler_foldNatDecEq___closed__2 = _init_l_Lean_Compiler_foldNatDecEq___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldNatDecEq___closed__2);
l_Lean_Compiler_foldNatDecLt___closed__1 = _init_l_Lean_Compiler_foldNatDecLt___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLt___closed__1);
l_Lean_Compiler_foldNatDecLt___closed__2 = _init_l_Lean_Compiler_foldNatDecLt___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLt___closed__2);
l_Lean_Compiler_foldNatDecLe___closed__1 = _init_l_Lean_Compiler_foldNatDecLe___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLe___closed__1);
l_Lean_Compiler_foldNatDecLe___closed__2 = _init_l_Lean_Compiler_foldNatDecLe___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLe___closed__2);
l_Lean_Compiler_foldNatBinBoolPred___closed__1 = _init_l_Lean_Compiler_foldNatBinBoolPred___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatBinBoolPred___closed__1);
l_Lean_Compiler_foldNatBinBoolPred___closed__2 = _init_l_Lean_Compiler_foldNatBinBoolPred___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldNatBinBoolPred___closed__2);
l_Lean_Compiler_foldNatBeq___rarg___closed__1 = _init_l_Lean_Compiler_foldNatBeq___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatBeq___rarg___closed__1);
l_Lean_Compiler_natFoldFns___closed__1 = _init_l_Lean_Compiler_natFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__1);
l_Lean_Compiler_natFoldFns___closed__2 = _init_l_Lean_Compiler_natFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__2);
l_Lean_Compiler_natFoldFns___closed__3 = _init_l_Lean_Compiler_natFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__3);
l_Lean_Compiler_natFoldFns___closed__4 = _init_l_Lean_Compiler_natFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__4);
l_Lean_Compiler_natFoldFns___closed__5 = _init_l_Lean_Compiler_natFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__5);
l_Lean_Compiler_natFoldFns___closed__6 = _init_l_Lean_Compiler_natFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__6);
l_Lean_Compiler_natFoldFns___closed__7 = _init_l_Lean_Compiler_natFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__7);
l_Lean_Compiler_natFoldFns___closed__8 = _init_l_Lean_Compiler_natFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__8);
l_Lean_Compiler_natFoldFns___closed__9 = _init_l_Lean_Compiler_natFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__9);
l_Lean_Compiler_natFoldFns___closed__10 = _init_l_Lean_Compiler_natFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__10);
l_Lean_Compiler_natFoldFns___closed__11 = _init_l_Lean_Compiler_natFoldFns___closed__11();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__11);
l_Lean_Compiler_natFoldFns___closed__12 = _init_l_Lean_Compiler_natFoldFns___closed__12();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__12);
l_Lean_Compiler_natFoldFns___closed__13 = _init_l_Lean_Compiler_natFoldFns___closed__13();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__13);
l_Lean_Compiler_natFoldFns___closed__14 = _init_l_Lean_Compiler_natFoldFns___closed__14();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__14);
l_Lean_Compiler_natFoldFns___closed__15 = _init_l_Lean_Compiler_natFoldFns___closed__15();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__15);
l_Lean_Compiler_natFoldFns___closed__16 = _init_l_Lean_Compiler_natFoldFns___closed__16();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__16);
l_Lean_Compiler_natFoldFns___closed__17 = _init_l_Lean_Compiler_natFoldFns___closed__17();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__17);
l_Lean_Compiler_natFoldFns___closed__18 = _init_l_Lean_Compiler_natFoldFns___closed__18();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__18);
l_Lean_Compiler_natFoldFns___closed__19 = _init_l_Lean_Compiler_natFoldFns___closed__19();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__19);
l_Lean_Compiler_natFoldFns___closed__20 = _init_l_Lean_Compiler_natFoldFns___closed__20();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__20);
l_Lean_Compiler_natFoldFns___closed__21 = _init_l_Lean_Compiler_natFoldFns___closed__21();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__21);
l_Lean_Compiler_natFoldFns___closed__22 = _init_l_Lean_Compiler_natFoldFns___closed__22();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__22);
l_Lean_Compiler_natFoldFns___closed__23 = _init_l_Lean_Compiler_natFoldFns___closed__23();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__23);
l_Lean_Compiler_natFoldFns___closed__24 = _init_l_Lean_Compiler_natFoldFns___closed__24();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__24);
l_Lean_Compiler_natFoldFns___closed__25 = _init_l_Lean_Compiler_natFoldFns___closed__25();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__25);
l_Lean_Compiler_natFoldFns___closed__26 = _init_l_Lean_Compiler_natFoldFns___closed__26();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__26);
l_Lean_Compiler_natFoldFns___closed__27 = _init_l_Lean_Compiler_natFoldFns___closed__27();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__27);
l_Lean_Compiler_natFoldFns___closed__28 = _init_l_Lean_Compiler_natFoldFns___closed__28();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__28);
l_Lean_Compiler_natFoldFns___closed__29 = _init_l_Lean_Compiler_natFoldFns___closed__29();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__29);
l_Lean_Compiler_natFoldFns___closed__30 = _init_l_Lean_Compiler_natFoldFns___closed__30();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__30);
l_Lean_Compiler_natFoldFns___closed__31 = _init_l_Lean_Compiler_natFoldFns___closed__31();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__31);
l_Lean_Compiler_natFoldFns___closed__32 = _init_l_Lean_Compiler_natFoldFns___closed__32();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__32);
l_Lean_Compiler_natFoldFns___closed__33 = _init_l_Lean_Compiler_natFoldFns___closed__33();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__33);
l_Lean_Compiler_natFoldFns___closed__34 = _init_l_Lean_Compiler_natFoldFns___closed__34();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__34);
l_Lean_Compiler_natFoldFns___closed__35 = _init_l_Lean_Compiler_natFoldFns___closed__35();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__35);
l_Lean_Compiler_natFoldFns___closed__36 = _init_l_Lean_Compiler_natFoldFns___closed__36();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__36);
l_Lean_Compiler_natFoldFns___closed__37 = _init_l_Lean_Compiler_natFoldFns___closed__37();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__37);
l_Lean_Compiler_natFoldFns___closed__38 = _init_l_Lean_Compiler_natFoldFns___closed__38();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__38);
l_Lean_Compiler_natFoldFns___closed__39 = _init_l_Lean_Compiler_natFoldFns___closed__39();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__39);
l_Lean_Compiler_natFoldFns___closed__40 = _init_l_Lean_Compiler_natFoldFns___closed__40();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__40);
l_Lean_Compiler_natFoldFns___closed__41 = _init_l_Lean_Compiler_natFoldFns___closed__41();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__41);
l_Lean_Compiler_natFoldFns___closed__42 = _init_l_Lean_Compiler_natFoldFns___closed__42();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__42);
l_Lean_Compiler_natFoldFns___closed__43 = _init_l_Lean_Compiler_natFoldFns___closed__43();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__43);
l_Lean_Compiler_natFoldFns___closed__44 = _init_l_Lean_Compiler_natFoldFns___closed__44();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__44);
l_Lean_Compiler_natFoldFns___closed__45 = _init_l_Lean_Compiler_natFoldFns___closed__45();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__45);
l_Lean_Compiler_natFoldFns___closed__46 = _init_l_Lean_Compiler_natFoldFns___closed__46();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__46);
l_Lean_Compiler_natFoldFns___closed__47 = _init_l_Lean_Compiler_natFoldFns___closed__47();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__47);
l_Lean_Compiler_natFoldFns___closed__48 = _init_l_Lean_Compiler_natFoldFns___closed__48();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__48);
l_Lean_Compiler_natFoldFns___closed__49 = _init_l_Lean_Compiler_natFoldFns___closed__49();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__49);
l_Lean_Compiler_natFoldFns___closed__50 = _init_l_Lean_Compiler_natFoldFns___closed__50();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__50);
l_Lean_Compiler_natFoldFns___closed__51 = _init_l_Lean_Compiler_natFoldFns___closed__51();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__51);
l_Lean_Compiler_natFoldFns = _init_l_Lean_Compiler_natFoldFns();
lean_mark_persistent(l_Lean_Compiler_natFoldFns);
l_Lean_Compiler_getBoolLit___closed__1 = _init_l_Lean_Compiler_getBoolLit___closed__1();
lean_mark_persistent(l_Lean_Compiler_getBoolLit___closed__1);
l_Lean_Compiler_getBoolLit___closed__2 = _init_l_Lean_Compiler_getBoolLit___closed__2();
lean_mark_persistent(l_Lean_Compiler_getBoolLit___closed__2);
l_Lean_Compiler_boolFoldFns___closed__1 = _init_l_Lean_Compiler_boolFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__1);
l_Lean_Compiler_boolFoldFns___closed__2 = _init_l_Lean_Compiler_boolFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__2);
l_Lean_Compiler_boolFoldFns___closed__3 = _init_l_Lean_Compiler_boolFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__3);
l_Lean_Compiler_boolFoldFns___closed__4 = _init_l_Lean_Compiler_boolFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__4);
l_Lean_Compiler_boolFoldFns___closed__5 = _init_l_Lean_Compiler_boolFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__5);
l_Lean_Compiler_boolFoldFns___closed__6 = _init_l_Lean_Compiler_boolFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__6);
l_Lean_Compiler_boolFoldFns___closed__7 = _init_l_Lean_Compiler_boolFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__7);
l_Lean_Compiler_boolFoldFns___closed__8 = _init_l_Lean_Compiler_boolFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__8);
l_Lean_Compiler_boolFoldFns___closed__9 = _init_l_Lean_Compiler_boolFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__9);
l_Lean_Compiler_boolFoldFns___closed__10 = _init_l_Lean_Compiler_boolFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__10);
l_Lean_Compiler_boolFoldFns = _init_l_Lean_Compiler_boolFoldFns();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns);
l_Lean_Compiler_binFoldFns___closed__1 = _init_l_Lean_Compiler_binFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_binFoldFns___closed__1);
l_Lean_Compiler_binFoldFns___closed__2 = _init_l_Lean_Compiler_binFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_binFoldFns___closed__2);
l_Lean_Compiler_binFoldFns = _init_l_Lean_Compiler_binFoldFns();
lean_mark_persistent(l_Lean_Compiler_binFoldFns);
l_Lean_Compiler_foldCharOfNat___closed__1 = _init_l_Lean_Compiler_foldCharOfNat___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldCharOfNat___closed__1);
l_Lean_Compiler_foldCharOfNat___closed__2 = _init_l_Lean_Compiler_foldCharOfNat___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldCharOfNat___closed__2);
l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1 = _init_l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1);
l_Lean_Compiler_uintFoldToNatFns = _init_l_Lean_Compiler_uintFoldToNatFns();
lean_mark_persistent(l_Lean_Compiler_uintFoldToNatFns);
l_Lean_Compiler_unFoldFns___closed__1 = _init_l_Lean_Compiler_unFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__1);
l_Lean_Compiler_unFoldFns___closed__2 = _init_l_Lean_Compiler_unFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__2);
l_Lean_Compiler_unFoldFns___closed__3 = _init_l_Lean_Compiler_unFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__3);
l_Lean_Compiler_unFoldFns___closed__4 = _init_l_Lean_Compiler_unFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__4);
l_Lean_Compiler_unFoldFns___closed__5 = _init_l_Lean_Compiler_unFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__5);
l_Lean_Compiler_unFoldFns___closed__6 = _init_l_Lean_Compiler_unFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__6);
l_Lean_Compiler_unFoldFns___closed__7 = _init_l_Lean_Compiler_unFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__7);
l_Lean_Compiler_unFoldFns___closed__8 = _init_l_Lean_Compiler_unFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__8);
l_Lean_Compiler_unFoldFns___closed__9 = _init_l_Lean_Compiler_unFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__9);
l_Lean_Compiler_unFoldFns___closed__10 = _init_l_Lean_Compiler_unFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__10);
l_Lean_Compiler_unFoldFns___closed__11 = _init_l_Lean_Compiler_unFoldFns___closed__11();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__11);
l_Lean_Compiler_unFoldFns = _init_l_Lean_Compiler_unFoldFns();
lean_mark_persistent(l_Lean_Compiler_unFoldFns);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

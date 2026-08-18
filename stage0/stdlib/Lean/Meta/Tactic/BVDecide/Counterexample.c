// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Counterexample
// Imports: import Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_noption_none();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_toInt(lean_object*, lean_object*);
size_t lean_isize_of_int(lean_object*);
size_t lean_isize_of_nat(lean_object*);
uint8_t lean_isize_dec_le(size_t, size_t);
lean_object* lean_isize_to_int(size_t);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprISize_mkNat(lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint16_t lean_uint16_of_nat_mk(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint32_t lean_uint32_of_nat_mk(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint64_t lean_uint64_of_nat_mk(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_int8_of_nat(lean_object*);
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
lean_object* lean_int8_to_int(uint8_t);
lean_object* l_Lean_instToExprInt8_mkNat(lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
lean_object* lean_int16_to_int(uint16_t);
lean_object* l_Lean_instToExprInt16_mkNat(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Lean_instToExprInt32_mkNat(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* l_Lean_instToExprInt64_mkNat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6_value;
static const lean_ctor_object l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Tactic.BVDecide.Counterexample"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Meta.Tactic.BVDecide.reconstructCounterExample"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: bitIdx == currentBit\n      "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "_private.Lean.Meta.Tactic.BVDecide.Counterexample.0.Lean.Meta.Tactic.BVDecide.DiagnosisM.diagnose.transformEquation"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 57, 165, 14, 135, 135, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(231, 54, 185, 195, 30, 183, 107, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(44, 210, 78, 221, 232, 52, 28, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 114, 73, 21, 161, 185, 192, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 144, 45, 221, 65, 48, 204, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(95, 106, 42, 185, 61, 138, 17, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(83, 21, 175, 117, 0, 32, 88, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 247, 174, 117, 226, 108, 136, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24_value),LEAN_SCALAR_PTR_LITERAL(121, 35, 113, 77, 117, 41, 40, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toBitVec64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value),LEAN_SCALAR_PTR_LITERAL(51, 79, 88, 119, 92, 132, 69, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toBitVec32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29_value),LEAN_SCALAR_PTR_LITERAL(40, 3, 162, 24, 208, 1, 22, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value),LEAN_SCALAR_PTR_LITERAL(116, 153, 59, 255, 117, 164, 81, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 16, 185, 133, 236, 22, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for USize was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " bits"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(43, 155, 189, 13, 93, 69, 82, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for USize was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for ISize was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(185, 56, 140, 35, 97, 137, 251, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for ISize was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for UInt8 was not 8 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(106, 22, 191, 22, 91, 53, 63, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Value for UInt16 was not 16 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(100, 85, 82, 103, 43, 170, 82, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Value for UInt32 was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(112, 78, 205, 187, 174, 188, 116, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Value for UInt64 was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(8, 204, 85, 89, 36, 115, 101, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Value for Int8 was not 8 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 113, 74, 244, 2, 252, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for Int16 was not 16 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(62, 21, 130, 152, 152, 188, 226, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for Int32 was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(133, 86, 165, 75, 15, 11, 161, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for Int64 was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(24, 152, 19, 102, 101, 167, 71, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\n  - "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "It abstracted the following unsupported expressions as opaque variables:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " derived via "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "The following potentially relevant hypotheses could not be used:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "- "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "The prover found a potentially spurious counterexample:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Consider the following assignment:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "The prover found a counterexample, consider the following assignment:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(lean_object* v_msg_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___f_11_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0));
v___f_12_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1));
v___f_13_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2));
v___f_14_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3));
v___f_15_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4));
v___f_16_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5));
v___f_17_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6));
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___f_11_);
lean_ctor_set(v___x_18_, 1, v___f_12_);
v___x_19_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___f_13_);
lean_ctor_set(v___x_19_, 2, v___f_14_);
lean_ctor_set(v___x_19_, 3, v___f_15_);
lean_ctor_set(v___x_19_, 4, v___f_16_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___f_17_);
v___x_21_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7));
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
v___x_23_ = l_instInhabitedOfMonad___redArg(v___x_20_, v___x_22_);
v___x_24_ = lean_panic_fn_borrowed(v___x_23_, v_msg_10_);
lean_dec(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(lean_object* v_b_25_, lean_object* v_acc_26_, lean_object* v_i_27_){
_start:
{
lean_object* v_keyArray_32_; lean_object* v_valueArray_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_keyArray_32_ = lean_ctor_get(v_b_25_, 1);
v_valueArray_33_ = lean_ctor_get(v_b_25_, 2);
v___x_34_ = lean_array_get_size(v_keyArray_32_);
v___x_35_ = lean_nat_dec_lt(v_i_27_, v___x_34_);
if (v___x_35_ == 0)
{
lean_dec(v_i_27_);
return v_acc_26_;
}
else
{
lean_object* v___x_36_; uint8_t v_isSome_37_; 
v___x_36_ = lean_array_fget_borrowed(v_keyArray_32_, v_i_27_);
v_isSome_37_ = lean_noption_is_some(v___x_36_);
if (v_isSome_37_ == 0)
{
goto v___jp_28_;
}
else
{
lean_object* v___x_38_; uint8_t v_isSome_39_; 
v___x_38_ = lean_array_fget_borrowed(v_valueArray_33_, v_i_27_);
v_isSome_39_ = lean_noption_is_some(v___x_38_);
if (v_isSome_39_ == 0)
{
goto v___jp_28_;
}
else
{
lean_object* v_val_40_; lean_object* v_val_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
lean_inc(v___x_36_);
v_val_40_ = lean_noption_get(v___x_36_);
lean_inc(v___x_38_);
v_val_41_ = lean_noption_get(v___x_38_);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v_val_40_);
lean_ctor_set(v___x_42_, 1, v_val_41_);
v___x_43_ = lean_array_push(v_acc_26_, v___x_42_);
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_i_27_, v___x_44_);
lean_dec(v_i_27_);
v_acc_26_ = v___x_43_;
v_i_27_ = v___x_45_;
goto _start;
}
}
}
v___jp_28_:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_add(v_i_27_, v___x_29_);
lean_dec(v_i_27_);
v_i_27_ = v___x_30_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17___boxed(lean_object* v_b_47_, lean_object* v_acc_48_, lean_object* v_i_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_b_47_, v_acc_48_, v_i_49_);
lean_dec_ref(v_b_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object* v_init_51_, lean_object* v_b_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_b_52_, v_init_51_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object* v_init_55_, lean_object* v_b_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_init_55_, v_b_56_);
lean_dec_ref(v_b_56_);
return v_res_57_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2___closed__0(void){
_start:
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = 0;
v___x_59_ = l_Lean_instInhabitedExpr;
v___x_60_ = lean_box(v___x_58_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2(lean_object* v_msg_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2___closed__0, &l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2___closed__0);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_panic_fn_borrowed(v___x_65_, v_msg_62_);
lean_dec_ref_known(v___x_65_, 2);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(lean_object* v_m_67_, lean_object* v_query_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_x_70_, v_zero_72_);
if (v_isZero_73_ == 1)
{
lean_dec(v_x_71_);
lean_dec(v_x_70_);
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(2);
return v___x_74_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_val_75_ = lean_ctor_get(v_x_69_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v_x_69_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_val_75_);
lean_dec(v_x_69_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_val_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v_keyArray_83_; lean_object* v_valueArray_84_; lean_object* v___x_85_; uint8_t v_isSome_86_; 
v_keyArray_83_ = lean_ctor_get(v_m_67_, 1);
v_valueArray_84_ = lean_ctor_get(v_m_67_, 2);
v___x_85_ = lean_array_fget_borrowed(v_keyArray_83_, v_x_71_);
v_isSome_86_ = lean_noption_is_some(v___x_85_);
if (v_isSome_86_ == 0)
{
lean_dec(v_x_70_);
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_x_71_);
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
lean_dec(v_x_71_);
v_val_88_ = lean_ctor_get(v_x_69_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v_x_69_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v_x_69_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_val_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_object* v_one_96_; lean_object* v_n_97_; lean_object* v___y_99_; 
v_one_96_ = lean_unsigned_to_nat(1u);
v_n_97_ = lean_nat_sub(v_x_70_, v_one_96_);
lean_dec(v_x_70_);
if (v_isSome_86_ == 0)
{
goto v___jp_105_;
}
else
{
lean_object* v___x_107_; uint8_t v_isSome_108_; 
v___x_107_ = lean_array_fget_borrowed(v_valueArray_84_, v_x_71_);
v_isSome_108_ = lean_noption_is_some(v___x_107_);
if (v_isSome_108_ == 0)
{
goto v___jp_105_;
}
else
{
lean_object* v_val_109_; uint8_t v___x_110_; 
lean_inc(v___x_85_);
v_val_109_ = lean_noption_get(v___x_85_);
v___x_110_ = lean_nat_dec_eq(v_val_109_, v_query_68_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
lean_dec(v_val_109_);
v___x_111_ = lean_array_get_size(v_keyArray_83_);
v___x_112_ = lean_nat_add(v_x_71_, v_one_96_);
lean_dec(v_x_71_);
v___x_113_ = lean_nat_dec_lt(v___x_112_, v___x_111_);
if (v___x_113_ == 0)
{
lean_dec(v___x_112_);
v_x_70_ = v_n_97_;
v_x_71_ = v_zero_72_;
goto _start;
}
else
{
v_x_70_ = v_n_97_;
v_x_71_ = v___x_112_;
goto _start;
}
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; 
lean_dec(v_n_97_);
lean_dec(v_x_69_);
lean_inc(v___x_107_);
v_val_116_ = lean_noption_get(v___x_107_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_x_71_);
lean_ctor_set(v___x_117_, 1, v_val_109_);
lean_ctor_set(v___x_117_, 2, v_val_116_);
return v___x_117_;
}
}
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_array_get_size(v_keyArray_83_);
v___x_101_ = lean_nat_add(v_x_71_, v_one_96_);
lean_dec(v_x_71_);
v___x_102_ = lean_nat_dec_lt(v___x_101_, v___x_100_);
if (v___x_102_ == 0)
{
lean_dec(v___x_101_);
v_x_69_ = v___y_99_;
v_x_70_ = v_n_97_;
v_x_71_ = v_zero_72_;
goto _start;
}
else
{
v_x_69_ = v___y_99_;
v_x_70_ = v_n_97_;
v_x_71_ = v___x_101_;
goto _start;
}
}
v___jp_105_:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_106_; 
lean_inc(v_x_71_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v_x_71_);
v___y_99_ = v___x_106_;
goto v___jp_98_;
}
else
{
v___y_99_ = v_x_69_;
goto v___jp_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg___boxed(lean_object* v_m_118_, lean_object* v_query_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_m_118_, v_query_119_, v_x_120_, v_x_121_, v_x_122_);
lean_dec(v_query_119_);
lean_dec_ref(v_m_118_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(lean_object* v_m_124_, lean_object* v_query_125_){
_start:
{
lean_object* v_keyArray_126_; lean_object* v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v_fold_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_keyArray_126_ = lean_ctor_get(v_m_124_, 1);
v___x_127_ = lean_array_get_size(v_keyArray_126_);
v___x_128_ = lean_uint64_of_nat(v_query_125_);
v___x_129_ = 32ULL;
v___x_130_ = lean_uint64_shift_right(v___x_128_, v___x_129_);
v_fold_131_ = lean_uint64_xor(v___x_128_, v___x_130_);
v___x_132_ = 16ULL;
v___x_133_ = lean_uint64_shift_right(v_fold_131_, v___x_132_);
v___x_134_ = lean_uint64_xor(v_fold_131_, v___x_133_);
v___x_135_ = lean_uint64_to_usize(v___x_134_);
v___x_136_ = lean_usize_of_nat(v___x_127_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_sub(v___x_136_, v___x_137_);
v___x_139_ = lean_usize_land(v___x_135_, v___x_138_);
v___x_140_ = lean_usize_to_nat(v___x_139_);
v___x_141_ = lean_box(0);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_m_124_, v_query_125_, v___x_141_, v___x_127_, v___x_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg___boxed(lean_object* v_m_143_, lean_object* v_query_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_m_143_, v_query_144_);
lean_dec(v_query_144_);
lean_dec_ref(v_m_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg(lean_object* v_m_146_, lean_object* v_query_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_m_146_, v_query_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_index_149_; lean_object* v_key_150_; lean_object* v_value_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_index_149_ = lean_ctor_get(v___x_148_, 0);
v_key_150_ = lean_ctor_get(v___x_148_, 1);
v_value_151_ = lean_ctor_get(v___x_148_, 2);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_148_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_value_151_);
lean_inc(v_key_150_);
lean_inc(v_index_149_);
lean_dec(v___x_148_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_index_149_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_key_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_value_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v___x_159_; 
lean_dec(v___x_148_);
v___x_159_ = lean_box(1);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_160_, lean_object* v_query_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg(v_m_160_, v_query_161_);
lean_dec(v_query_161_);
lean_dec_ref(v_m_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(lean_object* v_m_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg(v_m_163_, v_a_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_value_166_; lean_object* v___x_167_; 
v_value_166_ = lean_ctor_get(v___x_165_, 2);
lean_inc(v_value_166_);
lean_dec_ref_known(v___x_165_, 3);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v_value_166_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg___boxed(lean_object* v_m_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_m_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_m_169_);
return v_res_171_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_175_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__2));
v___x_176_ = lean_unsigned_to_nat(12u);
v___x_177_ = lean_unsigned_to_nat(672u);
v___x_178_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__1));
v___x_179_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__0));
v___x_180_ = l_mkPanicMessageWithDecl(v___x_179_, v___x_178_, v___x_177_, v___x_176_, v___x_175_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object* v_m_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_m_181_, v_a_182_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___closed__3);
v___x_185_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__2(v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; 
v_val_186_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_val_186_);
lean_dec_ref_known(v___x_183_, 1);
return v_val_186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_m_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_m_187_);
return v_res_189_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_193_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2));
v___x_194_ = lean_unsigned_to_nat(6u);
v___x_195_ = lean_unsigned_to_nat(67u);
v___x_196_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1));
v___x_197_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0));
v___x_198_ = l_mkPanicMessageWithDecl(v___x_197_, v___x_196_, v___x_195_, v___x_194_, v___x_193_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object* v_as_x27_199_, lean_object* v_b_200_){
_start:
{
if (lean_obj_tag(v_as_x27_199_) == 0)
{
return v_b_200_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v_fst_203_; lean_object* v_snd_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_228_; 
v_head_201_ = lean_ctor_get(v_as_x27_199_, 0);
v_tail_202_ = lean_ctor_get(v_as_x27_199_, 1);
v_fst_203_ = lean_ctor_get(v_head_201_, 0);
v_snd_204_ = lean_ctor_get(v_head_201_, 1);
v_fst_205_ = lean_ctor_get(v_b_200_, 0);
v_snd_206_ = lean_ctor_get(v_b_200_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_b_200_);
if (v_isSharedCheck_228_ == 0)
{
v___x_208_ = v_b_200_;
v_isShared_209_ = v_isSharedCheck_228_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_snd_206_);
lean_inc(v_fst_205_);
lean_dec(v_b_200_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_228_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_value_211_; uint8_t v___x_218_; 
v___x_218_ = lean_nat_dec_eq(v_fst_203_, v_snd_206_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_del_object(v___x_208_);
lean_dec(v_snd_206_);
lean_dec(v_fst_205_);
v___x_219_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3);
v___x_220_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
return v_a_221_;
}
else
{
lean_object* v_a_222_; 
v_a_222_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_220_, 1);
v_as_x27_199_ = v_tail_202_;
v_b_200_ = v_a_222_;
goto _start;
}
}
else
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_snd_204_);
if (v___x_224_ == 0)
{
v_value_211_ = v_fst_205_;
goto v___jp_210_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_shiftl(v___x_225_, v_snd_206_);
v___x_227_ = lean_nat_lor(v_fst_205_, v___x_226_);
lean_dec(v___x_226_);
lean_dec(v_fst_205_);
v_value_211_ = v___x_227_;
goto v___jp_210_;
}
}
v___jp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v_snd_206_, v___x_212_);
lean_dec(v_snd_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_213_);
lean_ctor_set(v___x_208_, 0, v_value_211_);
v___x_215_ = v___x_208_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_value_211_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v_as_x27_199_ = v_tail_202_;
v_b_200_ = v___x_215_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___boxed(lean_object* v_as_x27_229_, lean_object* v_b_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_229_, v_b_230_);
lean_dec(v_as_x27_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object* v_init_232_, lean_object* v_x_233_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
lean_object* v_k_234_; lean_object* v_v_235_; lean_object* v_l_236_; lean_object* v_r_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_k_234_ = lean_ctor_get(v_x_233_, 1);
v_v_235_ = lean_ctor_get(v_x_233_, 2);
v_l_236_ = lean_ctor_get(v_x_233_, 3);
v_r_237_ = lean_ctor_get(v_x_233_, 4);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_232_, v_r_237_);
lean_inc(v_v_235_);
lean_inc(v_k_234_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_k_234_);
lean_ctor_set(v___x_239_, 1, v_v_235_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
v_init_232_ = v___x_240_;
v_x_233_ = v_l_236_;
goto _start;
}
else
{
return v_init_232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___boxed(lean_object* v_init_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_242_, v_x_243_);
lean_dec(v_x_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(lean_object* v_atomsAssignment_247_, lean_object* v_as_248_, size_t v_sz_249_, size_t v_i_250_, lean_object* v_b_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_lt(v_i_250_, v_sz_249_);
if (v___x_252_ == 0)
{
return v_b_251_;
}
else
{
lean_object* v_a_253_; lean_object* v_fst_254_; lean_object* v_snd_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_snd_258_; lean_object* v_fst_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_283_; 
v_a_253_ = lean_array_uget_borrowed(v_as_248_, v_i_250_);
v_fst_254_ = lean_ctor_get(v_a_253_, 0);
v_snd_255_ = lean_ctor_get(v_a_253_, 1);
v___x_256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___closed__0));
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_247_, v_fst_254_);
v_snd_258_ = lean_ctor_get(v___x_257_, 1);
lean_inc(v_snd_258_);
lean_dec_ref(v___x_257_);
v_fst_259_ = lean_ctor_get(v_snd_258_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_snd_258_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_snd_258_, 1);
lean_dec(v_unused_284_);
v___x_261_ = v_snd_258_;
v_isShared_262_ = v_isSharedCheck_283_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_fst_259_);
lean_dec(v_snd_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_283_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_282_; 
v___x_263_ = lean_box(0);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v___x_263_, v_snd_255_);
v___x_265_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v___x_264_, v___x_256_);
lean_dec(v___x_264_);
v_fst_266_ = lean_ctor_get(v___x_265_, 0);
v_snd_267_ = lean_ctor_get(v___x_265_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_282_ == 0)
{
v___x_269_ = v___x_265_;
v_isShared_270_ = v_isSharedCheck_282_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_snd_267_);
lean_inc(v_fst_266_);
lean_dec(v___x_265_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_282_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = l_BitVec_ofNat(v_snd_267_, v_fst_266_);
lean_dec(v_fst_266_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_271_);
lean_ctor_set(v___x_261_, 0, v_snd_267_);
v___x_273_ = v___x_261_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_snd_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_281_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_275_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_273_);
lean_ctor_set(v___x_269_, 0, v_fst_259_);
v___x_275_ = v___x_269_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_fst_259_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_280_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; size_t v___x_277_; size_t v___x_278_; 
v___x_276_ = lean_array_push(v_b_251_, v___x_275_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_250_, v___x_277_);
v_i_250_ = v___x_278_;
v_b_251_ = v___x_276_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___boxed(lean_object* v_atomsAssignment_285_, lean_object* v_as_286_, lean_object* v_sz_287_, lean_object* v_i_288_, lean_object* v_b_289_){
_start:
{
size_t v_sz_boxed_290_; size_t v_i_boxed_291_; lean_object* v_res_292_; 
v_sz_boxed_290_ = lean_unbox_usize(v_sz_287_);
lean_dec(v_sz_287_);
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_atomsAssignment_285_, v_as_286_, v_sz_boxed_290_, v_i_boxed_291_, v_b_289_);
lean_dec_ref(v_as_286_);
lean_dec_ref(v_atomsAssignment_285_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(lean_object* v_k_293_, lean_object* v_v_294_, lean_object* v_t_295_){
_start:
{
if (lean_obj_tag(v_t_295_) == 0)
{
lean_object* v_size_296_; lean_object* v_k_297_; lean_object* v_v_298_; lean_object* v_l_299_; lean_object* v_r_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_581_; 
v_size_296_ = lean_ctor_get(v_t_295_, 0);
v_k_297_ = lean_ctor_get(v_t_295_, 1);
v_v_298_ = lean_ctor_get(v_t_295_, 2);
v_l_299_ = lean_ctor_get(v_t_295_, 3);
v_r_300_ = lean_ctor_get(v_t_295_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v_t_295_);
if (v_isSharedCheck_581_ == 0)
{
v___x_302_ = v_t_295_;
v_isShared_303_ = v_isSharedCheck_581_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_r_300_);
lean_inc(v_l_299_);
lean_inc(v_v_298_);
lean_inc(v_k_297_);
lean_inc(v_size_296_);
lean_dec(v_t_295_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_581_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_lt(v_k_293_, v_k_297_);
if (v___x_304_ == 0)
{
uint8_t v___x_305_; 
v___x_305_ = lean_nat_dec_eq(v_k_293_, v_k_297_);
if (v___x_305_ == 0)
{
lean_object* v_impl_306_; lean_object* v___x_307_; 
lean_dec(v_size_296_);
v_impl_306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_293_, v_v_294_, v_r_300_);
v___x_307_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_299_) == 0)
{
lean_object* v_size_308_; lean_object* v_size_309_; lean_object* v_k_310_; lean_object* v_v_311_; lean_object* v_l_312_; lean_object* v_r_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_size_308_ = lean_ctor_get(v_l_299_, 0);
v_size_309_ = lean_ctor_get(v_impl_306_, 0);
lean_inc(v_size_309_);
v_k_310_ = lean_ctor_get(v_impl_306_, 1);
lean_inc(v_k_310_);
v_v_311_ = lean_ctor_get(v_impl_306_, 2);
lean_inc(v_v_311_);
v_l_312_ = lean_ctor_get(v_impl_306_, 3);
lean_inc(v_l_312_);
v_r_313_ = lean_ctor_get(v_impl_306_, 4);
lean_inc(v_r_313_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_mul(v___x_314_, v_size_308_);
v___x_316_ = lean_nat_dec_lt(v___x_315_, v_size_309_);
lean_dec(v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_dec(v_r_313_);
lean_dec(v_l_312_);
lean_dec(v_v_311_);
lean_dec(v_k_310_);
v___x_317_ = lean_nat_add(v___x_307_, v_size_308_);
v___x_318_ = lean_nat_add(v___x_317_, v_size_309_);
lean_dec(v_size_309_);
lean_dec(v___x_317_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_impl_306_);
lean_ctor_set(v___x_302_, 0, v___x_318_);
v___x_320_ = v___x_302_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_impl_306_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_385_; 
v_isSharedCheck_385_ = !lean_is_exclusive(v_impl_306_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_386_ = lean_ctor_get(v_impl_306_, 4);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_impl_306_, 3);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_impl_306_, 2);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_impl_306_, 1);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_impl_306_, 0);
lean_dec(v_unused_390_);
v___x_323_ = v_impl_306_;
v_isShared_324_ = v_isSharedCheck_385_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_impl_306_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_385_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_size_325_; lean_object* v_k_326_; lean_object* v_v_327_; lean_object* v_l_328_; lean_object* v_r_329_; lean_object* v_size_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_size_325_ = lean_ctor_get(v_l_312_, 0);
v_k_326_ = lean_ctor_get(v_l_312_, 1);
v_v_327_ = lean_ctor_get(v_l_312_, 2);
v_l_328_ = lean_ctor_get(v_l_312_, 3);
v_r_329_ = lean_ctor_get(v_l_312_, 4);
v_size_330_ = lean_ctor_get(v_r_313_, 0);
v___x_331_ = lean_unsigned_to_nat(2u);
v___x_332_ = lean_nat_mul(v___x_331_, v_size_330_);
v___x_333_ = lean_nat_dec_lt(v_size_325_, v___x_332_);
lean_dec(v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_361_; 
lean_inc(v_r_329_);
lean_inc(v_l_328_);
lean_inc(v_v_327_);
lean_inc(v_k_326_);
v_isSharedCheck_361_ = !lean_is_exclusive(v_l_312_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; lean_object* v_unused_365_; lean_object* v_unused_366_; 
v_unused_362_ = lean_ctor_get(v_l_312_, 4);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_l_312_, 3);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_l_312_, 2);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_l_312_, 1);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_l_312_, 0);
lean_dec(v_unused_366_);
v___x_335_ = v_l_312_;
v_isShared_336_ = v_isSharedCheck_361_;
goto v_resetjp_334_;
}
else
{
lean_dec(v_l_312_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_361_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_351_; 
v___x_337_ = lean_nat_add(v___x_307_, v_size_308_);
v___x_338_ = lean_nat_add(v___x_337_, v_size_309_);
lean_dec(v_size_309_);
if (lean_obj_tag(v_l_328_) == 0)
{
lean_object* v_size_359_; 
v_size_359_ = lean_ctor_get(v_l_328_, 0);
lean_inc(v_size_359_);
v___y_351_ = v_size_359_;
goto v___jp_350_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v___y_351_ = v___x_360_;
goto v___jp_350_;
}
v___jp_339_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_nat_add(v___y_340_, v___y_342_);
lean_dec(v___y_342_);
lean_dec(v___y_340_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 4, v_r_313_);
lean_ctor_set(v___x_335_, 3, v_r_329_);
lean_ctor_set(v___x_335_, 2, v_v_311_);
lean_ctor_set(v___x_335_, 1, v_k_310_);
lean_ctor_set(v___x_335_, 0, v___x_343_);
v___x_345_ = v___x_335_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_k_310_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_v_311_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_r_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_r_313_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v___x_345_);
lean_ctor_set(v___x_323_, 3, v___y_341_);
lean_ctor_set(v___x_323_, 2, v_v_327_);
lean_ctor_set(v___x_323_, 1, v_k_326_);
lean_ctor_set(v___x_323_, 0, v___x_338_);
v___x_347_ = v___x_323_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v___y_341_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
v___jp_350_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_nat_add(v___x_337_, v___y_351_);
lean_dec(v___y_351_);
lean_dec(v___x_337_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_l_328_);
lean_ctor_set(v___x_302_, 0, v___x_352_);
v___x_354_ = v___x_302_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v_l_328_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = lean_nat_add(v___x_307_, v_size_330_);
if (lean_obj_tag(v_r_329_) == 0)
{
lean_object* v_size_356_; 
v_size_356_ = lean_ctor_get(v_r_329_, 0);
lean_inc(v_size_356_);
v___y_340_ = v___x_355_;
v___y_341_ = v___x_354_;
v___y_342_ = v_size_356_;
goto v___jp_339_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v___y_340_ = v___x_355_;
v___y_341_ = v___x_354_;
v___y_342_ = v___x_357_;
goto v___jp_339_;
}
}
}
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_del_object(v___x_302_);
v___x_367_ = lean_nat_add(v___x_307_, v_size_308_);
v___x_368_ = lean_nat_add(v___x_367_, v_size_309_);
lean_dec(v_size_309_);
v___x_369_ = lean_nat_add(v___x_367_, v_size_325_);
lean_dec(v___x_367_);
lean_inc_ref(v_l_299_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v_l_312_);
lean_ctor_set(v___x_323_, 3, v_l_299_);
lean_ctor_set(v___x_323_, 2, v_v_298_);
lean_ctor_set(v___x_323_, 1, v_k_297_);
lean_ctor_set(v___x_323_, 0, v___x_369_);
v___x_371_ = v___x_323_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_l_312_);
v___x_371_ = v_reuseFailAlloc_384_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_isSharedCheck_378_ = !lean_is_exclusive(v_l_299_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_379_ = lean_ctor_get(v_l_299_, 4);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_l_299_, 3);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_l_299_, 2);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_l_299_, 1);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_l_299_, 0);
lean_dec(v_unused_383_);
v___x_373_ = v_l_299_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_dec(v_l_299_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 4, v_r_313_);
lean_ctor_set(v___x_373_, 3, v___x_371_);
lean_ctor_set(v___x_373_, 2, v_v_311_);
lean_ctor_set(v___x_373_, 1, v_k_310_);
lean_ctor_set(v___x_373_, 0, v___x_368_);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_310_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_311_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_r_313_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_391_; 
v_l_391_ = lean_ctor_get(v_impl_306_, 3);
lean_inc(v_l_391_);
if (lean_obj_tag(v_l_391_) == 0)
{
lean_object* v_r_392_; lean_object* v_k_393_; lean_object* v_v_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_417_; 
v_r_392_ = lean_ctor_get(v_impl_306_, 4);
v_k_393_ = lean_ctor_get(v_impl_306_, 1);
v_v_394_ = lean_ctor_get(v_impl_306_, 2);
v_isSharedCheck_417_ = !lean_is_exclusive(v_impl_306_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_418_ = lean_ctor_get(v_impl_306_, 3);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_impl_306_, 0);
lean_dec(v_unused_419_);
v___x_396_ = v_impl_306_;
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_r_392_);
lean_inc(v_v_394_);
lean_inc(v_k_393_);
lean_dec(v_impl_306_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_k_398_; lean_object* v_v_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_413_; 
v_k_398_ = lean_ctor_get(v_l_391_, 1);
v_v_399_ = lean_ctor_get(v_l_391_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_l_391_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_414_ = lean_ctor_get(v_l_391_, 4);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_l_391_, 3);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_l_391_, 0);
lean_dec(v_unused_416_);
v___x_401_ = v_l_391_;
v_isShared_402_ = v_isSharedCheck_413_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_v_399_);
lean_inc(v_k_398_);
lean_dec(v_l_391_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_413_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_392_, 2);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 4, v_r_392_);
lean_ctor_set(v___x_401_, 3, v_r_392_);
lean_ctor_set(v___x_401_, 2, v_v_298_);
lean_ctor_set(v___x_401_, 1, v_k_297_);
lean_ctor_set(v___x_401_, 0, v___x_307_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_r_392_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_r_392_);
v___x_405_ = v_reuseFailAlloc_412_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
lean_inc(v_r_392_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 3, v_r_392_);
lean_ctor_set(v___x_396_, 0, v___x_307_);
v___x_407_ = v___x_396_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_k_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_v_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_r_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_r_392_);
v___x_407_ = v_reuseFailAlloc_411_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v___x_407_);
lean_ctor_set(v___x_302_, 3, v___x_405_);
lean_ctor_set(v___x_302_, 2, v_v_399_);
lean_ctor_set(v___x_302_, 1, v_k_398_);
lean_ctor_set(v___x_302_, 0, v___x_403_);
v___x_409_ = v___x_302_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_399_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
else
{
lean_object* v_r_420_; 
v_r_420_ = lean_ctor_get(v_impl_306_, 4);
lean_inc(v_r_420_);
if (lean_obj_tag(v_r_420_) == 0)
{
lean_object* v_k_421_; lean_object* v_v_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_433_; 
v_k_421_ = lean_ctor_get(v_impl_306_, 1);
v_v_422_ = lean_ctor_get(v_impl_306_, 2);
v_isSharedCheck_433_ = !lean_is_exclusive(v_impl_306_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_434_ = lean_ctor_get(v_impl_306_, 4);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_impl_306_, 3);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_impl_306_, 0);
lean_dec(v_unused_436_);
v___x_424_ = v_impl_306_;
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_v_422_);
lean_inc(v_k_421_);
lean_dec(v_impl_306_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(3u);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 4, v_l_391_);
lean_ctor_set(v___x_424_, 2, v_v_298_);
lean_ctor_set(v___x_424_, 1, v_k_297_);
lean_ctor_set(v___x_424_, 0, v___x_307_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_l_391_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_l_391_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_420_);
lean_ctor_set(v___x_302_, 3, v___x_428_);
lean_ctor_set(v___x_302_, 2, v_v_422_);
lean_ctor_set(v___x_302_, 1, v_k_421_);
lean_ctor_set(v___x_302_, 0, v___x_426_);
v___x_430_ = v___x_302_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_k_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_v_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_r_420_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(2u);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_impl_306_);
lean_ctor_set(v___x_302_, 3, v_r_420_);
lean_ctor_set(v___x_302_, 0, v___x_437_);
v___x_439_ = v___x_302_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_r_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_impl_306_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v_v_298_);
lean_dec(v_k_297_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 2, v_v_294_);
lean_ctor_set(v___x_302_, 1, v_k_293_);
v___x_442_ = v___x_302_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_size_296_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_k_293_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_v_294_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_l_299_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_r_300_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_impl_444_; lean_object* v___x_445_; 
lean_dec(v_size_296_);
v_impl_444_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_293_, v_v_294_, v_l_299_);
v___x_445_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_300_) == 0)
{
lean_object* v_size_446_; lean_object* v_size_447_; lean_object* v_k_448_; lean_object* v_v_449_; lean_object* v_l_450_; lean_object* v_r_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_size_446_ = lean_ctor_get(v_r_300_, 0);
v_size_447_ = lean_ctor_get(v_impl_444_, 0);
lean_inc(v_size_447_);
v_k_448_ = lean_ctor_get(v_impl_444_, 1);
lean_inc(v_k_448_);
v_v_449_ = lean_ctor_get(v_impl_444_, 2);
lean_inc(v_v_449_);
v_l_450_ = lean_ctor_get(v_impl_444_, 3);
lean_inc(v_l_450_);
v_r_451_ = lean_ctor_get(v_impl_444_, 4);
lean_inc(v_r_451_);
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = lean_nat_mul(v___x_452_, v_size_446_);
v___x_454_ = lean_nat_dec_lt(v___x_453_, v_size_447_);
lean_dec(v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec(v_r_451_);
lean_dec(v_l_450_);
lean_dec(v_v_449_);
lean_dec(v_k_448_);
v___x_455_ = lean_nat_add(v___x_445_, v_size_447_);
lean_dec(v_size_447_);
v___x_456_ = lean_nat_add(v___x_455_, v_size_446_);
lean_dec(v___x_455_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v_impl_444_);
lean_ctor_set(v___x_302_, 0, v___x_456_);
v___x_458_ = v___x_302_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_impl_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_r_300_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_525_; 
v_isSharedCheck_525_ = !lean_is_exclusive(v_impl_444_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_526_ = lean_ctor_get(v_impl_444_, 4);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_impl_444_, 3);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_impl_444_, 2);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_impl_444_, 1);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_impl_444_, 0);
lean_dec(v_unused_530_);
v___x_461_ = v_impl_444_;
v_isShared_462_ = v_isSharedCheck_525_;
goto v_resetjp_460_;
}
else
{
lean_dec(v_impl_444_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_525_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_size_463_; lean_object* v_size_464_; lean_object* v_k_465_; lean_object* v_v_466_; lean_object* v_l_467_; lean_object* v_r_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_size_463_ = lean_ctor_get(v_l_450_, 0);
v_size_464_ = lean_ctor_get(v_r_451_, 0);
v_k_465_ = lean_ctor_get(v_r_451_, 1);
v_v_466_ = lean_ctor_get(v_r_451_, 2);
v_l_467_ = lean_ctor_get(v_r_451_, 3);
v_r_468_ = lean_ctor_get(v_r_451_, 4);
v___x_469_ = lean_unsigned_to_nat(2u);
v___x_470_ = lean_nat_mul(v___x_469_, v_size_463_);
v___x_471_ = lean_nat_dec_lt(v_size_464_, v___x_470_);
lean_dec(v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_500_; 
lean_inc(v_r_468_);
lean_inc(v_l_467_);
lean_inc(v_v_466_);
lean_inc(v_k_465_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_r_451_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; 
v_unused_501_ = lean_ctor_get(v_r_451_, 4);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_r_451_, 3);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_r_451_, 2);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_r_451_, 1);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_r_451_, 0);
lean_dec(v_unused_505_);
v___x_473_ = v_r_451_;
v_isShared_474_ = v_isSharedCheck_500_;
goto v_resetjp_472_;
}
else
{
lean_dec(v_r_451_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_500_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___x_488_; lean_object* v___y_490_; 
v___x_475_ = lean_nat_add(v___x_445_, v_size_447_);
lean_dec(v_size_447_);
v___x_476_ = lean_nat_add(v___x_475_, v_size_446_);
lean_dec(v___x_475_);
v___x_488_ = lean_nat_add(v___x_445_, v_size_463_);
if (lean_obj_tag(v_l_467_) == 0)
{
lean_object* v_size_498_; 
v_size_498_ = lean_ctor_get(v_l_467_, 0);
lean_inc(v_size_498_);
v___y_490_ = v_size_498_;
goto v___jp_489_;
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___y_490_ = v___x_499_;
goto v___jp_489_;
}
v___jp_477_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_nat_add(v___y_478_, v___y_480_);
lean_dec(v___y_480_);
lean_dec(v___y_478_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_r_300_);
lean_ctor_set(v___x_473_, 3, v_r_468_);
lean_ctor_set(v___x_473_, 2, v_v_298_);
lean_ctor_set(v___x_473_, 1, v_k_297_);
lean_ctor_set(v___x_473_, 0, v___x_481_);
v___x_483_ = v___x_473_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_r_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v_r_300_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 4, v___x_483_);
lean_ctor_set(v___x_461_, 3, v___y_479_);
lean_ctor_set(v___x_461_, 2, v_v_466_);
lean_ctor_set(v___x_461_, 1, v_k_465_);
lean_ctor_set(v___x_461_, 0, v___x_476_);
v___x_485_ = v___x_461_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_k_465_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_v_466_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v___y_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_nat_add(v___x_488_, v___y_490_);
lean_dec(v___y_490_);
lean_dec(v___x_488_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_l_467_);
lean_ctor_set(v___x_302_, 3, v_l_450_);
lean_ctor_set(v___x_302_, 2, v_v_449_);
lean_ctor_set(v___x_302_, 1, v_k_448_);
lean_ctor_set(v___x_302_, 0, v___x_491_);
v___x_493_ = v___x_302_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_l_467_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; 
v___x_494_ = lean_nat_add(v___x_445_, v_size_446_);
if (lean_obj_tag(v_r_468_) == 0)
{
lean_object* v_size_495_; 
v_size_495_ = lean_ctor_get(v_r_468_, 0);
lean_inc(v_size_495_);
v___y_478_ = v___x_494_;
v___y_479_ = v___x_493_;
v___y_480_ = v_size_495_;
goto v___jp_477_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___y_478_ = v___x_494_;
v___y_479_ = v___x_493_;
v___y_480_ = v___x_496_;
goto v___jp_477_;
}
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
lean_del_object(v___x_302_);
v___x_506_ = lean_nat_add(v___x_445_, v_size_447_);
lean_dec(v_size_447_);
v___x_507_ = lean_nat_add(v___x_506_, v_size_446_);
lean_dec(v___x_506_);
v___x_508_ = lean_nat_add(v___x_445_, v_size_446_);
v___x_509_ = lean_nat_add(v___x_508_, v_size_464_);
lean_dec(v___x_508_);
lean_inc_ref(v_r_300_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 4, v_r_300_);
lean_ctor_set(v___x_461_, 3, v_r_451_);
lean_ctor_set(v___x_461_, 2, v_v_298_);
lean_ctor_set(v___x_461_, 1, v_k_297_);
lean_ctor_set(v___x_461_, 0, v___x_509_);
v___x_511_ = v___x_461_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_r_451_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_r_300_);
v___x_511_ = v_reuseFailAlloc_524_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_isSharedCheck_518_ = !lean_is_exclusive(v_r_300_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; lean_object* v_unused_522_; lean_object* v_unused_523_; 
v_unused_519_ = lean_ctor_get(v_r_300_, 4);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_r_300_, 3);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_r_300_, 2);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_r_300_, 1);
lean_dec(v_unused_522_);
v_unused_523_ = lean_ctor_get(v_r_300_, 0);
lean_dec(v_unused_523_);
v___x_513_ = v_r_300_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_dec(v_r_300_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v___x_511_);
lean_ctor_set(v___x_513_, 3, v_l_450_);
lean_ctor_set(v___x_513_, 2, v_v_449_);
lean_ctor_set(v___x_513_, 1, v_k_448_);
lean_ctor_set(v___x_513_, 0, v___x_507_);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_k_448_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_v_449_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_l_450_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_531_; 
v_l_531_ = lean_ctor_get(v_impl_444_, 3);
lean_inc(v_l_531_);
if (lean_obj_tag(v_l_531_) == 0)
{
lean_object* v_r_532_; lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_r_532_ = lean_ctor_get(v_impl_444_, 4);
v_k_533_ = lean_ctor_get(v_impl_444_, 1);
v_v_534_ = lean_ctor_get(v_impl_444_, 2);
v_isSharedCheck_545_ = !lean_is_exclusive(v_impl_444_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_impl_444_, 3);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_impl_444_, 0);
lean_dec(v_unused_547_);
v___x_536_ = v_impl_444_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_r_532_);
lean_inc(v_v_534_);
lean_inc(v_k_533_);
lean_dec(v_impl_444_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 3, v_r_532_);
lean_ctor_set(v___x_536_, 2, v_v_298_);
lean_ctor_set(v___x_536_, 1, v_k_297_);
lean_ctor_set(v___x_536_, 0, v___x_445_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_r_532_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_r_532_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v___x_540_);
lean_ctor_set(v___x_302_, 3, v_l_531_);
lean_ctor_set(v___x_302_, 2, v_v_534_);
lean_ctor_set(v___x_302_, 1, v_k_533_);
lean_ctor_set(v___x_302_, 0, v___x_538_);
v___x_542_ = v___x_302_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_l_531_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v_r_548_; 
v_r_548_ = lean_ctor_get(v_impl_444_, 4);
lean_inc(v_r_548_);
if (lean_obj_tag(v_r_548_) == 0)
{
lean_object* v_k_549_; lean_object* v_v_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_573_; 
v_k_549_ = lean_ctor_get(v_impl_444_, 1);
v_v_550_ = lean_ctor_get(v_impl_444_, 2);
v_isSharedCheck_573_ = !lean_is_exclusive(v_impl_444_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_574_ = lean_ctor_get(v_impl_444_, 4);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_impl_444_, 3);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_impl_444_, 0);
lean_dec(v_unused_576_);
v___x_552_ = v_impl_444_;
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_v_550_);
lean_inc(v_k_549_);
lean_dec(v_impl_444_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_k_554_; lean_object* v_v_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_569_; 
v_k_554_ = lean_ctor_get(v_r_548_, 1);
v_v_555_ = lean_ctor_get(v_r_548_, 2);
v_isSharedCheck_569_ = !lean_is_exclusive(v_r_548_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; 
v_unused_570_ = lean_ctor_get(v_r_548_, 4);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_r_548_, 3);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_548_, 0);
lean_dec(v_unused_572_);
v___x_557_ = v_r_548_;
v_isShared_558_ = v_isSharedCheck_569_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_v_555_);
lean_inc(v_k_554_);
lean_dec(v_r_548_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_569_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_unsigned_to_nat(3u);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 4, v_l_531_);
lean_ctor_set(v___x_557_, 3, v_l_531_);
lean_ctor_set(v___x_557_, 2, v_v_550_);
lean_ctor_set(v___x_557_, 1, v_k_549_);
lean_ctor_set(v___x_557_, 0, v___x_445_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_k_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_v_550_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_l_531_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_l_531_);
v___x_561_ = v_reuseFailAlloc_568_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 4, v_l_531_);
lean_ctor_set(v___x_552_, 2, v_v_298_);
lean_ctor_set(v___x_552_, 1, v_k_297_);
lean_ctor_set(v___x_552_, 0, v___x_445_);
v___x_563_ = v___x_552_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_l_531_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_l_531_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v___x_563_);
lean_ctor_set(v___x_302_, 3, v___x_561_);
lean_ctor_set(v___x_302_, 2, v_v_555_);
lean_ctor_set(v___x_302_, 1, v_k_554_);
lean_ctor_set(v___x_302_, 0, v___x_559_);
v___x_565_ = v___x_302_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_k_554_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_v_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(2u);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_548_);
lean_ctor_set(v___x_302_, 3, v_impl_444_);
lean_ctor_set(v___x_302_, 0, v___x_577_);
v___x_579_ = v___x_302_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_impl_444_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_r_548_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_k_293_);
lean_ctor_set(v___x_583_, 2, v_v_294_);
lean_ctor_set(v___x_583_, 3, v_t_295_);
lean_ctor_set(v___x_583_, 4, v_t_295_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(lean_object* v_m_584_, lean_object* v_a_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_m_584_, v_a_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_inc(v_fallback_586_);
return v_fallback_586_;
}
else
{
lean_object* v_val_588_; 
v_val_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v___x_587_, 1);
return v_val_588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg___boxed(lean_object* v_m_589_, lean_object* v_a_590_, lean_object* v_fallback_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_589_, v_a_590_, v_fallback_591_);
lean_dec(v_fallback_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_m_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg(lean_object* v_b_593_, lean_object* v_acc_594_, lean_object* v_i_595_){
_start:
{
lean_object* v___y_597_; lean_object* v_keyArray_605_; lean_object* v_valueArray_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_keyArray_605_ = lean_ctor_get(v_b_593_, 1);
v_valueArray_606_ = lean_ctor_get(v_b_593_, 2);
v___x_607_ = lean_array_get_size(v_keyArray_605_);
v___x_608_ = lean_nat_dec_lt(v_i_595_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_i_595_);
return v_acc_594_;
}
else
{
lean_object* v___x_609_; uint8_t v_isSome_610_; 
v___x_609_ = lean_array_fget_borrowed(v_keyArray_605_, v_i_595_);
v_isSome_610_ = lean_noption_is_some(v___x_609_);
if (v_isSome_610_ == 0)
{
goto v___jp_601_;
}
else
{
lean_object* v___x_611_; uint8_t v_isSome_612_; 
v___x_611_ = lean_array_fget_borrowed(v_valueArray_606_, v_i_595_);
v_isSome_612_ = lean_noption_is_some(v___x_611_);
if (v_isSome_612_ == 0)
{
goto v___jp_601_;
}
else
{
lean_object* v_val_613_; lean_object* v_val_614_; lean_object* v_i_616_; lean_object* v___x_621_; 
lean_inc(v___x_609_);
v_val_613_ = lean_noption_get(v___x_609_);
lean_inc(v___x_611_);
v_val_614_ = lean_noption_get(v___x_611_);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_acc_594_, v_val_613_);
switch(lean_obj_tag(v___x_621_))
{
case 0:
{
lean_object* v_index_622_; lean_object* v_size_623_; lean_object* v___x_624_; 
v_index_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_index_622_);
lean_dec_ref_known(v___x_621_, 3);
v_size_623_ = lean_ctor_get(v_acc_594_, 0);
lean_inc(v_size_623_);
v___x_624_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_594_, v_size_623_, v_index_622_, v_val_613_, v_val_614_);
lean_dec(v_index_622_);
v___y_597_ = v___x_624_;
goto v___jp_596_;
}
case 1:
{
lean_object* v_index_625_; 
v_index_625_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_index_625_);
lean_dec_ref_known(v___x_621_, 1);
v_i_616_ = v_index_625_;
goto v___jp_615_;
}
default: 
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_594_, v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_index_628_; 
v_index_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_index_628_);
lean_dec_ref_known(v___x_627_, 1);
v_i_616_ = v_index_628_;
goto v___jp_615_;
}
else
{
lean_dec(v_val_614_);
lean_dec(v_val_613_);
v___y_597_ = v_acc_594_;
goto v___jp_596_;
}
}
}
v___jp_615_:
{
lean_object* v_size_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_size_617_ = lean_ctor_get(v_acc_594_, 0);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_size_617_, v___x_618_);
v___x_620_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_594_, v___x_619_, v_i_616_, v_val_613_, v_val_614_);
lean_dec(v_i_616_);
v___y_597_ = v___x_620_;
goto v___jp_596_;
}
}
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_i_595_, v___x_598_);
lean_dec(v_i_595_);
v_acc_594_ = v___y_597_;
v_i_595_ = v___x_599_;
goto _start;
}
v___jp_601_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_i_595_, v___x_602_);
lean_dec(v_i_595_);
v_i_595_ = v___x_603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg___boxed(lean_object* v_b_629_, lean_object* v_acc_630_, lean_object* v_i_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg(v_b_629_, v_acc_630_, v_i_631_);
lean_dec_ref(v_b_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg(lean_object* v_init_633_, lean_object* v_b_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg(v_b_634_, v_init_633_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg___boxed(lean_object* v_init_637_, lean_object* v_b_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg(v_init_637_, v_b_638_);
lean_dec_ref(v_b_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(lean_object* v_m_640_){
_start:
{
lean_object* v_keyArray_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_cellCount_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_target_648_; lean_object* v___x_649_; 
v_keyArray_641_ = lean_ctor_get(v_m_640_, 1);
v___x_642_ = lean_array_get_size(v_keyArray_641_);
v___x_643_ = lean_unsigned_to_nat(2u);
v_cellCount_644_ = lean_nat_mul(v___x_642_, v___x_643_);
v___x_645_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_644_);
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_644_);
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_644_);
v_target_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_648_, 0, v___x_645_);
lean_ctor_set(v_target_648_, 1, v___x_646_);
lean_ctor_set(v_target_648_, 2, v___x_647_);
v___x_649_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg(v_target_648_, v_m_640_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg___boxed(lean_object* v_m_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(v_m_650_);
lean_dec_ref(v_m_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object* v_aigSize_652_, lean_object* v_assignment_653_, lean_object* v_as_654_, size_t v_sz_655_, size_t v_i_656_, lean_object* v_b_657_){
_start:
{
lean_object* v___y_659_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v_i_667_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v_i_688_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___x_705_; 
v___x_705_ = lean_usize_dec_lt(v_i_656_, v_sz_655_);
if (v___x_705_ == 0)
{
return v_b_657_;
}
else
{
lean_object* v_a_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; uint8_t v___y_710_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_a_706_ = lean_array_uget_borrowed(v_as_654_, v_i_656_);
v_fst_707_ = lean_ctor_get(v_a_706_, 0);
v_snd_708_ = lean_ctor_get(v_a_706_, 1);
v___x_747_ = lean_nat_add(v_snd_708_, v_aigSize_652_);
v___x_748_ = lean_array_get_size(v_assignment_653_);
v___x_749_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v___x_747_);
v___y_710_ = v___x_705_;
goto v___jp_709_;
}
else
{
lean_object* v___x_750_; lean_object* v_fst_751_; uint8_t v___x_752_; 
v___x_750_ = lean_array_fget_borrowed(v_assignment_653_, v___x_747_);
lean_dec(v___x_747_);
v_fst_751_ = lean_ctor_get(v___x_750_, 0);
v___x_752_ = lean_unbox(v_fst_751_);
v___y_710_ = v___x_752_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v_var_711_; lean_object* v_idx_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_var_711_ = lean_ctor_get(v_fst_707_, 0);
v_idx_712_ = lean_ctor_get(v_fst_707_, 2);
v___x_713_ = lean_box(1);
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_b_657_, v_var_711_, v___x_713_);
v___x_715_ = lean_box(v___y_710_);
lean_inc(v_idx_712_);
v___x_716_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_idx_712_, v___x_715_, v___x_714_);
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_b_657_, v_var_711_);
switch(lean_obj_tag(v___x_717_))
{
case 0:
{
lean_object* v_index_718_; lean_object* v_size_719_; lean_object* v___x_720_; 
v_index_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_index_718_);
lean_dec_ref_known(v___x_717_, 3);
v_size_719_ = lean_ctor_get(v_b_657_, 0);
lean_inc(v_size_719_);
lean_inc(v_var_711_);
v___x_720_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_657_, v_size_719_, v_index_718_, v_var_711_, v___x_716_);
lean_dec(v_index_718_);
v___y_659_ = v___x_720_;
goto v___jp_658_;
}
case 1:
{
lean_object* v_index_721_; lean_object* v_size_722_; lean_object* v_keyArray_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_index_721_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_index_721_);
lean_dec_ref_known(v___x_717_, 1);
v_size_722_ = lean_ctor_get(v_b_657_, 0);
v_keyArray_723_ = lean_ctor_get(v_b_657_, 1);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_size_722_, v___x_724_);
v___x_726_ = lean_array_get_size(v_keyArray_723_);
v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_index_721_);
lean_inc(v_var_711_);
v___y_694_ = v___x_716_;
v___y_695_ = v_var_711_;
goto v___jp_693_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_728_ = lean_unsigned_to_nat(4u);
v___x_729_ = lean_nat_mul(v___x_725_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(3u);
v___x_731_ = lean_nat_mul(v___x_726_, v___x_730_);
v___x_732_ = lean_nat_dec_le(v___x_729_, v___x_731_);
lean_dec(v___x_731_);
lean_dec(v___x_729_);
if (v___x_732_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_index_721_);
lean_inc(v_var_711_);
v___y_694_ = v___x_716_;
v___y_695_ = v_var_711_;
goto v___jp_693_;
}
else
{
lean_object* v___x_733_; 
lean_inc(v_var_711_);
v___x_733_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_657_, v___x_725_, v_index_721_, v_var_711_, v___x_716_);
lean_dec(v_index_721_);
v___y_659_ = v___x_733_;
goto v___jp_658_;
}
}
}
default: 
{
lean_object* v_size_734_; lean_object* v_keyArray_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_size_734_ = lean_ctor_get(v_b_657_, 0);
v_keyArray_735_ = lean_ctor_get(v_b_657_, 1);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_size_734_, v___x_736_);
v___x_738_ = lean_array_get_size(v_keyArray_735_);
v___x_739_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v___x_737_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(v_b_657_);
lean_dec_ref(v_b_657_);
lean_inc(v_var_711_);
v___y_673_ = v___x_716_;
v___y_674_ = v_var_711_;
v___y_675_ = v___x_740_;
goto v___jp_672_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_741_ = lean_unsigned_to_nat(4u);
v___x_742_ = lean_nat_mul(v___x_737_, v___x_741_);
lean_dec(v___x_737_);
v___x_743_ = lean_unsigned_to_nat(3u);
v___x_744_ = lean_nat_mul(v___x_738_, v___x_743_);
v___x_745_ = lean_nat_dec_le(v___x_742_, v___x_744_);
lean_dec(v___x_744_);
lean_dec(v___x_742_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(v_b_657_);
lean_dec_ref(v_b_657_);
lean_inc(v_var_711_);
v___y_673_ = v___x_716_;
v___y_674_ = v_var_711_;
v___y_675_ = v___x_746_;
goto v___jp_672_;
}
else
{
lean_inc(v_var_711_);
v___y_673_ = v___x_716_;
v___y_674_ = v_var_711_;
v___y_675_ = v_b_657_;
goto v___jp_672_;
}
}
}
}
}
}
v___jp_658_:
{
size_t v___x_660_; size_t v___x_661_; 
v___x_660_ = ((size_t)1ULL);
v___x_661_ = lean_usize_add(v_i_656_, v___x_660_);
v_i_656_ = v___x_661_;
v_b_657_ = v___y_659_;
goto _start;
}
v___jp_663_:
{
lean_object* v_size_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_size_668_ = lean_ctor_get(v___y_664_, 0);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_size_668_, v___x_669_);
v___x_671_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_664_, v___x_670_, v_i_667_, v___y_666_, v___y_665_);
lean_dec(v_i_667_);
v___y_659_ = v___x_671_;
goto v___jp_658_;
}
v___jp_672_:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v___y_675_, v___y_674_);
switch(lean_obj_tag(v___x_676_))
{
case 0:
{
lean_object* v_index_677_; lean_object* v_size_678_; lean_object* v___x_679_; 
v_index_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_index_677_);
lean_dec_ref_known(v___x_676_, 3);
v_size_678_ = lean_ctor_get(v___y_675_, 0);
lean_inc(v_size_678_);
v___x_679_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_675_, v_size_678_, v_index_677_, v___y_674_, v___y_673_);
lean_dec(v_index_677_);
v___y_659_ = v___x_679_;
goto v___jp_658_;
}
case 1:
{
lean_object* v_index_680_; 
v_index_680_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_index_680_);
lean_dec_ref_known(v___x_676_, 1);
v___y_664_ = v___y_675_;
v___y_665_ = v___y_673_;
v___y_666_ = v___y_674_;
v_i_667_ = v_index_680_;
goto v___jp_663_;
}
default: 
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_675_, v___x_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_index_683_; 
v_index_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_index_683_);
lean_dec_ref_known(v___x_682_, 1);
v___y_664_ = v___y_675_;
v___y_665_ = v___y_673_;
v___y_666_ = v___y_674_;
v_i_667_ = v_index_683_;
goto v___jp_663_;
}
else
{
lean_dec(v___y_674_);
lean_dec(v___y_673_);
v___y_659_ = v___y_675_;
goto v___jp_658_;
}
}
}
}
v___jp_684_:
{
lean_object* v_size_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_size_689_ = lean_ctor_get(v___y_685_, 0);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_add(v_size_689_, v___x_690_);
v___x_692_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_685_, v___x_691_, v_i_688_, v___y_687_, v___y_686_);
lean_dec(v_i_688_);
v___y_659_ = v___x_692_;
goto v___jp_658_;
}
v___jp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(v_b_657_);
lean_dec_ref(v_b_657_);
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v___x_696_, v___y_695_);
switch(lean_obj_tag(v___x_697_))
{
case 0:
{
lean_object* v_index_698_; lean_object* v_size_699_; lean_object* v___x_700_; 
v_index_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_index_698_);
lean_dec_ref_known(v___x_697_, 3);
v_size_699_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_size_699_);
v___x_700_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_696_, v_size_699_, v_index_698_, v___y_695_, v___y_694_);
lean_dec(v_index_698_);
v___y_659_ = v___x_700_;
goto v___jp_658_;
}
case 1:
{
lean_object* v_index_701_; 
v_index_701_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_index_701_);
lean_dec_ref_known(v___x_697_, 1);
v___y_685_ = v___x_696_;
v___y_686_ = v___y_694_;
v___y_687_ = v___y_695_;
v_i_688_ = v_index_701_;
goto v___jp_684_;
}
default: 
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_696_, v___x_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_index_704_; 
v_index_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_index_704_);
lean_dec_ref_known(v___x_703_, 1);
v___y_685_ = v___x_696_;
v___y_686_ = v___y_694_;
v___y_687_ = v___y_695_;
v_i_688_ = v_index_704_;
goto v___jp_684_;
}
else
{
lean_dec(v___y_695_);
lean_dec(v___y_694_);
v___y_659_ = v___x_696_;
goto v___jp_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object* v_aigSize_753_, lean_object* v_assignment_754_, lean_object* v_as_755_, lean_object* v_sz_756_, lean_object* v_i_757_, lean_object* v_b_758_){
_start:
{
size_t v_sz_boxed_759_; size_t v_i_boxed_760_; lean_object* v_res_761_; 
v_sz_boxed_759_ = lean_unbox_usize(v_sz_756_);
lean_dec(v_sz_756_);
v_i_boxed_760_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_aigSize_753_, v_assignment_754_, v_as_755_, v_sz_boxed_759_, v_i_boxed_760_, v_b_758_);
lean_dec_ref(v_as_755_);
lean_dec_ref(v_assignment_754_);
lean_dec(v_aigSize_753_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9_spec__14(lean_object* v_b_762_, lean_object* v_acc_763_, lean_object* v_i_764_){
_start:
{
lean_object* v_keyArray_769_; lean_object* v_valueArray_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_keyArray_769_ = lean_ctor_get(v_b_762_, 1);
v_valueArray_770_ = lean_ctor_get(v_b_762_, 2);
v___x_771_ = lean_array_get_size(v_keyArray_769_);
v___x_772_ = lean_nat_dec_lt(v_i_764_, v___x_771_);
if (v___x_772_ == 0)
{
lean_dec(v_i_764_);
return v_acc_763_;
}
else
{
lean_object* v___x_773_; uint8_t v_isSome_774_; 
v___x_773_ = lean_array_fget_borrowed(v_keyArray_769_, v_i_764_);
v_isSome_774_ = lean_noption_is_some(v___x_773_);
if (v_isSome_774_ == 0)
{
goto v___jp_765_;
}
else
{
lean_object* v___x_775_; uint8_t v_isSome_776_; 
v___x_775_ = lean_array_fget_borrowed(v_valueArray_770_, v_i_764_);
v_isSome_776_ = lean_noption_is_some(v___x_775_);
if (v_isSome_776_ == 0)
{
goto v___jp_765_;
}
else
{
lean_object* v_val_777_; lean_object* v_val_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc(v___x_773_);
v_val_777_ = lean_noption_get(v___x_773_);
lean_inc(v___x_775_);
v_val_778_ = lean_noption_get(v___x_775_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_val_777_);
lean_ctor_set(v___x_779_, 1, v_val_778_);
v___x_780_ = lean_array_push(v_acc_763_, v___x_779_);
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_i_764_, v___x_781_);
lean_dec(v_i_764_);
v_acc_763_ = v___x_780_;
v_i_764_ = v___x_782_;
goto _start;
}
}
}
v___jp_765_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_add(v_i_764_, v___x_766_);
lean_dec(v_i_764_);
v_i_764_ = v___x_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9_spec__14___boxed(lean_object* v_b_784_, lean_object* v_acc_785_, lean_object* v_i_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9_spec__14(v_b_784_, v_acc_785_, v_i_786_);
lean_dec_ref(v_b_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object* v_init_788_, lean_object* v_b_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9_spec__14(v_b_789_, v_init_788_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object* v_init_792_, lean_object* v_b_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_init_792_, v_b_793_);
lean_dec_ref(v_b_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___lam__0(lean_object* v_atomsAssignment_795_, lean_object* v_k_796_, lean_object* v_v_797_){
_start:
{
lean_object* v_var_798_; lean_object* v___x_799_; lean_object* v_snd_800_; lean_object* v_snd_801_; uint8_t v___x_802_; 
v_var_798_ = lean_ctor_get(v_k_796_, 0);
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_795_, v_var_798_);
v_snd_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_snd_800_);
lean_dec_ref(v___x_799_);
v_snd_801_ = lean_ctor_get(v_snd_800_, 1);
lean_inc(v_snd_801_);
lean_dec(v_snd_800_);
v___x_802_ = lean_unbox(v_snd_801_);
lean_dec(v_snd_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_v_797_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; 
lean_dec(v_v_797_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___lam__0___boxed(lean_object* v_atomsAssignment_805_, lean_object* v_k_806_, lean_object* v_v_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___lam__0(v_atomsAssignment_805_, v_k_806_, v_v_807_);
lean_dec_ref(v_k_806_);
lean_dec_ref(v_atomsAssignment_805_);
return v_res_808_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = lean_noption_none();
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12(lean_object* v_atomsAssignment_810_, lean_object* v_m_811_){
_start:
{
lean_object* v_keyArray_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_keyArray_812_ = lean_ctor_get(v_m_811_, 1);
v___f_813_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___lam__0___boxed), 3, 1);
lean_closure_set(v___f_813_, 0, v_atomsAssignment_810_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_array_get_size(v_keyArray_812_);
v___x_816_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___closed__0);
v___x_817_ = lean_mk_array(v___x_815_, v___x_816_);
lean_inc_ref(v_keyArray_812_);
v___x_818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_818_, 0, v___x_814_);
lean_ctor_set(v___x_818_, 1, v_keyArray_812_);
lean_ctor_set(v___x_818_, 2, v___x_817_);
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v___f_813_, v_m_811_, v___x_818_, v___x_814_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12___boxed(lean_object* v_atomsAssignment_820_, lean_object* v_m_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12(v_atomsAssignment_820_, v_m_821_);
lean_dec_ref(v_m_821_);
return v_res_822_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0(void){
_start:
{
lean_object* v_cellCount_823_; lean_object* v___x_824_; 
v_cellCount_823_ = lean_unsigned_to_nat(16u);
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1(void){
_start:
{
lean_object* v_cellCount_825_; lean_object* v___x_826_; 
v_cellCount_825_ = lean_unsigned_to_nat(16u);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_sparseMap_830_; 
v___x_827_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1);
v___x_828_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0);
v___x_829_ = lean_unsigned_to_nat(0u);
v_sparseMap_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_sparseMap_830_, 0, v___x_829_);
lean_ctor_set(v_sparseMap_830_, 1, v___x_828_);
lean_ctor_set(v_sparseMap_830_, 2, v___x_827_);
return v_sparseMap_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object* v_var2Cnf_833_, lean_object* v_assignment_834_, lean_object* v_aigSize_835_, lean_object* v_atomsAssignment_836_){
_start:
{
lean_object* v___x_837_; lean_object* v_size_838_; lean_object* v_sparseMap_839_; lean_object* v___x_840_; lean_object* v___x_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v_size_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; size_t v_sz_849_; lean_object* v___x_850_; 
lean_inc_ref(v_atomsAssignment_836_);
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12(v_atomsAssignment_836_, v_var2Cnf_833_);
v_size_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_size_838_);
v_sparseMap_839_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2);
v___x_840_ = lean_mk_empty_array_with_capacity(v_size_838_);
lean_dec(v_size_838_);
v___x_841_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v___x_840_, v___x_837_);
lean_dec_ref(v___x_837_);
v_sz_842_ = lean_array_size(v___x_841_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_aigSize_835_, v_assignment_834_, v___x_841_, v_sz_842_, v___x_843_, v_sparseMap_839_);
lean_dec_ref(v___x_841_);
v_size_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_size_845_);
v___x_846_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__3));
v___x_847_ = lean_mk_empty_array_with_capacity(v_size_845_);
lean_dec(v_size_845_);
v___x_848_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v___x_847_, v___x_844_);
lean_dec_ref(v___x_844_);
v_sz_849_ = lean_array_size(v___x_848_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_atomsAssignment_836_, v___x_848_, v_sz_849_, v___x_843_, v___x_846_);
lean_dec_ref(v___x_848_);
lean_dec_ref(v_atomsAssignment_836_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object* v_var2Cnf_851_, lean_object* v_assignment_852_, lean_object* v_aigSize_853_, lean_object* v_atomsAssignment_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_var2Cnf_851_, v_assignment_852_, v_aigSize_853_, v_atomsAssignment_854_);
lean_dec(v_aigSize_853_);
lean_dec_ref(v_assignment_852_);
lean_dec_ref(v_var2Cnf_851_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object* v_as_856_, lean_object* v_as_x27_857_, lean_object* v_b_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_857_, v_b_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___boxed(lean_object* v_as_861_, lean_object* v_as_x27_862_, lean_object* v_b_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(v_as_861_, v_as_x27_862_, v_b_863_, v_a_864_);
lean_dec(v_as_x27_862_);
lean_dec(v_as_861_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object* v_00_u03b2_866_, lean_object* v_m_867_, lean_object* v_a_868_, lean_object* v_fallback_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_867_, v_a_868_, v_fallback_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object* v_00_u03b2_871_, lean_object* v_m_872_, lean_object* v_a_873_, lean_object* v_fallback_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_00_u03b2_871_, v_m_872_, v_a_873_, v_fallback_874_);
lean_dec(v_fallback_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_m_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object* v_00_u03b2_876_, lean_object* v_k_877_, lean_object* v_v_878_, lean_object* v_t_879_, lean_object* v_hl_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_877_, v_v_878_, v_t_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object* v_00_u03b2_882_, lean_object* v_m_883_, lean_object* v_query_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_m_883_, v_query_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___boxed(lean_object* v_00_u03b2_886_, lean_object* v_m_887_, lean_object* v_query_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(v_00_u03b2_886_, v_m_887_, v_query_888_);
lean_dec(v_query_888_);
lean_dec_ref(v_m_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object* v_00_u03b2_890_, lean_object* v_m_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___redArg(v_m_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object* v_00_u03b2_893_, lean_object* v_m_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_00_u03b2_893_, v_m_894_);
lean_dec_ref(v_m_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object* v_atomsAssignment_896_, lean_object* v_m_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_spec__12(v_atomsAssignment_896_, v_m_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object* v_atomsAssignment_899_, lean_object* v_m_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_899_, v_m_900_);
lean_dec_ref(v_m_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object* v_00_u03b2_902_, lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_m_903_, v_a_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object* v_00_u03b2_906_, lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_00_u03b2_906_, v_m_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_m_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(lean_object* v_00_u03b2_910_, lean_object* v_m_911_, lean_object* v_query_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_m_911_, v_query_912_, v_x_913_, v_x_914_, v_x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___boxed(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_query_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(v_00_u03b2_918_, v_m_919_, v_query_920_, v_x_921_, v_x_922_, v_x_923_, v_x_924_);
lean_dec(v_query_920_);
lean_dec_ref(v_m_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10(lean_object* v_00_u03b2_926_, lean_object* v_init_927_, lean_object* v_b_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___redArg(v_init_927_, v_b_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10___boxed(lean_object* v_00_u03b2_930_, lean_object* v_init_931_, lean_object* v_b_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10(v_00_u03b2_930_, v_init_931_, v_b_932_);
lean_dec_ref(v_b_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_934_, lean_object* v_m_935_, lean_object* v_query_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___redArg(v_m_935_, v_query_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_938_, lean_object* v_m_939_, lean_object* v_query_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(v_00_u03b2_938_, v_m_939_, v_query_940_);
lean_dec(v_query_940_);
lean_dec_ref(v_m_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12(lean_object* v_00_u03b2_942_, lean_object* v_b_943_, lean_object* v_acc_944_, lean_object* v_i_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___redArg(v_b_943_, v_acc_944_, v_i_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12___boxed(lean_object* v_00_u03b2_947_, lean_object* v_b_948_, lean_object* v_acc_949_, lean_object* v_i_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_spec__10_spec__12(v_00_u03b2_947_, v_b_948_, v_acc_949_, v_i_950_);
lean_dec_ref(v_b_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(lean_object* v_mvarId_952_, lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_952_, v_x_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_959_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_959_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(lean_object* v_mvarId_976_, lean_object* v_x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_976_, v_x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_object* v_00_u03b1_984_, lean_object* v_mvarId_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_985_, v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(lean_object* v_00_u03b1_993_, lean_object* v_mvarId_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(v_00_u03b1_993_, v_mvarId_994_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(lean_object* v___x_1002_, lean_object* v_x_1003_, lean_object* v_counterExample_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_st_mk_ref(v___x_1002_);
lean_inc(v___x_1010_);
v___x_1011_ = lean_apply_7(v_x_1003_, v_counterExample_1004_, v___x_1010_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, lean_box(0));
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1020_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_st_ref_get(v___x_1010_);
lean_dec(v___x_1010_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1017_ = v___x_1013_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v___x_1010_);
v_a_1021_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1011_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1011_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(lean_object* v___x_1029_, lean_object* v_x_1030_, lean_object* v_counterExample_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_1029_, v_x_1030_, v_counterExample_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v_res_1037_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0(void){
_start:
{
lean_object* v_cellCount_1038_; lean_object* v___x_1039_; 
v_cellCount_1038_ = lean_unsigned_to_nat(16u);
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1(void){
_start:
{
lean_object* v_cellCount_1040_; lean_object* v___x_1041_; 
v_cellCount_1040_ = lean_unsigned_to_nat(16u);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1);
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1043_);
lean_ctor_set(v___x_1045_, 2, v___x_1042_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3));
v___x_1049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2);
v___x_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(lean_object* v_x_1051_, lean_object* v_counterExample_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_goal_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; 
v_goal_1058_ = lean_ctor_get(v_counterExample_1052_, 0);
lean_inc(v_goal_1058_);
v___x_1059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4);
v___f_1060_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1060_, 0, v___x_1059_);
lean_closure_set(v___f_1060_, 1, v_x_1051_);
lean_closure_set(v___f_1060_, 2, v_counterExample_1052_);
v___x_1061_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_goal_1058_, v___f_1060_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(lean_object* v_x_1062_, lean_object* v_counterExample_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_1062_, v_counterExample_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(lean_object* v_a_1070_){
_start:
{
lean_object* v_unusedHypotheses_1072_; lean_object* v___x_1073_; 
v_unusedHypotheses_1072_ = lean_ctor_get(v_a_1070_, 1);
lean_inc_ref(v_unusedHypotheses_1072_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_unusedHypotheses_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_1074_);
lean_dec_ref(v_a_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_unusedHypotheses_1084_; lean_object* v___x_1085_; 
v_unusedHypotheses_1084_ = lean_ctor_get(v_a_1077_, 1);
lean_inc_ref(v_unusedHypotheses_1084_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_unusedHypotheses_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(lean_object* v_a_1094_){
_start:
{
lean_object* v_equations_1096_; lean_object* v___x_1097_; 
v_equations_1096_ = lean_ctor_get(v_a_1094_, 2);
lean_inc_ref(v_equations_1096_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_equations_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_1098_);
lean_dec_ref(v_a_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_equations_1108_; lean_object* v___x_1109_; 
v_equations_1108_ = lean_ctor_get(v_a_1101_, 2);
lean_inc_ref(v_equations_1108_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_equations_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(lean_object* v_e_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v_uninterpretedSymbols_1124_; lean_object* v_unusedRelevantHypotheses_1125_; lean_object* v_derivedEquations_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1201_; 
v___x_1123_ = lean_st_ref_take(v_a_1121_);
v_uninterpretedSymbols_1124_ = lean_ctor_get(v___x_1123_, 0);
v_unusedRelevantHypotheses_1125_ = lean_ctor_get(v___x_1123_, 1);
v_derivedEquations_1126_ = lean_ctor_get(v___x_1123_, 2);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1128_ = v___x_1123_;
v_isShared_1129_ = v_isSharedCheck_1201_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_derivedEquations_1126_);
lean_inc(v_unusedRelevantHypotheses_1125_);
lean_inc(v_uninterpretedSymbols_1124_);
lean_dec(v___x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1201_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___y_1134_; lean_object* v___y_1141_; lean_object* v_i_1142_; lean_object* v___y_1148_; lean_object* v___y_1158_; lean_object* v_i_1159_; lean_object* v___x_1174_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1132_ = lean_box(0);
lean_inc_ref(v_e_1120_);
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1130_, v___x_1131_, v_uninterpretedSymbols_1124_, v_e_1120_);
switch(lean_obj_tag(v___x_1174_))
{
case 0:
{
lean_dec_ref_known(v___x_1174_, 3);
lean_dec_ref(v_e_1120_);
v___y_1134_ = v_uninterpretedSymbols_1124_;
goto v___jp_1133_;
}
case 1:
{
lean_object* v_index_1175_; lean_object* v_size_1176_; lean_object* v_keyArray_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_index_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_index_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v_size_1176_ = lean_ctor_get(v_uninterpretedSymbols_1124_, 0);
v_keyArray_1177_ = lean_ctor_get(v_uninterpretedSymbols_1124_, 1);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_size_1176_, v___x_1178_);
v___x_1180_ = lean_array_get_size(v_keyArray_1177_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_index_1175_);
goto v___jp_1164_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1182_ = lean_unsigned_to_nat(4u);
v___x_1183_ = lean_nat_mul(v___x_1179_, v___x_1182_);
v___x_1184_ = lean_unsigned_to_nat(3u);
v___x_1185_ = lean_nat_mul(v___x_1180_, v___x_1184_);
v___x_1186_ = lean_nat_dec_le(v___x_1183_, v___x_1185_);
lean_dec(v___x_1185_);
lean_dec(v___x_1183_);
if (v___x_1186_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_index_1175_);
goto v___jp_1164_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DHashMap_Raw_setEntry___redArg(v_uninterpretedSymbols_1124_, v___x_1179_, v_index_1175_, v_e_1120_, v___x_1132_);
lean_dec(v_index_1175_);
v___y_1134_ = v___x_1187_;
goto v___jp_1133_;
}
}
}
default: 
{
lean_object* v_size_1188_; lean_object* v_keyArray_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_size_1188_ = lean_ctor_get(v_uninterpretedSymbols_1124_, 0);
v_keyArray_1189_ = lean_ctor_get(v_uninterpretedSymbols_1124_, 1);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_size_1188_, v___x_1190_);
v___x_1192_ = lean_array_get_size(v_keyArray_1189_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v___x_1191_);
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1130_, v___x_1131_, v_uninterpretedSymbols_1124_);
v___y_1148_ = v___x_1194_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1195_ = lean_unsigned_to_nat(4u);
v___x_1196_ = lean_nat_mul(v___x_1191_, v___x_1195_);
lean_dec(v___x_1191_);
v___x_1197_ = lean_unsigned_to_nat(3u);
v___x_1198_ = lean_nat_mul(v___x_1192_, v___x_1197_);
v___x_1199_ = lean_nat_dec_le(v___x_1196_, v___x_1198_);
lean_dec(v___x_1198_);
lean_dec(v___x_1196_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1130_, v___x_1131_, v_uninterpretedSymbols_1124_);
v___y_1148_ = v___x_1200_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v_uninterpretedSymbols_1124_;
goto v___jp_1147_;
}
}
}
}
v___jp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___y_1134_);
v___x_1136_ = v___x_1128_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___y_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_unusedRelevantHypotheses_1125_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_derivedEquations_1126_);
v___x_1136_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_st_ref_put(v_a_1121_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1132_);
return v___x_1138_;
}
}
v___jp_1140_:
{
lean_object* v_size_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_size_1143_ = lean_ctor_get(v___y_1141_, 0);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_size_1143_, v___x_1144_);
v___x_1146_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1141_, v___x_1145_, v_i_1142_, v_e_1120_, v___x_1132_);
lean_dec(v_i_1142_);
v___y_1134_ = v___x_1146_;
goto v___jp_1133_;
}
v___jp_1147_:
{
lean_object* v___x_1149_; 
lean_inc_ref(v_e_1120_);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1130_, v___x_1131_, v___y_1148_, v_e_1120_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
lean_object* v_index_1150_; lean_object* v_size_1151_; lean_object* v___x_1152_; 
v_index_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_index_1150_);
lean_dec_ref_known(v___x_1149_, 3);
v_size_1151_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_size_1151_);
v___x_1152_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1148_, v_size_1151_, v_index_1150_, v_e_1120_, v___x_1132_);
lean_dec(v_index_1150_);
v___y_1134_ = v___x_1152_;
goto v___jp_1133_;
}
case 1:
{
lean_object* v_index_1153_; 
v_index_1153_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_index_1153_);
lean_dec_ref_known(v___x_1149_, 1);
v___y_1141_ = v___y_1148_;
v_i_1142_ = v_index_1153_;
goto v___jp_1140_;
}
default: 
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1148_, v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_index_1156_; 
v_index_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_index_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___y_1141_ = v___y_1148_;
v_i_1142_ = v_index_1156_;
goto v___jp_1140_;
}
else
{
lean_dec_ref(v_e_1120_);
v___y_1134_ = v___y_1148_;
goto v___jp_1133_;
}
}
}
}
v___jp_1157_:
{
lean_object* v_size_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_size_1160_ = lean_ctor_get(v___y_1158_, 0);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_size_1160_, v___x_1161_);
v___x_1163_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1158_, v___x_1162_, v_i_1159_, v_e_1120_, v___x_1132_);
lean_dec(v_i_1159_);
v___y_1134_ = v___x_1163_;
goto v___jp_1133_;
}
v___jp_1164_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1130_, v___x_1131_, v_uninterpretedSymbols_1124_);
lean_inc_ref(v_e_1120_);
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1130_, v___x_1131_, v___x_1165_, v_e_1120_);
switch(lean_obj_tag(v___x_1166_))
{
case 0:
{
lean_object* v_index_1167_; lean_object* v_size_1168_; lean_object* v___x_1169_; 
v_index_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_index_1167_);
lean_dec_ref_known(v___x_1166_, 3);
v_size_1168_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_size_1168_);
v___x_1169_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1165_, v_size_1168_, v_index_1167_, v_e_1120_, v___x_1132_);
lean_dec(v_index_1167_);
v___y_1134_ = v___x_1169_;
goto v___jp_1133_;
}
case 1:
{
lean_object* v_index_1170_; 
v_index_1170_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_index_1170_);
lean_dec_ref_known(v___x_1166_, 1);
v___y_1158_ = v___x_1165_;
v_i_1159_ = v_index_1170_;
goto v___jp_1157_;
}
default: 
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1165_, v___x_1171_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_index_1173_; 
v_index_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_index_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___y_1158_ = v___x_1165_;
v_i_1159_ = v_index_1173_;
goto v___jp_1157_;
}
else
{
lean_dec_ref(v_e_1120_);
v___y_1134_ = v___x_1165_;
goto v___jp_1133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object* v_e_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_1202_, v_a_1203_);
lean_dec(v_a_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(lean_object* v_e_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_uninterpretedSymbols_1215_; lean_object* v_unusedRelevantHypotheses_1216_; lean_object* v_derivedEquations_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1292_; 
v___x_1214_ = lean_st_ref_take(v_a_1208_);
v_uninterpretedSymbols_1215_ = lean_ctor_get(v___x_1214_, 0);
v_unusedRelevantHypotheses_1216_ = lean_ctor_get(v___x_1214_, 1);
v_derivedEquations_1217_ = lean_ctor_get(v___x_1214_, 2);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1219_ = v___x_1214_;
v_isShared_1220_ = v_isSharedCheck_1292_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_derivedEquations_1217_);
lean_inc(v_unusedRelevantHypotheses_1216_);
lean_inc(v_uninterpretedSymbols_1215_);
lean_dec(v___x_1214_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1292_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___y_1225_; lean_object* v___y_1232_; lean_object* v_i_1233_; lean_object* v___y_1239_; lean_object* v___y_1249_; lean_object* v_i_1250_; lean_object* v___x_1265_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1223_ = lean_box(0);
lean_inc_ref(v_e_1206_);
v___x_1265_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1221_, v___x_1222_, v_uninterpretedSymbols_1215_, v_e_1206_);
switch(lean_obj_tag(v___x_1265_))
{
case 0:
{
lean_dec_ref_known(v___x_1265_, 3);
lean_dec_ref(v_e_1206_);
v___y_1225_ = v_uninterpretedSymbols_1215_;
goto v___jp_1224_;
}
case 1:
{
lean_object* v_index_1266_; lean_object* v_size_1267_; lean_object* v_keyArray_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_index_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_index_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v_size_1267_ = lean_ctor_get(v_uninterpretedSymbols_1215_, 0);
v_keyArray_1268_ = lean_ctor_get(v_uninterpretedSymbols_1215_, 1);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v_size_1267_, v___x_1269_);
v___x_1271_ = lean_array_get_size(v_keyArray_1268_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v___x_1270_);
lean_dec(v_index_1266_);
goto v___jp_1255_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1273_ = lean_unsigned_to_nat(4u);
v___x_1274_ = lean_nat_mul(v___x_1270_, v___x_1273_);
v___x_1275_ = lean_unsigned_to_nat(3u);
v___x_1276_ = lean_nat_mul(v___x_1271_, v___x_1275_);
v___x_1277_ = lean_nat_dec_le(v___x_1274_, v___x_1276_);
lean_dec(v___x_1276_);
lean_dec(v___x_1274_);
if (v___x_1277_ == 0)
{
lean_dec(v___x_1270_);
lean_dec(v_index_1266_);
goto v___jp_1255_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Raw_setEntry___redArg(v_uninterpretedSymbols_1215_, v___x_1270_, v_index_1266_, v_e_1206_, v___x_1223_);
lean_dec(v_index_1266_);
v___y_1225_ = v___x_1278_;
goto v___jp_1224_;
}
}
}
default: 
{
lean_object* v_size_1279_; lean_object* v_keyArray_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_size_1279_ = lean_ctor_get(v_uninterpretedSymbols_1215_, 0);
v_keyArray_1280_ = lean_ctor_get(v_uninterpretedSymbols_1215_, 1);
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v_size_1279_, v___x_1281_);
v___x_1283_ = lean_array_get_size(v_keyArray_1280_);
v___x_1284_ = lean_nat_dec_lt(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec(v___x_1282_);
v___x_1285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1221_, v___x_1222_, v_uninterpretedSymbols_1215_);
v___y_1239_ = v___x_1285_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1286_ = lean_unsigned_to_nat(4u);
v___x_1287_ = lean_nat_mul(v___x_1282_, v___x_1286_);
lean_dec(v___x_1282_);
v___x_1288_ = lean_unsigned_to_nat(3u);
v___x_1289_ = lean_nat_mul(v___x_1283_, v___x_1288_);
v___x_1290_ = lean_nat_dec_le(v___x_1287_, v___x_1289_);
lean_dec(v___x_1289_);
lean_dec(v___x_1287_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1221_, v___x_1222_, v_uninterpretedSymbols_1215_);
v___y_1239_ = v___x_1291_;
goto v___jp_1238_;
}
else
{
v___y_1239_ = v_uninterpretedSymbols_1215_;
goto v___jp_1238_;
}
}
}
}
v___jp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___y_1225_);
v___x_1227_ = v___x_1219_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___y_1225_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_unusedRelevantHypotheses_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_derivedEquations_1217_);
v___x_1227_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_st_ref_put(v_a_1208_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1223_);
return v___x_1229_;
}
}
v___jp_1231_:
{
lean_object* v_size_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_size_1234_ = lean_ctor_get(v___y_1232_, 0);
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_size_1234_, v___x_1235_);
v___x_1237_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1232_, v___x_1236_, v_i_1233_, v_e_1206_, v___x_1223_);
lean_dec(v_i_1233_);
v___y_1225_ = v___x_1237_;
goto v___jp_1224_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; 
lean_inc_ref(v_e_1206_);
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1221_, v___x_1222_, v___y_1239_, v_e_1206_);
switch(lean_obj_tag(v___x_1240_))
{
case 0:
{
lean_object* v_index_1241_; lean_object* v_size_1242_; lean_object* v___x_1243_; 
v_index_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_index_1241_);
lean_dec_ref_known(v___x_1240_, 3);
v_size_1242_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_size_1242_);
v___x_1243_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1239_, v_size_1242_, v_index_1241_, v_e_1206_, v___x_1223_);
lean_dec(v_index_1241_);
v___y_1225_ = v___x_1243_;
goto v___jp_1224_;
}
case 1:
{
lean_object* v_index_1244_; 
v_index_1244_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_index_1244_);
lean_dec_ref_known(v___x_1240_, 1);
v___y_1232_ = v___y_1239_;
v_i_1233_ = v_index_1244_;
goto v___jp_1231_;
}
default: 
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1239_, v___x_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_index_1247_; 
v_index_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_index_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___y_1232_ = v___y_1239_;
v_i_1233_ = v_index_1247_;
goto v___jp_1231_;
}
else
{
lean_dec_ref(v_e_1206_);
v___y_1225_ = v___y_1239_;
goto v___jp_1224_;
}
}
}
}
v___jp_1248_:
{
lean_object* v_size_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_size_1251_ = lean_ctor_get(v___y_1249_, 0);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_add(v_size_1251_, v___x_1252_);
v___x_1254_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1249_, v___x_1253_, v_i_1250_, v_e_1206_, v___x_1223_);
lean_dec(v_i_1250_);
v___y_1225_ = v___x_1254_;
goto v___jp_1224_;
}
v___jp_1255_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1221_, v___x_1222_, v_uninterpretedSymbols_1215_);
lean_inc_ref(v_e_1206_);
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1221_, v___x_1222_, v___x_1256_, v_e_1206_);
switch(lean_obj_tag(v___x_1257_))
{
case 0:
{
lean_object* v_index_1258_; lean_object* v_size_1259_; lean_object* v___x_1260_; 
v_index_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_index_1258_);
lean_dec_ref_known(v___x_1257_, 3);
v_size_1259_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_size_1259_);
v___x_1260_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1256_, v_size_1259_, v_index_1258_, v_e_1206_, v___x_1223_);
lean_dec(v_index_1258_);
v___y_1225_ = v___x_1260_;
goto v___jp_1224_;
}
case 1:
{
lean_object* v_index_1261_; 
v_index_1261_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_index_1261_);
lean_dec_ref_known(v___x_1257_, 1);
v___y_1249_ = v___x_1256_;
v_i_1250_ = v_index_1261_;
goto v___jp_1248_;
}
default: 
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1256_, v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_index_1264_; 
v_index_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_index_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___y_1249_ = v___x_1256_;
v_i_1250_ = v_index_1264_;
goto v___jp_1248_;
}
else
{
lean_dec_ref(v_e_1206_);
v___y_1225_ = v___x_1256_;
goto v___jp_1224_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object* v_hyp_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v_uninterpretedSymbols_1308_; lean_object* v_unusedRelevantHypotheses_1309_; lean_object* v_derivedEquations_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1385_; 
v___x_1307_ = lean_st_ref_take(v_a_1305_);
v_uninterpretedSymbols_1308_ = lean_ctor_get(v___x_1307_, 0);
v_unusedRelevantHypotheses_1309_ = lean_ctor_get(v___x_1307_, 1);
v_derivedEquations_1310_ = lean_ctor_get(v___x_1307_, 2);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1312_ = v___x_1307_;
v_isShared_1313_ = v_isSharedCheck_1385_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_derivedEquations_1310_);
lean_inc(v_unusedRelevantHypotheses_1309_);
lean_inc(v_uninterpretedSymbols_1308_);
lean_dec(v___x_1307_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1385_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; lean_object* v___y_1318_; lean_object* v___y_1325_; lean_object* v_i_1326_; lean_object* v___y_1332_; lean_object* v___y_1342_; lean_object* v_i_1343_; lean_object* v___x_1358_; 
v___f_1314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1316_ = lean_box(0);
lean_inc_ref(v_hyp_1304_);
v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1314_, v___f_1315_, v_unusedRelevantHypotheses_1309_, v_hyp_1304_);
switch(lean_obj_tag(v___x_1358_))
{
case 0:
{
lean_dec_ref_known(v___x_1358_, 3);
lean_dec_ref(v_hyp_1304_);
v___y_1318_ = v_unusedRelevantHypotheses_1309_;
goto v___jp_1317_;
}
case 1:
{
lean_object* v_index_1359_; lean_object* v_size_1360_; lean_object* v_keyArray_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_index_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_index_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v_size_1360_ = lean_ctor_get(v_unusedRelevantHypotheses_1309_, 0);
v_keyArray_1361_ = lean_ctor_get(v_unusedRelevantHypotheses_1309_, 1);
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_add(v_size_1360_, v___x_1362_);
v___x_1364_ = lean_array_get_size(v_keyArray_1361_);
v___x_1365_ = lean_nat_dec_lt(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec(v___x_1363_);
lean_dec(v_index_1359_);
goto v___jp_1348_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1366_ = lean_unsigned_to_nat(4u);
v___x_1367_ = lean_nat_mul(v___x_1363_, v___x_1366_);
v___x_1368_ = lean_unsigned_to_nat(3u);
v___x_1369_ = lean_nat_mul(v___x_1364_, v___x_1368_);
v___x_1370_ = lean_nat_dec_le(v___x_1367_, v___x_1369_);
lean_dec(v___x_1369_);
lean_dec(v___x_1367_);
if (v___x_1370_ == 0)
{
lean_dec(v___x_1363_);
lean_dec(v_index_1359_);
goto v___jp_1348_;
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DHashMap_Raw_setEntry___redArg(v_unusedRelevantHypotheses_1309_, v___x_1363_, v_index_1359_, v_hyp_1304_, v___x_1316_);
lean_dec(v_index_1359_);
v___y_1318_ = v___x_1371_;
goto v___jp_1317_;
}
}
}
default: 
{
lean_object* v_size_1372_; lean_object* v_keyArray_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_size_1372_ = lean_ctor_get(v_unusedRelevantHypotheses_1309_, 0);
v_keyArray_1373_ = lean_ctor_get(v_unusedRelevantHypotheses_1309_, 1);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_add(v_size_1372_, v___x_1374_);
v___x_1376_ = lean_array_get_size(v_keyArray_1373_);
v___x_1377_ = lean_nat_dec_lt(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec(v___x_1375_);
v___x_1378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1314_, v___f_1315_, v_unusedRelevantHypotheses_1309_);
v___y_1332_ = v___x_1378_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1379_ = lean_unsigned_to_nat(4u);
v___x_1380_ = lean_nat_mul(v___x_1375_, v___x_1379_);
lean_dec(v___x_1375_);
v___x_1381_ = lean_unsigned_to_nat(3u);
v___x_1382_ = lean_nat_mul(v___x_1376_, v___x_1381_);
v___x_1383_ = lean_nat_dec_le(v___x_1380_, v___x_1382_);
lean_dec(v___x_1382_);
lean_dec(v___x_1380_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1314_, v___f_1315_, v_unusedRelevantHypotheses_1309_);
v___y_1332_ = v___x_1384_;
goto v___jp_1331_;
}
else
{
v___y_1332_ = v_unusedRelevantHypotheses_1309_;
goto v___jp_1331_;
}
}
}
}
v___jp_1317_:
{
lean_object* v___x_1320_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___y_1318_);
v___x_1320_ = v___x_1312_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_uninterpretedSymbols_1308_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___y_1318_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_derivedEquations_1310_);
v___x_1320_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_st_ref_put(v_a_1305_, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1316_);
return v___x_1322_;
}
}
v___jp_1324_:
{
lean_object* v_size_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_size_1327_ = lean_ctor_get(v___y_1325_, 0);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_size_1327_, v___x_1328_);
v___x_1330_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1325_, v___x_1329_, v_i_1326_, v_hyp_1304_, v___x_1316_);
lean_dec(v_i_1326_);
v___y_1318_ = v___x_1330_;
goto v___jp_1317_;
}
v___jp_1331_:
{
lean_object* v___x_1333_; 
lean_inc_ref(v_hyp_1304_);
v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1314_, v___f_1315_, v___y_1332_, v_hyp_1304_);
switch(lean_obj_tag(v___x_1333_))
{
case 0:
{
lean_object* v_index_1334_; lean_object* v_size_1335_; lean_object* v___x_1336_; 
v_index_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_index_1334_);
lean_dec_ref_known(v___x_1333_, 3);
v_size_1335_ = lean_ctor_get(v___y_1332_, 0);
lean_inc(v_size_1335_);
v___x_1336_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1332_, v_size_1335_, v_index_1334_, v_hyp_1304_, v___x_1316_);
lean_dec(v_index_1334_);
v___y_1318_ = v___x_1336_;
goto v___jp_1317_;
}
case 1:
{
lean_object* v_index_1337_; 
v_index_1337_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_index_1337_);
lean_dec_ref_known(v___x_1333_, 1);
v___y_1325_ = v___y_1332_;
v_i_1326_ = v_index_1337_;
goto v___jp_1324_;
}
default: 
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1332_, v___x_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_index_1340_; 
v_index_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_index_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v___y_1325_ = v___y_1332_;
v_i_1326_ = v_index_1340_;
goto v___jp_1324_;
}
else
{
lean_dec_ref(v_hyp_1304_);
v___y_1318_ = v___y_1332_;
goto v___jp_1317_;
}
}
}
}
v___jp_1341_:
{
lean_object* v_size_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_size_1344_ = lean_ctor_get(v___y_1342_, 0);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_nat_add(v_size_1344_, v___x_1345_);
v___x_1347_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1342_, v___x_1346_, v_i_1343_, v_hyp_1304_, v___x_1316_);
lean_dec(v_i_1343_);
v___y_1318_ = v___x_1347_;
goto v___jp_1317_;
}
v___jp_1348_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1314_, v___f_1315_, v_unusedRelevantHypotheses_1309_);
lean_inc_ref(v_hyp_1304_);
v___x_1350_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1314_, v___f_1315_, v___x_1349_, v_hyp_1304_);
switch(lean_obj_tag(v___x_1350_))
{
case 0:
{
lean_object* v_index_1351_; lean_object* v_size_1352_; lean_object* v___x_1353_; 
v_index_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_index_1351_);
lean_dec_ref_known(v___x_1350_, 3);
v_size_1352_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_size_1352_);
v___x_1353_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1349_, v_size_1352_, v_index_1351_, v_hyp_1304_, v___x_1316_);
lean_dec(v_index_1351_);
v___y_1318_ = v___x_1353_;
goto v___jp_1317_;
}
case 1:
{
lean_object* v_index_1354_; 
v_index_1354_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_index_1354_);
lean_dec_ref_known(v___x_1350_, 1);
v___y_1342_ = v___x_1349_;
v_i_1343_ = v_index_1354_;
goto v___jp_1341_;
}
default: 
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1349_, v___x_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_index_1357_; 
v_index_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_index_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___y_1342_ = v___x_1349_;
v_i_1343_ = v_index_1357_;
goto v___jp_1341_;
}
else
{
lean_dec_ref(v_hyp_1304_);
v___y_1318_ = v___x_1349_;
goto v___jp_1317_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object* v_hyp_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_hyp_1386_, v_a_1387_);
lean_dec(v_a_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(lean_object* v_hyp_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v_uninterpretedSymbols_1399_; lean_object* v_unusedRelevantHypotheses_1400_; lean_object* v_derivedEquations_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1476_; 
v___x_1398_ = lean_st_ref_take(v_a_1392_);
v_uninterpretedSymbols_1399_ = lean_ctor_get(v___x_1398_, 0);
v_unusedRelevantHypotheses_1400_ = lean_ctor_get(v___x_1398_, 1);
v_derivedEquations_1401_ = lean_ctor_get(v___x_1398_, 2);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1403_ = v___x_1398_;
v_isShared_1404_ = v_isSharedCheck_1476_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_derivedEquations_1401_);
lean_inc(v_unusedRelevantHypotheses_1400_);
lean_inc(v_uninterpretedSymbols_1399_);
lean_dec(v___x_1398_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1476_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___f_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1416_; lean_object* v_i_1417_; lean_object* v___y_1423_; lean_object* v___y_1433_; lean_object* v_i_1434_; lean_object* v___x_1449_; 
v___f_1405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1407_ = lean_box(0);
lean_inc_ref(v_hyp_1390_);
v___x_1449_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1405_, v___f_1406_, v_unusedRelevantHypotheses_1400_, v_hyp_1390_);
switch(lean_obj_tag(v___x_1449_))
{
case 0:
{
lean_dec_ref_known(v___x_1449_, 3);
lean_dec_ref(v_hyp_1390_);
v___y_1409_ = v_unusedRelevantHypotheses_1400_;
goto v___jp_1408_;
}
case 1:
{
lean_object* v_index_1450_; lean_object* v_size_1451_; lean_object* v_keyArray_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_index_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_index_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v_size_1451_ = lean_ctor_get(v_unusedRelevantHypotheses_1400_, 0);
v_keyArray_1452_ = lean_ctor_get(v_unusedRelevantHypotheses_1400_, 1);
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_add(v_size_1451_, v___x_1453_);
v___x_1455_ = lean_array_get_size(v_keyArray_1452_);
v___x_1456_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_dec(v___x_1454_);
lean_dec(v_index_1450_);
goto v___jp_1439_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1457_ = lean_unsigned_to_nat(4u);
v___x_1458_ = lean_nat_mul(v___x_1454_, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(3u);
v___x_1460_ = lean_nat_mul(v___x_1455_, v___x_1459_);
v___x_1461_ = lean_nat_dec_le(v___x_1458_, v___x_1460_);
lean_dec(v___x_1460_);
lean_dec(v___x_1458_);
if (v___x_1461_ == 0)
{
lean_dec(v___x_1454_);
lean_dec(v_index_1450_);
goto v___jp_1439_;
}
else
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Raw_setEntry___redArg(v_unusedRelevantHypotheses_1400_, v___x_1454_, v_index_1450_, v_hyp_1390_, v___x_1407_);
lean_dec(v_index_1450_);
v___y_1409_ = v___x_1462_;
goto v___jp_1408_;
}
}
}
default: 
{
lean_object* v_size_1463_; lean_object* v_keyArray_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_size_1463_ = lean_ctor_get(v_unusedRelevantHypotheses_1400_, 0);
v_keyArray_1464_ = lean_ctor_get(v_unusedRelevantHypotheses_1400_, 1);
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v_size_1463_, v___x_1465_);
v___x_1467_ = lean_array_get_size(v_keyArray_1464_);
v___x_1468_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec(v___x_1466_);
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1405_, v___f_1406_, v_unusedRelevantHypotheses_1400_);
v___y_1423_ = v___x_1469_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1470_ = lean_unsigned_to_nat(4u);
v___x_1471_ = lean_nat_mul(v___x_1466_, v___x_1470_);
lean_dec(v___x_1466_);
v___x_1472_ = lean_unsigned_to_nat(3u);
v___x_1473_ = lean_nat_mul(v___x_1467_, v___x_1472_);
v___x_1474_ = lean_nat_dec_le(v___x_1471_, v___x_1473_);
lean_dec(v___x_1473_);
lean_dec(v___x_1471_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1405_, v___f_1406_, v_unusedRelevantHypotheses_1400_);
v___y_1423_ = v___x_1475_;
goto v___jp_1422_;
}
else
{
v___y_1423_ = v_unusedRelevantHypotheses_1400_;
goto v___jp_1422_;
}
}
}
}
v___jp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___y_1409_);
v___x_1411_ = v___x_1403_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_uninterpretedSymbols_1399_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___y_1409_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_derivedEquations_1401_);
v___x_1411_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_st_ref_put(v_a_1392_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1407_);
return v___x_1413_;
}
}
v___jp_1415_:
{
lean_object* v_size_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_size_1418_ = lean_ctor_get(v___y_1416_, 0);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_size_1418_, v___x_1419_);
v___x_1421_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1416_, v___x_1420_, v_i_1417_, v_hyp_1390_, v___x_1407_);
lean_dec(v_i_1417_);
v___y_1409_ = v___x_1421_;
goto v___jp_1408_;
}
v___jp_1422_:
{
lean_object* v___x_1424_; 
lean_inc_ref(v_hyp_1390_);
v___x_1424_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1405_, v___f_1406_, v___y_1423_, v_hyp_1390_);
switch(lean_obj_tag(v___x_1424_))
{
case 0:
{
lean_object* v_index_1425_; lean_object* v_size_1426_; lean_object* v___x_1427_; 
v_index_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_index_1425_);
lean_dec_ref_known(v___x_1424_, 3);
v_size_1426_ = lean_ctor_get(v___y_1423_, 0);
lean_inc(v_size_1426_);
v___x_1427_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1423_, v_size_1426_, v_index_1425_, v_hyp_1390_, v___x_1407_);
lean_dec(v_index_1425_);
v___y_1409_ = v___x_1427_;
goto v___jp_1408_;
}
case 1:
{
lean_object* v_index_1428_; 
v_index_1428_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_index_1428_);
lean_dec_ref_known(v___x_1424_, 1);
v___y_1416_ = v___y_1423_;
v_i_1417_ = v_index_1428_;
goto v___jp_1415_;
}
default: 
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1423_, v___x_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_index_1431_; 
v_index_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_index_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___y_1416_ = v___y_1423_;
v_i_1417_ = v_index_1431_;
goto v___jp_1415_;
}
else
{
lean_dec_ref(v_hyp_1390_);
v___y_1409_ = v___y_1423_;
goto v___jp_1408_;
}
}
}
}
v___jp_1432_:
{
lean_object* v_size_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_size_1435_ = lean_ctor_get(v___y_1433_, 0);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_add(v_size_1435_, v___x_1436_);
v___x_1438_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1433_, v___x_1437_, v_i_1434_, v_hyp_1390_, v___x_1407_);
lean_dec(v_i_1434_);
v___y_1409_ = v___x_1438_;
goto v___jp_1408_;
}
v___jp_1439_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1405_, v___f_1406_, v_unusedRelevantHypotheses_1400_);
lean_inc_ref(v_hyp_1390_);
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1405_, v___f_1406_, v___x_1440_, v_hyp_1390_);
switch(lean_obj_tag(v___x_1441_))
{
case 0:
{
lean_object* v_index_1442_; lean_object* v_size_1443_; lean_object* v___x_1444_; 
v_index_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_index_1442_);
lean_dec_ref_known(v___x_1441_, 3);
v_size_1443_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_size_1443_);
v___x_1444_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1440_, v_size_1443_, v_index_1442_, v_hyp_1390_, v___x_1407_);
lean_dec(v_index_1442_);
v___y_1409_ = v___x_1444_;
goto v___jp_1408_;
}
case 1:
{
lean_object* v_index_1445_; 
v_index_1445_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_index_1445_);
lean_dec_ref_known(v___x_1441_, 1);
v___y_1433_ = v___x_1440_;
v_i_1434_ = v_index_1445_;
goto v___jp_1432_;
}
default: 
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1440_, v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_index_1448_; 
v_index_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_index_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___y_1433_ = v___x_1440_;
v_i_1434_ = v_index_1448_;
goto v___jp_1432_;
}
else
{
lean_dec_ref(v_hyp_1390_);
v___y_1409_ = v___x_1440_;
goto v___jp_1408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object* v_hyp_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_hyp_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(lean_object* v_var_1486_, lean_object* v_value_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v_uninterpretedSymbols_1491_; lean_object* v_unusedRelevantHypotheses_1492_; lean_object* v_derivedEquations_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1505_; 
v___x_1490_ = lean_st_ref_take(v_a_1488_);
v_uninterpretedSymbols_1491_ = lean_ctor_get(v___x_1490_, 0);
v_unusedRelevantHypotheses_1492_ = lean_ctor_get(v___x_1490_, 1);
v_derivedEquations_1493_ = lean_ctor_get(v___x_1490_, 2);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1495_ = v___x_1490_;
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_derivedEquations_1493_);
lean_inc(v_unusedRelevantHypotheses_1492_);
lean_inc(v_uninterpretedSymbols_1491_);
lean_dec(v___x_1490_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_var_1486_);
lean_ctor_set(v___x_1497_, 1, v_value_1487_);
v___x_1498_ = lean_array_push(v_derivedEquations_1493_, v___x_1497_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 2, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_uninterpretedSymbols_1491_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_unusedRelevantHypotheses_1492_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_st_ref_put(v_a_1488_, v___x_1500_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object* v_var_1506_, lean_object* v_value_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_1506_, v_value_1507_, v_a_1508_);
lean_dec(v_a_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(lean_object* v_var_1511_, lean_object* v_value_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v_uninterpretedSymbols_1521_; lean_object* v_unusedRelevantHypotheses_1522_; lean_object* v_derivedEquations_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1535_; 
v___x_1520_ = lean_st_ref_take(v_a_1514_);
v_uninterpretedSymbols_1521_ = lean_ctor_get(v___x_1520_, 0);
v_unusedRelevantHypotheses_1522_ = lean_ctor_get(v___x_1520_, 1);
v_derivedEquations_1523_ = lean_ctor_get(v___x_1520_, 2);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1525_ = v___x_1520_;
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_derivedEquations_1523_);
lean_inc(v_unusedRelevantHypotheses_1522_);
lean_inc(v_uninterpretedSymbols_1521_);
lean_dec(v___x_1520_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_var_1511_);
lean_ctor_set(v___x_1527_, 1, v_value_1512_);
v___x_1528_ = lean_array_push(v_derivedEquations_1523_, v___x_1527_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 2, v___x_1528_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_uninterpretedSymbols_1521_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_unusedRelevantHypotheses_1522_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_st_ref_put(v_a_1514_, v___x_1530_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(lean_object* v_var_1536_, lean_object* v_value_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_1536_, v_value_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object* v_m_1546_, lean_object* v_query_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_){
_start:
{
lean_object* v_zero_1551_; uint8_t v_isZero_1552_; 
v_zero_1551_ = lean_unsigned_to_nat(0u);
v_isZero_1552_ = lean_nat_dec_eq(v_x_1549_, v_zero_1551_);
if (v_isZero_1552_ == 1)
{
lean_dec(v_x_1550_);
lean_dec(v_x_1549_);
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_box(2);
return v___x_1553_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_val_1554_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v_x_1548_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v_x_1548_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_val_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_keyArray_1562_; lean_object* v_valueArray_1563_; lean_object* v___x_1564_; uint8_t v_isSome_1565_; 
v_keyArray_1562_ = lean_ctor_get(v_m_1546_, 1);
v_valueArray_1563_ = lean_ctor_get(v_m_1546_, 2);
v___x_1564_ = lean_array_fget_borrowed(v_keyArray_1562_, v_x_1550_);
v_isSome_1565_ = lean_noption_is_some(v___x_1564_);
if (v_isSome_1565_ == 0)
{
lean_dec(v_x_1549_);
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_x_1550_);
return v___x_1566_;
}
else
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_x_1550_);
v_val_1567_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v_x_1548_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v_x_1548_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_val_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_one_1575_; lean_object* v_n_1576_; lean_object* v___y_1578_; 
v_one_1575_ = lean_unsigned_to_nat(1u);
v_n_1576_ = lean_nat_sub(v_x_1549_, v_one_1575_);
lean_dec(v_x_1549_);
if (v_isSome_1565_ == 0)
{
goto v___jp_1584_;
}
else
{
lean_object* v___x_1586_; uint8_t v_isSome_1587_; 
v___x_1586_ = lean_array_fget_borrowed(v_valueArray_1563_, v_x_1550_);
v_isSome_1587_ = lean_noption_is_some(v___x_1586_);
if (v_isSome_1587_ == 0)
{
goto v___jp_1584_;
}
else
{
lean_object* v_val_1588_; lean_object* v_type_1589_; lean_object* v_type_1590_; uint8_t v___x_1591_; 
lean_inc(v___x_1564_);
v_val_1588_ = lean_noption_get(v___x_1564_);
v_type_1589_ = lean_ctor_get(v_val_1588_, 1);
lean_inc_ref(v_type_1589_);
v_type_1590_ = lean_ctor_get(v_query_1547_, 1);
v___x_1591_ = lean_expr_eqv(v_type_1589_, v_type_1590_);
lean_dec_ref(v_type_1589_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
lean_dec(v_val_1588_);
v___x_1592_ = lean_array_get_size(v_keyArray_1562_);
v___x_1593_ = lean_nat_add(v_x_1550_, v_one_1575_);
lean_dec(v_x_1550_);
v___x_1594_ = lean_nat_dec_lt(v___x_1593_, v___x_1592_);
if (v___x_1594_ == 0)
{
lean_dec(v___x_1593_);
v_x_1549_ = v_n_1576_;
v_x_1550_ = v_zero_1551_;
goto _start;
}
else
{
v_x_1549_ = v_n_1576_;
v_x_1550_ = v___x_1593_;
goto _start;
}
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1598_; 
lean_dec(v_n_1576_);
lean_dec(v_x_1548_);
lean_inc(v___x_1586_);
v_val_1597_ = lean_noption_get(v___x_1586_);
v___x_1598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1598_, 0, v_x_1550_);
lean_ctor_set(v___x_1598_, 1, v_val_1588_);
lean_ctor_set(v___x_1598_, 2, v_val_1597_);
return v___x_1598_;
}
}
}
v___jp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1579_ = lean_array_get_size(v_keyArray_1562_);
v___x_1580_ = lean_nat_add(v_x_1550_, v_one_1575_);
lean_dec(v_x_1550_);
v___x_1581_ = lean_nat_dec_lt(v___x_1580_, v___x_1579_);
if (v___x_1581_ == 0)
{
lean_dec(v___x_1580_);
v_x_1548_ = v___y_1578_;
v_x_1549_ = v_n_1576_;
v_x_1550_ = v_zero_1551_;
goto _start;
}
else
{
v_x_1548_ = v___y_1578_;
v_x_1549_ = v_n_1576_;
v_x_1550_ = v___x_1580_;
goto _start;
}
}
v___jp_1584_:
{
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v___x_1585_; 
lean_inc(v_x_1550_);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_x_1550_);
v___y_1578_ = v___x_1585_;
goto v___jp_1577_;
}
else
{
v___y_1578_ = v_x_1548_;
goto v___jp_1577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object* v_m_1599_, lean_object* v_query_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_m_1599_, v_query_1600_, v_x_1601_, v_x_1602_, v_x_1603_);
lean_dec_ref(v_query_1600_);
lean_dec_ref(v_m_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object* v_m_1605_, lean_object* v_query_1606_){
_start:
{
lean_object* v_keyArray_1607_; lean_object* v_type_1608_; lean_object* v___x_1609_; uint64_t v___x_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v_fold_1613_; uint64_t v___x_1614_; uint64_t v___x_1615_; uint64_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_keyArray_1607_ = lean_ctor_get(v_m_1605_, 1);
v_type_1608_ = lean_ctor_get(v_query_1606_, 1);
v___x_1609_ = lean_array_get_size(v_keyArray_1607_);
v___x_1610_ = l_Lean_Expr_hash(v_type_1608_);
v___x_1611_ = 32ULL;
v___x_1612_ = lean_uint64_shift_right(v___x_1610_, v___x_1611_);
v_fold_1613_ = lean_uint64_xor(v___x_1610_, v___x_1612_);
v___x_1614_ = 16ULL;
v___x_1615_ = lean_uint64_shift_right(v_fold_1613_, v___x_1614_);
v___x_1616_ = lean_uint64_xor(v_fold_1613_, v___x_1615_);
v___x_1617_ = lean_uint64_to_usize(v___x_1616_);
v___x_1618_ = lean_usize_of_nat(v___x_1609_);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_sub(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_usize_land(v___x_1617_, v___x_1620_);
v___x_1622_ = lean_usize_to_nat(v___x_1621_);
v___x_1623_ = lean_box(0);
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_m_1605_, v_query_1606_, v___x_1623_, v___x_1609_, v___x_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg___boxed(lean_object* v_m_1625_, lean_object* v_query_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_1625_, v_query_1626_);
lean_dec_ref(v_query_1626_);
lean_dec_ref(v_m_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg(lean_object* v_b_1628_, lean_object* v_acc_1629_, lean_object* v_i_1630_){
_start:
{
lean_object* v___y_1632_; lean_object* v_keyArray_1640_; lean_object* v_valueArray_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_keyArray_1640_ = lean_ctor_get(v_b_1628_, 1);
v_valueArray_1641_ = lean_ctor_get(v_b_1628_, 2);
v___x_1642_ = lean_array_get_size(v_keyArray_1640_);
v___x_1643_ = lean_nat_dec_lt(v_i_1630_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_dec(v_i_1630_);
return v_acc_1629_;
}
else
{
lean_object* v___x_1644_; uint8_t v_isSome_1645_; 
v___x_1644_ = lean_array_fget_borrowed(v_keyArray_1640_, v_i_1630_);
v_isSome_1645_ = lean_noption_is_some(v___x_1644_);
if (v_isSome_1645_ == 0)
{
goto v___jp_1636_;
}
else
{
lean_object* v___x_1646_; uint8_t v_isSome_1647_; 
v___x_1646_ = lean_array_fget_borrowed(v_valueArray_1641_, v_i_1630_);
v_isSome_1647_ = lean_noption_is_some(v___x_1646_);
if (v_isSome_1647_ == 0)
{
goto v___jp_1636_;
}
else
{
lean_object* v_val_1648_; lean_object* v_val_1649_; lean_object* v_i_1651_; lean_object* v___x_1656_; 
lean_inc(v___x_1644_);
v_val_1648_ = lean_noption_get(v___x_1644_);
lean_inc(v___x_1646_);
v_val_1649_ = lean_noption_get(v___x_1646_);
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_acc_1629_, v_val_1648_);
switch(lean_obj_tag(v___x_1656_))
{
case 0:
{
lean_object* v_index_1657_; lean_object* v_size_1658_; lean_object* v___x_1659_; 
v_index_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_index_1657_);
lean_dec_ref_known(v___x_1656_, 3);
v_size_1658_ = lean_ctor_get(v_acc_1629_, 0);
lean_inc(v_size_1658_);
v___x_1659_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1629_, v_size_1658_, v_index_1657_, v_val_1648_, v_val_1649_);
lean_dec(v_index_1657_);
v___y_1632_ = v___x_1659_;
goto v___jp_1631_;
}
case 1:
{
lean_object* v_index_1660_; 
v_index_1660_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_index_1660_);
lean_dec_ref_known(v___x_1656_, 1);
v_i_1651_ = v_index_1660_;
goto v___jp_1650_;
}
default: 
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1629_, v___x_1661_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_index_1663_; 
v_index_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_index_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v_i_1651_ = v_index_1663_;
goto v___jp_1650_;
}
else
{
lean_dec(v_val_1649_);
lean_dec(v_val_1648_);
v___y_1632_ = v_acc_1629_;
goto v___jp_1631_;
}
}
}
v___jp_1650_:
{
lean_object* v_size_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_size_1652_ = lean_ctor_get(v_acc_1629_, 0);
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_add(v_size_1652_, v___x_1653_);
v___x_1655_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1629_, v___x_1654_, v_i_1651_, v_val_1648_, v_val_1649_);
lean_dec(v_i_1651_);
v___y_1632_ = v___x_1655_;
goto v___jp_1631_;
}
}
}
}
v___jp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_add(v_i_1630_, v___x_1633_);
lean_dec(v_i_1630_);
v_acc_1629_ = v___y_1632_;
v_i_1630_ = v___x_1634_;
goto _start;
}
v___jp_1636_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_add(v_i_1630_, v___x_1637_);
lean_dec(v_i_1630_);
v_i_1630_ = v___x_1638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_1664_, lean_object* v_acc_1665_, lean_object* v_i_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg(v_b_1664_, v_acc_1665_, v_i_1666_);
lean_dec_ref(v_b_1664_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg(lean_object* v_init_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg(v_b_1669_, v_init_1668_, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg___boxed(lean_object* v_init_1672_, lean_object* v_b_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg(v_init_1672_, v_b_1673_);
lean_dec_ref(v_b_1673_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object* v_m_1675_){
_start:
{
lean_object* v_keyArray_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_cellCount_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_target_1683_; lean_object* v___x_1684_; 
v_keyArray_1676_ = lean_ctor_get(v_m_1675_, 1);
v___x_1677_ = lean_array_get_size(v_keyArray_1676_);
v___x_1678_ = lean_unsigned_to_nat(2u);
v_cellCount_1679_ = lean_nat_mul(v___x_1677_, v___x_1678_);
v___x_1680_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1679_);
v___x_1681_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1679_);
v___x_1682_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1679_);
v_target_1683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1683_, 0, v___x_1680_);
lean_ctor_set(v_target_1683_, 1, v___x_1681_);
lean_ctor_set(v_target_1683_, 2, v___x_1682_);
v___x_1684_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg(v_target_1683_, v_m_1675_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object* v_m_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_m_1685_);
lean_dec_ref(v_m_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg(lean_object* v_fvar_1687_, lean_object* v_b_1688_, lean_object* v_acc_1689_, lean_object* v_i_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_a_1698_; lean_object* v_keyArray_1702_; lean_object* v_valueArray_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_keyArray_1702_ = lean_ctor_get(v_b_1688_, 1);
v_valueArray_1703_ = lean_ctor_get(v_b_1688_, 2);
v___x_1704_ = lean_array_get_size(v_keyArray_1702_);
v___x_1705_ = lean_nat_dec_lt(v_i_1690_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_i_1690_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_acc_1689_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; uint8_t v_isSome_1708_; 
v___x_1707_ = lean_array_fget_borrowed(v_keyArray_1702_, v_i_1690_);
v_isSome_1708_ = lean_noption_is_some(v___x_1707_);
if (v_isSome_1708_ == 0)
{
goto v___jp_1693_;
}
else
{
lean_object* v___x_1709_; uint8_t v_isSome_1710_; 
v___x_1709_ = lean_array_fget_borrowed(v_valueArray_1703_, v_i_1690_);
v_isSome_1710_ = lean_noption_is_some(v___x_1709_);
if (v_isSome_1710_ == 0)
{
goto v___jp_1693_;
}
else
{
lean_object* v_val_1711_; lean_object* v_type_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
lean_inc(v___x_1707_);
v_val_1711_ = lean_noption_get(v___x_1707_);
v_type_1712_ = lean_ctor_get(v_val_1711_, 1);
lean_inc_ref(v_type_1712_);
v___x_1713_ = lean_box(0);
v___x_1714_ = l_Lean_Expr_containsFVar(v_type_1712_, v_fvar_1687_);
lean_dec_ref(v_type_1712_);
if (v___x_1714_ == 0)
{
lean_dec(v_val_1711_);
v_a_1698_ = v___x_1713_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1715_; lean_object* v_uninterpretedSymbols_1716_; lean_object* v_unusedRelevantHypotheses_1717_; lean_object* v_derivedEquations_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1789_; 
v___x_1715_ = lean_st_ref_take(v___y_1691_);
v_uninterpretedSymbols_1716_ = lean_ctor_get(v___x_1715_, 0);
v_unusedRelevantHypotheses_1717_ = lean_ctor_get(v___x_1715_, 1);
v_derivedEquations_1718_ = lean_ctor_get(v___x_1715_, 2);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1720_ = v___x_1715_;
v_isShared_1721_ = v_isSharedCheck_1789_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_derivedEquations_1718_);
lean_inc(v_unusedRelevantHypotheses_1717_);
lean_inc(v_uninterpretedSymbols_1716_);
lean_dec(v___x_1715_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1789_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___y_1723_; lean_object* v___y_1729_; lean_object* v_i_1730_; lean_object* v___y_1746_; lean_object* v_i_1747_; lean_object* v___y_1753_; lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_unusedRelevantHypotheses_1717_, v_val_1711_);
switch(lean_obj_tag(v___x_1762_))
{
case 0:
{
lean_dec_ref_known(v___x_1762_, 3);
lean_dec(v_val_1711_);
v___y_1723_ = v_unusedRelevantHypotheses_1717_;
goto v___jp_1722_;
}
case 1:
{
lean_object* v_index_1763_; lean_object* v_size_1764_; lean_object* v_keyArray_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_index_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_index_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v_size_1764_ = lean_ctor_get(v_unusedRelevantHypotheses_1717_, 0);
v_keyArray_1765_ = lean_ctor_get(v_unusedRelevantHypotheses_1717_, 1);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_nat_add(v_size_1764_, v___x_1766_);
v___x_1768_ = lean_array_get_size(v_keyArray_1765_);
v___x_1769_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec(v___x_1767_);
lean_dec(v_index_1763_);
goto v___jp_1735_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1770_ = lean_unsigned_to_nat(4u);
v___x_1771_ = lean_nat_mul(v___x_1767_, v___x_1770_);
v___x_1772_ = lean_unsigned_to_nat(3u);
v___x_1773_ = lean_nat_mul(v___x_1768_, v___x_1772_);
v___x_1774_ = lean_nat_dec_le(v___x_1771_, v___x_1773_);
lean_dec(v___x_1773_);
lean_dec(v___x_1771_);
if (v___x_1774_ == 0)
{
lean_dec(v___x_1767_);
lean_dec(v_index_1763_);
goto v___jp_1735_;
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_DHashMap_Raw_setEntry___redArg(v_unusedRelevantHypotheses_1717_, v___x_1767_, v_index_1763_, v_val_1711_, v___x_1713_);
lean_dec(v_index_1763_);
v___y_1723_ = v___x_1775_;
goto v___jp_1722_;
}
}
}
default: 
{
lean_object* v_size_1776_; lean_object* v_keyArray_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_size_1776_ = lean_ctor_get(v_unusedRelevantHypotheses_1717_, 0);
v_keyArray_1777_ = lean_ctor_get(v_unusedRelevantHypotheses_1717_, 1);
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_size_1776_, v___x_1778_);
v___x_1780_ = lean_array_get_size(v_keyArray_1777_);
v___x_1781_ = lean_nat_dec_lt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec(v___x_1779_);
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_unusedRelevantHypotheses_1717_);
lean_dec_ref(v_unusedRelevantHypotheses_1717_);
v___y_1753_ = v___x_1782_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1783_ = lean_unsigned_to_nat(4u);
v___x_1784_ = lean_nat_mul(v___x_1779_, v___x_1783_);
lean_dec(v___x_1779_);
v___x_1785_ = lean_unsigned_to_nat(3u);
v___x_1786_ = lean_nat_mul(v___x_1780_, v___x_1785_);
v___x_1787_ = lean_nat_dec_le(v___x_1784_, v___x_1786_);
lean_dec(v___x_1786_);
lean_dec(v___x_1784_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_unusedRelevantHypotheses_1717_);
lean_dec_ref(v_unusedRelevantHypotheses_1717_);
v___y_1753_ = v___x_1788_;
goto v___jp_1752_;
}
else
{
v___y_1753_ = v_unusedRelevantHypotheses_1717_;
goto v___jp_1752_;
}
}
}
}
v___jp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___y_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_uninterpretedSymbols_1716_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v___y_1723_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_derivedEquations_1718_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_st_ref_put(v___y_1691_, v___x_1725_);
v_a_1698_ = v___x_1713_;
goto v___jp_1697_;
}
}
v___jp_1728_:
{
lean_object* v_size_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_size_1731_ = lean_ctor_get(v___y_1729_, 0);
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v_size_1731_, v___x_1732_);
v___x_1734_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1729_, v___x_1733_, v_i_1730_, v_val_1711_, v___x_1713_);
lean_dec(v_i_1730_);
v___y_1723_ = v___x_1734_;
goto v___jp_1722_;
}
v___jp_1735_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_unusedRelevantHypotheses_1717_);
lean_dec_ref(v_unusedRelevantHypotheses_1717_);
v___x_1737_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v___x_1736_, v_val_1711_);
switch(lean_obj_tag(v___x_1737_))
{
case 0:
{
lean_object* v_index_1738_; lean_object* v_size_1739_; lean_object* v___x_1740_; 
v_index_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_index_1738_);
lean_dec_ref_known(v___x_1737_, 3);
v_size_1739_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_size_1739_);
v___x_1740_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1736_, v_size_1739_, v_index_1738_, v_val_1711_, v___x_1713_);
lean_dec(v_index_1738_);
v___y_1723_ = v___x_1740_;
goto v___jp_1722_;
}
case 1:
{
lean_object* v_index_1741_; 
v_index_1741_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_index_1741_);
lean_dec_ref_known(v___x_1737_, 1);
v___y_1729_ = v___x_1736_;
v_i_1730_ = v_index_1741_;
goto v___jp_1728_;
}
default: 
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1736_, v___x_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_index_1744_; 
v_index_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_index_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___y_1729_ = v___x_1736_;
v_i_1730_ = v_index_1744_;
goto v___jp_1728_;
}
else
{
lean_dec(v_val_1711_);
v___y_1723_ = v___x_1736_;
goto v___jp_1722_;
}
}
}
}
v___jp_1745_:
{
lean_object* v_size_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_size_1748_ = lean_ctor_get(v___y_1746_, 0);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_size_1748_, v___x_1749_);
v___x_1751_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1746_, v___x_1750_, v_i_1747_, v_val_1711_, v___x_1713_);
lean_dec(v_i_1747_);
v___y_1723_ = v___x_1751_;
goto v___jp_1722_;
}
v___jp_1752_:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v___y_1753_, v_val_1711_);
switch(lean_obj_tag(v___x_1754_))
{
case 0:
{
lean_object* v_index_1755_; lean_object* v_size_1756_; lean_object* v___x_1757_; 
v_index_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_index_1755_);
lean_dec_ref_known(v___x_1754_, 3);
v_size_1756_ = lean_ctor_get(v___y_1753_, 0);
lean_inc(v_size_1756_);
v___x_1757_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1753_, v_size_1756_, v_index_1755_, v_val_1711_, v___x_1713_);
lean_dec(v_index_1755_);
v___y_1723_ = v___x_1757_;
goto v___jp_1722_;
}
case 1:
{
lean_object* v_index_1758_; 
v_index_1758_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_index_1758_);
lean_dec_ref_known(v___x_1754_, 1);
v___y_1746_ = v___y_1753_;
v_i_1747_ = v_index_1758_;
goto v___jp_1745_;
}
default: 
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1753_, v___x_1759_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_index_1761_; 
v_index_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_index_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___y_1746_ = v___y_1753_;
v_i_1747_ = v_index_1761_;
goto v___jp_1745_;
}
else
{
lean_dec(v_val_1711_);
v___y_1723_ = v___y_1753_;
goto v___jp_1722_;
}
}
}
}
}
}
}
}
}
v___jp_1693_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_nat_add(v_i_1690_, v___x_1694_);
lean_dec(v_i_1690_);
v_i_1690_ = v___x_1695_;
goto _start;
}
v___jp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = lean_nat_add(v_i_1690_, v___x_1699_);
lean_dec(v_i_1690_);
v_acc_1689_ = v_a_1698_;
v_i_1690_ = v___x_1700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg___boxed(lean_object* v_fvar_1790_, lean_object* v_b_1791_, lean_object* v_acc_1792_, lean_object* v_i_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg(v_fvar_1790_, v_b_1791_, v_acc_1792_, v_i_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v_b_1791_);
lean_dec(v_fvar_1790_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object* v_fvar_1797_, lean_object* v_init_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg(v_fvar_1797_, v_b_1799_, v_init_1798_, v___x_1807_, v___y_1801_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object* v_fvar_1809_, lean_object* v_init_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1809_, v_init_1810_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_b_1811_);
lean_dec(v_fvar_1809_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object* v_fvar_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_unusedHypotheses_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_unusedHypotheses_1828_ = lean_ctor_get(v_a_1821_, 1);
v___x_1829_ = lean_box(0);
v___x_1830_ = l_Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1820_, v___x_1829_, v_unusedHypotheses_1828_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v___x_1830_, 0);
lean_dec(v_unused_1838_);
v___x_1832_ = v___x_1830_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v___x_1830_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1829_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object* v_fvar_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_fvar_1839_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object* v_00_u03b2_1848_, lean_object* v_m_1849_, lean_object* v_query_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_1849_, v_query_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___boxed(lean_object* v_00_u03b2_1852_, lean_object* v_m_1853_, lean_object* v_query_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(v_00_u03b2_1852_, v_m_1853_, v_query_1854_);
lean_dec_ref(v_query_1854_);
lean_dec_ref(v_m_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object* v_00_u03b2_1856_, lean_object* v_m_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_m_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_m_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_00_u03b2_1859_, v_m_1860_);
lean_dec_ref(v_m_1860_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object* v_00_u03b2_1862_, lean_object* v_m_1863_, lean_object* v_query_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_m_1863_, v_query_1864_, v_x_1865_, v_x_1866_, v_x_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1870_, lean_object* v_m_1871_, lean_object* v_query_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(v_00_u03b2_1870_, v_m_1871_, v_query_1872_, v_x_1873_, v_x_1874_, v_x_1875_, v_x_1876_);
lean_dec_ref(v_query_1872_);
lean_dec_ref(v_m_1871_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2(lean_object* v_00_u03b2_1878_, lean_object* v_init_1879_, lean_object* v_b_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___redArg(v_init_1879_, v_b_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1882_, lean_object* v_init_1883_, lean_object* v_b_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2(v_00_u03b2_1882_, v_init_1883_, v_b_1884_);
lean_dec_ref(v_b_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4(lean_object* v_fvar_1886_, lean_object* v_b_1887_, lean_object* v_acc_1888_, lean_object* v_i_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___redArg(v_fvar_1886_, v_b_1887_, v_acc_1888_, v_i_1889_, v___y_1891_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4___boxed(lean_object* v_fvar_1898_, lean_object* v_b_1899_, lean_object* v_acc_1900_, lean_object* v_i_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_spec__4(v_fvar_1898_, v_b_1899_, v_acc_1900_, v_i_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec_ref(v_b_1899_);
lean_dec(v_fvar_1898_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1910_, lean_object* v_b_1911_, lean_object* v_acc_1912_, lean_object* v_i_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___redArg(v_b_1911_, v_acc_1912_, v_i_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1915_, lean_object* v_b_1916_, lean_object* v_acc_1917_, lean_object* v_i_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_spec__2_spec__3(v_00_u03b2_1915_, v_b_1916_, v_acc_1917_, v_i_1918_);
lean_dec_ref(v_b_1916_);
return v_res_1919_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_instMonadEIO(lean_box(0));
return v___x_1920_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = l_Lean_instInhabitedExpr;
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(lean_object* v_msg_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v_toApplicative_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_2000_; 
v___x_1935_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0);
v___x_1936_ = l_StateRefT_x27_instMonad___redArg(v___x_1935_);
v_toApplicative_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v___x_1936_, 1);
lean_dec(v_unused_2001_);
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_2000_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_toApplicative_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_2000_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_toFunctor_1941_; lean_object* v_toSeq_1942_; lean_object* v_toSeqLeft_1943_; lean_object* v_toSeqRight_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1998_; 
v_toFunctor_1941_ = lean_ctor_get(v_toApplicative_1937_, 0);
v_toSeq_1942_ = lean_ctor_get(v_toApplicative_1937_, 2);
v_toSeqLeft_1943_ = lean_ctor_get(v_toApplicative_1937_, 3);
v_toSeqRight_1944_ = lean_ctor_get(v_toApplicative_1937_, 4);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_toApplicative_1937_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_toApplicative_1937_, 1);
lean_dec(v_unused_1999_);
v___x_1946_ = v_toApplicative_1937_;
v_isShared_1947_ = v_isSharedCheck_1998_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_toSeqRight_1944_);
lean_inc(v_toSeqLeft_1943_);
lean_inc(v_toSeq_1942_);
lean_inc(v_toFunctor_1941_);
lean_dec(v_toApplicative_1937_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1998_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___x_1957_; 
v___f_1948_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1));
v___f_1949_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1941_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toFunctor_1941_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toFunctor_1941_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___f_1950_);
lean_ctor_set(v___x_1952_, 1, v___f_1951_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeqRight_1944_);
v___f_1954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1954_, 0, v_toSeqLeft_1943_);
v___f_1955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1955_, 0, v_toSeq_1942_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___f_1953_);
lean_ctor_set(v___x_1946_, 3, v___f_1954_);
lean_ctor_set(v___x_1946_, 2, v___f_1955_);
lean_ctor_set(v___x_1946_, 1, v___f_1948_);
lean_ctor_set(v___x_1946_, 0, v___x_1952_);
v___x_1957_ = v___x_1946_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___f_1948_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v___f_1955_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v___f_1954_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v___f_1953_);
v___x_1957_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___f_1949_);
lean_ctor_set(v___x_1939_, 0, v___x_1957_);
v___x_1959_ = v___x_1939_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___f_1949_);
v___x_1959_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v_toApplicative_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1994_; 
v___x_1960_ = l_StateRefT_x27_instMonad___redArg(v___x_1959_);
v_toApplicative_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1960_, 1);
lean_dec(v_unused_1995_);
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1994_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_toApplicative_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1994_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_toFunctor_1965_; lean_object* v_toSeq_1966_; lean_object* v_toSeqLeft_1967_; lean_object* v_toSeqRight_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1992_; 
v_toFunctor_1965_ = lean_ctor_get(v_toApplicative_1961_, 0);
v_toSeq_1966_ = lean_ctor_get(v_toApplicative_1961_, 2);
v_toSeqLeft_1967_ = lean_ctor_get(v_toApplicative_1961_, 3);
v_toSeqRight_1968_ = lean_ctor_get(v_toApplicative_1961_, 4);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_toApplicative_1961_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_toApplicative_1961_, 1);
lean_dec(v_unused_1993_);
v___x_1970_ = v_toApplicative_1961_;
v_isShared_1971_ = v_isSharedCheck_1992_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_toSeqRight_1968_);
lean_inc(v_toSeqLeft_1967_);
lean_inc(v_toSeq_1966_);
lean_inc(v_toFunctor_1965_);
lean_dec(v_toApplicative_1961_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1992_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___f_1979_; lean_object* v___x_1981_; 
v___f_1972_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3));
v___f_1973_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1965_);
v___f_1974_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1974_, 0, v_toFunctor_1965_);
v___f_1975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1975_, 0, v_toFunctor_1965_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___f_1974_);
lean_ctor_set(v___x_1976_, 1, v___f_1975_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toSeqRight_1968_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toSeqLeft_1967_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toSeq_1966_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___f_1977_);
lean_ctor_set(v___x_1970_, 3, v___f_1978_);
lean_ctor_set(v___x_1970_, 2, v___f_1979_);
lean_ctor_set(v___x_1970_, 1, v___f_1972_);
lean_ctor_set(v___x_1970_, 0, v___x_1976_);
v___x_1981_ = v___x_1970_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___f_1972_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v___f_1979_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v___f_1978_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v___f_1977_);
v___x_1981_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___f_1973_);
lean_ctor_set(v___x_1963_, 0, v___x_1981_);
v___x_1983_ = v___x_1963_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___f_1973_);
v___x_1983_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; lean_object* v___x_41395__overap_1988_; lean_object* v___x_1989_; 
v___x_1984_ = l_StateRefT_x27_instMonad___redArg(v___x_1983_);
v___x_1985_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5);
v___x_1986_ = l_instInhabitedOfMonad___redArg(v___x_1984_, v___x_1985_);
v___f_1987_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1987_, 0, v___x_1986_);
v___x_41395__overap_1988_ = lean_panic_fn_borrowed(v___f_1987_, v_msg_1927_);
lean_dec_ref(v___f_1987_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
v___x_1989_ = lean_apply_7(v___x_41395__overap_1988_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, lean_box(0));
return v___x_1989_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(lean_object* v_msg_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(lean_object* v_msgData_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v_env_2018_; lean_object* v___x_2019_; lean_object* v_mctx_2020_; lean_object* v_lctx_2021_; lean_object* v_options_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2017_ = lean_st_ref_get(v___y_2015_);
v_env_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_ref(v_env_2018_);
lean_dec(v___x_2017_);
v___x_2019_ = lean_st_ref_get(v___y_2013_);
v_mctx_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_ref(v_mctx_2020_);
lean_dec(v___x_2019_);
v_lctx_2021_ = lean_ctor_get(v___y_2012_, 2);
v_options_2022_ = lean_ctor_get(v___y_2014_, 2);
lean_inc_ref(v_options_2022_);
lean_inc_ref(v_lctx_2021_);
v___x_2023_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2023_, 0, v_env_2018_);
lean_ctor_set(v___x_2023_, 1, v_mctx_2020_);
lean_ctor_set(v___x_2023_, 2, v_lctx_2021_);
lean_ctor_set(v___x_2023_, 3, v_options_2022_);
v___x_2024_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v_msgData_2011_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(lean_object* v_msgData_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(lean_object* v_msg_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_ref_2039_; lean_object* v___x_2040_; lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2049_; 
v_ref_2039_ = lean_ctor_get(v___y_2036_, 5);
v___x_2040_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msg_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_inc(v_ref_2039_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_ref_2039_);
lean_ctor_set(v___x_2045_, 1, v_a_2041_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 1);
lean_ctor_set(v___x_2043_, 0, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(lean_object* v_msg_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2057_, lean_object* v_msg_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_fileName_2066_; lean_object* v_fileMap_2067_; lean_object* v_options_2068_; lean_object* v_currRecDepth_2069_; lean_object* v_maxRecDepth_2070_; lean_object* v_ref_2071_; lean_object* v_currNamespace_2072_; lean_object* v_openDecls_2073_; lean_object* v_initHeartbeats_2074_; lean_object* v_maxHeartbeats_2075_; lean_object* v_quotContext_2076_; lean_object* v_currMacroScope_2077_; uint8_t v_diag_2078_; lean_object* v_cancelTk_x3f_2079_; uint8_t v_suppressElabErrors_2080_; lean_object* v_inheritedTraceOptions_2081_; lean_object* v_ref_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_fileName_2066_ = lean_ctor_get(v___y_2063_, 0);
v_fileMap_2067_ = lean_ctor_get(v___y_2063_, 1);
v_options_2068_ = lean_ctor_get(v___y_2063_, 2);
v_currRecDepth_2069_ = lean_ctor_get(v___y_2063_, 3);
v_maxRecDepth_2070_ = lean_ctor_get(v___y_2063_, 4);
v_ref_2071_ = lean_ctor_get(v___y_2063_, 5);
v_currNamespace_2072_ = lean_ctor_get(v___y_2063_, 6);
v_openDecls_2073_ = lean_ctor_get(v___y_2063_, 7);
v_initHeartbeats_2074_ = lean_ctor_get(v___y_2063_, 8);
v_maxHeartbeats_2075_ = lean_ctor_get(v___y_2063_, 9);
v_quotContext_2076_ = lean_ctor_get(v___y_2063_, 10);
v_currMacroScope_2077_ = lean_ctor_get(v___y_2063_, 11);
v_diag_2078_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*14);
v_cancelTk_x3f_2079_ = lean_ctor_get(v___y_2063_, 12);
v_suppressElabErrors_2080_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2081_ = lean_ctor_get(v___y_2063_, 13);
v_ref_2082_ = l_Lean_replaceRef(v_ref_2057_, v_ref_2071_);
lean_inc_ref(v_inheritedTraceOptions_2081_);
lean_inc(v_cancelTk_x3f_2079_);
lean_inc(v_currMacroScope_2077_);
lean_inc(v_quotContext_2076_);
lean_inc(v_maxHeartbeats_2075_);
lean_inc(v_initHeartbeats_2074_);
lean_inc(v_openDecls_2073_);
lean_inc(v_currNamespace_2072_);
lean_inc(v_maxRecDepth_2070_);
lean_inc(v_currRecDepth_2069_);
lean_inc_ref(v_options_2068_);
lean_inc_ref(v_fileMap_2067_);
lean_inc_ref(v_fileName_2066_);
v___x_2083_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2083_, 0, v_fileName_2066_);
lean_ctor_set(v___x_2083_, 1, v_fileMap_2067_);
lean_ctor_set(v___x_2083_, 2, v_options_2068_);
lean_ctor_set(v___x_2083_, 3, v_currRecDepth_2069_);
lean_ctor_set(v___x_2083_, 4, v_maxRecDepth_2070_);
lean_ctor_set(v___x_2083_, 5, v_ref_2082_);
lean_ctor_set(v___x_2083_, 6, v_currNamespace_2072_);
lean_ctor_set(v___x_2083_, 7, v_openDecls_2073_);
lean_ctor_set(v___x_2083_, 8, v_initHeartbeats_2074_);
lean_ctor_set(v___x_2083_, 9, v_maxHeartbeats_2075_);
lean_ctor_set(v___x_2083_, 10, v_quotContext_2076_);
lean_ctor_set(v___x_2083_, 11, v_currMacroScope_2077_);
lean_ctor_set(v___x_2083_, 12, v_cancelTk_x3f_2079_);
lean_ctor_set(v___x_2083_, 13, v_inheritedTraceOptions_2081_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*14, v_diag_2078_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*14 + 1, v_suppressElabErrors_2080_);
v___x_2084_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_2058_, v___y_2061_, v___y_2062_, v___x_2083_, v___y_2064_);
lean_dec_ref_known(v___x_2083_, 14);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2085_, lean_object* v_msg_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_2085_, v_msg_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v_ref_2085_);
return v_res_2094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
lean_ctor_set(v___x_2100_, 2, v___x_2099_);
lean_ctor_set(v___x_2100_, 3, v___x_2099_);
lean_ctor_set(v___x_2100_, 4, v___x_2098_);
lean_ctor_set(v___x_2100_, 5, v___x_2098_);
lean_ctor_set(v___x_2100_, 6, v___x_2098_);
lean_ctor_set(v___x_2100_, 7, v___x_2098_);
lean_ctor_set(v___x_2100_, 8, v___x_2098_);
lean_ctor_set(v___x_2100_, 9, v___x_2098_);
lean_ctor_set(v___x_2100_, 10, v___x_2098_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_unsigned_to_nat(32u);
v___x_2102_ = lean_mk_empty_array_with_capacity(v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2104_ = ((size_t)5ULL);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_unsigned_to_nat(32u);
v___x_2107_ = lean_mk_empty_array_with_capacity(v___x_2106_);
v___x_2108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_2109_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2107_);
lean_ctor_set(v___x_2109_, 2, v___x_2105_);
lean_ctor_set(v___x_2109_, 3, v___x_2105_);
lean_ctor_set_usize(v___x_2109_, 4, v___x_2104_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2110_ = lean_box(1);
v___x_2111_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_2112_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_2113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___x_2111_);
lean_ctor_set(v___x_2113_, 2, v___x_2110_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_2128_ = l_Lean_stringToMessageData(v___x_2127_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_2135_, lean_object* v_declHint_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v_env_2140_; uint8_t v___x_2141_; 
v___x_2139_ = lean_st_ref_get(v___y_2137_);
v_env_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc_ref(v_env_2140_);
lean_dec(v___x_2139_);
v___x_2141_ = l_Lean_Name_isAnonymous(v_declHint_2136_);
if (v___x_2141_ == 0)
{
uint8_t v_isExporting_2142_; 
v_isExporting_2142_ = lean_ctor_get_uint8(v_env_2140_, sizeof(void*)*8);
if (v_isExporting_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec_ref(v_env_2140_);
lean_dec(v_declHint_2136_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_msg_2135_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
lean_inc_ref(v_env_2140_);
v___x_2144_ = l_Lean_Environment_setExporting(v_env_2140_, v___x_2141_);
lean_inc(v_declHint_2136_);
lean_inc_ref(v___x_2144_);
v___x_2145_ = l_Lean_Environment_contains(v___x_2144_, v_declHint_2136_, v_isExporting_2142_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_dec_ref(v___x_2144_);
lean_dec_ref(v_env_2140_);
lean_dec(v_declHint_2136_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_msg_2135_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_c_2152_; lean_object* v___x_2153_; 
v___x_2147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_2148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_2149_ = l_Lean_Options_empty;
v___x_2150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2144_);
lean_ctor_set(v___x_2150_, 1, v___x_2147_);
lean_ctor_set(v___x_2150_, 2, v___x_2148_);
lean_ctor_set(v___x_2150_, 3, v___x_2149_);
lean_inc(v_declHint_2136_);
v___x_2151_ = l_Lean_MessageData_ofConstName(v_declHint_2136_, v___x_2141_);
v_c_2152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2152_, 0, v___x_2150_);
lean_ctor_set(v_c_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2140_, v_declHint_2136_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v_env_2140_);
lean_dec(v_declHint_2136_);
v___x_2154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v_c_2152_);
v___x_2156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = l_Lean_MessageData_note(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_msg_2135_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
else
{
lean_object* v_val_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2196_; 
v_val_2161_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2163_ = v___x_2153_;
v_isShared_2164_ = v_isSharedCheck_2196_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_val_2161_);
lean_dec(v___x_2153_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2196_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_mod_2168_; uint8_t v___x_2169_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = l_Lean_Environment_header(v_env_2140_);
lean_dec_ref(v_env_2140_);
v___x_2167_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2166_);
v_mod_2168_ = lean_array_get(v___x_2165_, v___x_2167_, v_val_2161_);
lean_dec(v_val_2161_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = l_Lean_isPrivateName(v_declHint_2136_);
lean_dec(v_declHint_2136_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v_c_2152_);
v___x_2172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = l_Lean_MessageData_ofName(v_mod_2168_);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_MessageData_note(v___x_2177_);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v_msg_2135_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2179_);
v___x_2181_ = v___x_2163_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v_c_2152_);
v___x_2185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_MessageData_ofName(v_mod_2168_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Lean_MessageData_note(v___x_2190_);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_msg_2135_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2192_);
v___x_2194_ = v___x_2163_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2197_; 
lean_dec_ref(v_env_2140_);
lean_dec(v_declHint_2136_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_msg_2135_);
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_2198_, lean_object* v_declHint_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_2198_, v_declHint_2199_, v___y_2200_);
lean_dec(v___y_2200_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_2203_, lean_object* v_declHint_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2222_; 
v___x_2212_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_2203_, v_declHint_2204_, v___y_2210_);
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2222_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2222_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = l_Lean_unknownIdentifierMessageTag;
v___x_2218_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v_a_2213_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_2223_, lean_object* v_declHint_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_2223_, v_declHint_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_2233_, lean_object* v_msg_2234_, lean_object* v_declHint_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; 
v___x_2243_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_2234_, v_declHint_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_2233_, v_a_2244_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2246_, lean_object* v_msg_2247_, lean_object* v_declHint_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2246_, v_msg_2247_, v_declHint_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v_ref_2246_);
return v_res_2256_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_2263_, lean_object* v_constName_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2272_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_2273_ = 0;
lean_inc(v_constName_2264_);
v___x_2274_ = l_Lean_MessageData_ofConstName(v_constName_2264_, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2272_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2263_, v___x_2277_, v_constName_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_2279_, lean_object* v_constName_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2279_, v_constName_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_ref_2279_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object* v_constName_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_ref_2297_; lean_object* v___x_2298_; 
v_ref_2297_ = lean_ctor_get(v___y_2294_, 5);
v___x_2298_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2297_, v_constName_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(lean_object* v_constName_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v_env_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_st_ref_get(v___y_2314_);
v_env_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_ref(v_env_2317_);
lean_dec(v___x_2316_);
v___x_2318_ = 0;
lean_inc(v_constName_2308_);
v___x_2319_ = l_Lean_Environment_find_x3f(v_env_2317_, v_constName_2308_, v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2320_;
}
else
{
lean_object* v_val_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_constName_2308_);
v_val_2321_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2319_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_val_2321_);
lean_dec(v___x_2319_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 0);
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_val_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object* v_constName_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
return v_res_2337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2));
v___x_2345_ = l_Lean_Expr_const___override(v___x_2344_, v___x_2343_);
return v___x_2345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5));
v___x_2349_ = lean_unsigned_to_nat(61u);
v___x_2350_ = lean_unsigned_to_nat(219u);
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4));
v___x_2352_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0));
v___x_2353_ = l_mkPanicMessageWithDecl(v___x_2352_, v___x_2351_, v___x_2350_, v___x_2349_, v___x_2348_);
return v___x_2353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34));
v___x_2409_ = l_Lean_stringToMessageData(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36));
v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = l_Lean_Level_ofNat(v___x_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
v___x_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v___x_2419_);
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39));
v___x_2424_ = l_Lean_Expr_const___override(v___x_2423_, v___x_2422_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_box(0);
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43));
v___x_2429_ = l_Lean_mkConst(v___x_2428_, v___x_2427_);
return v___x_2429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_box(0);
v___x_2435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46));
v___x_2436_ = l_Lean_Expr_const___override(v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48));
v___x_2439_ = l_Lean_stringToMessageData(v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
static size_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52(void){
_start:
{
lean_object* v___x_2443_; size_t v___x_2444_; 
v___x_2443_ = lean_unsigned_to_nat(0u);
v___x_2444_ = lean_isize_of_nat(v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55));
v___x_2452_ = l_Lean_Expr_const___override(v___x_2451_, v___x_2450_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57));
v___x_2457_ = l_Lean_Expr_const___override(v___x_2456_, v___x_2455_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_box(0);
v___x_2463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60));
v___x_2464_ = l_Lean_Expr_const___override(v___x_2463_, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62));
v___x_2467_ = l_Lean_stringToMessageData(v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_box(0);
v___x_2474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66));
v___x_2475_ = l_Lean_mkConst(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_box(0);
v___x_2481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69));
v___x_2482_ = l_Lean_mkConst(v___x_2481_, v___x_2480_);
return v___x_2482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71));
v___x_2485_ = l_Lean_stringToMessageData(v___x_2484_);
return v___x_2485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_box(0);
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73));
v___x_2490_ = l_Lean_mkConst(v___x_2489_, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_box(0);
v___x_2495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75));
v___x_2496_ = l_Lean_Expr_const___override(v___x_2495_, v___x_2494_);
return v___x_2496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_box(0);
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79));
v___x_2504_ = l_Lean_mkConst(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_box(0);
v___x_2509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81));
v___x_2510_ = l_Lean_Expr_const___override(v___x_2509_, v___x_2508_);
return v___x_2510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83));
v___x_2513_ = l_Lean_stringToMessageData(v___x_2512_);
return v___x_2513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = lean_box(0);
v___x_2517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85));
v___x_2518_ = l_Lean_mkConst(v___x_2517_, v___x_2516_);
return v___x_2518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87));
v___x_2524_ = l_Lean_Expr_const___override(v___x_2523_, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_box(0);
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91));
v___x_2532_ = l_Lean_mkConst(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = lean_box(0);
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93));
v___x_2538_ = l_Lean_Expr_const___override(v___x_2537_, v___x_2536_);
return v___x_2538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95));
v___x_2541_ = l_Lean_stringToMessageData(v___x_2540_);
return v___x_2541_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97(void){
_start:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_int8_of_nat(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98));
v___x_2548_ = l_Lean_Expr_const___override(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_box(0);
v___x_2553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100));
v___x_2554_ = l_Lean_Expr_const___override(v___x_2553_, v___x_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102));
v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
return v___x_2557_;
}
}
static uint16_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104(void){
_start:
{
lean_object* v___x_2558_; uint16_t v___x_2559_; 
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = lean_int16_of_nat(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_box(0);
v___x_2563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105));
v___x_2564_ = l_Lean_Expr_const___override(v___x_2563_, v___x_2562_);
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_box(0);
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107));
v___x_2570_ = l_Lean_Expr_const___override(v___x_2569_, v___x_2568_);
return v___x_2570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109));
v___x_2573_ = l_Lean_stringToMessageData(v___x_2572_);
return v___x_2573_;
}
}
static uint32_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111(void){
_start:
{
lean_object* v___x_2574_; uint32_t v___x_2575_; 
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = lean_int32_of_nat(v___x_2574_);
return v___x_2575_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_box(0);
v___x_2579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112));
v___x_2580_ = l_Lean_Expr_const___override(v___x_2579_, v___x_2578_);
return v___x_2580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_box(0);
v___x_2585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114));
v___x_2586_ = l_Lean_Expr_const___override(v___x_2585_, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116));
v___x_2589_ = l_Lean_stringToMessageData(v___x_2588_);
return v___x_2589_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118(void){
_start:
{
lean_object* v___x_2590_; uint64_t v___x_2591_; 
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_int64_of_nat(v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119));
v___x_2596_ = l_Lean_Expr_const___override(v___x_2595_, v___x_2594_);
return v___x_2596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_box(0);
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121));
v___x_2602_ = l_Lean_Expr_const___override(v___x_2601_, v___x_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object* v_var_2603_, lean_object* v_value_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
uint8_t v___x_2627_; 
v___x_2627_ = l_Lean_Expr_isFVar(v_var_2603_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_inc_ref(v_var_2603_);
v___x_2628_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_2603_, v_a_2608_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_3139_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_3139_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_3139_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = l_Lean_Expr_cleanupAnnotations(v_a_2629_);
v___x_2698_ = l_Lean_Expr_isApp(v___x_2697_);
if (v___x_2698_ == 0)
{
lean_dec_ref(v___x_2697_);
v___y_2634_ = v_a_2605_;
v___y_2635_ = v_a_2606_;
v___y_2636_ = v_a_2607_;
v___y_2637_ = v_a_2608_;
v___y_2638_ = v_a_2609_;
v___y_2639_ = v_a_2610_;
goto v___jp_2633_;
}
else
{
lean_object* v_arg_2699_; lean_object* v___y_2701_; lean_object* v___y_2705_; lean_object* v___y_2709_; lean_object* v___y_2713_; lean_object* v___y_2717_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_arg_2699_ = lean_ctor_get(v___x_2697_, 1);
lean_inc_ref(v_arg_2699_);
v___x_2720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2697_);
v___x_2721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9));
v___x_2722_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11));
v___x_2724_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13));
v___x_2726_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15));
v___x_2728_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17));
v___x_2730_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19));
v___x_2732_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21));
v___x_2734_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23));
v___x_2736_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25));
v___x_2738_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2737_);
if (v___x_2738_ == 0)
{
uint8_t v___x_2739_; 
lean_dec_ref(v_arg_2699_);
v___x_2739_ = l_Lean_Expr_isApp(v___x_2720_);
if (v___x_2739_ == 0)
{
lean_dec_ref(v___x_2720_);
v___y_2634_ = v_a_2605_;
v___y_2635_ = v_a_2606_;
v___y_2636_ = v_a_2607_;
v___y_2637_ = v_a_2608_;
v___y_2638_ = v_a_2609_;
v___y_2639_ = v_a_2610_;
goto v___jp_2633_;
}
else
{
lean_object* v_arg_2740_; lean_object* v___y_2742_; lean_object* v___y_2746_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_arg_2740_ = lean_ctor_get(v___x_2720_, 1);
lean_inc_ref(v_arg_2740_);
v___x_2749_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2720_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28));
v___x_2751_ = l_Lean_Expr_isConstOf(v___x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30));
v___x_2753_ = l_Lean_Expr_isConstOf(v___x_2749_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32));
v___x_2755_ = l_Lean_Expr_isConstOf(v___x_2749_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33));
v___x_2757_ = l_Lean_Expr_isConstOf(v___x_2749_, v___x_2756_);
lean_dec_ref(v___x_2749_);
if (v___x_2757_ == 0)
{
lean_dec_ref(v_arg_2740_);
v___y_2634_ = v_a_2605_;
v___y_2635_ = v_a_2606_;
v___y_2636_ = v_a_2607_;
v___y_2637_ = v_a_2608_;
v___y_2638_ = v_a_2609_;
v___y_2639_ = v_a_2610_;
goto v___jp_2633_;
}
else
{
lean_object* v_w_2758_; lean_object* v_bv_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2787_; 
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2758_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2759_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2761_ = v_value_2604_;
v_isShared_2762_ = v_isSharedCheck_2787_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_bv_2759_);
lean_inc(v_w_2758_);
lean_dec(v_value_2604_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2787_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_unsigned_to_nat(32u);
v___x_2764_ = lean_nat_dec_eq(v_w_2758_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
lean_dec(v_bv_2759_);
lean_dec_ref(v_arg_2740_);
v___x_2765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35);
v___x_2766_ = l_Nat_reprFast(v_w_2758_);
v___x_2767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = l_Lean_MessageData_ofFormat(v___x_2767_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set_tag(v___x_2761_, 7);
lean_ctor_set(v___x_2761_, 1, v___x_2768_);
lean_ctor_set(v___x_2761_, 0, v___x_2765_);
v___x_2770_ = v___x_2761_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2772_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2773_;
}
}
else
{
size_t v___x_2775_; lean_object* v___x_2776_; lean_object* v_r_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
lean_dec(v_w_2758_);
v___x_2775_ = lean_usize_of_nat(v_bv_2759_);
lean_dec(v_bv_2759_);
v___x_2776_ = lean_usize_to_nat(v___x_2775_);
v_r_2777_ = l_Lean_mkRawNatLit(v___x_2776_);
v___x_2778_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2777_);
v___x_2781_ = l_Lean_Expr_app___override(v___x_2780_, v_r_2777_);
v___x_2782_ = l_Lean_mkApp3(v___x_2778_, v___x_2779_, v_r_2777_, v___x_2781_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2782_);
lean_ctor_set(v___x_2761_, 0, v_arg_2740_);
v___x_2784_ = v___x_2761_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_arg_2740_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
}
}
}
else
{
lean_object* v_w_2788_; lean_object* v_bv_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref(v___x_2749_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2788_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2789_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2791_ = v_value_2604_;
v_isShared_2792_ = v_isSharedCheck_2817_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_bv_2789_);
lean_inc(v_w_2788_);
lean_dec(v_value_2604_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2817_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2793_ = lean_unsigned_to_nat(64u);
v___x_2794_ = lean_nat_dec_eq(v_w_2788_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_dec(v_bv_2789_);
lean_dec_ref(v_arg_2740_);
v___x_2795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49);
v___x_2796_ = l_Nat_reprFast(v_w_2788_);
v___x_2797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
v___x_2798_ = l_Lean_MessageData_ofFormat(v___x_2797_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 7);
lean_ctor_set(v___x_2791_, 1, v___x_2798_);
lean_ctor_set(v___x_2791_, 0, v___x_2795_);
v___x_2800_ = v___x_2791_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2802_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2803_;
}
}
else
{
size_t v___x_2805_; lean_object* v___x_2806_; lean_object* v_r_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
lean_dec(v_w_2788_);
v___x_2805_ = lean_usize_of_nat(v_bv_2789_);
lean_dec(v_bv_2789_);
v___x_2806_ = lean_usize_to_nat(v___x_2805_);
v_r_2807_ = l_Lean_mkRawNatLit(v___x_2806_);
v___x_2808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2807_);
v___x_2811_ = l_Lean_Expr_app___override(v___x_2810_, v_r_2807_);
v___x_2812_ = l_Lean_mkApp3(v___x_2808_, v___x_2809_, v_r_2807_, v___x_2811_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2812_);
lean_ctor_set(v___x_2791_, 0, v_arg_2740_);
v___x_2814_ = v___x_2791_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_arg_2740_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_w_2818_; lean_object* v_bv_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v___x_2749_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2818_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2819_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2821_ = v_value_2604_;
v_isShared_2822_ = v_isSharedCheck_2850_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_bv_2819_);
lean_inc(v_w_2818_);
lean_dec(v_value_2604_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2850_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_unsigned_to_nat(32u);
v___x_2824_ = lean_nat_dec_eq(v_w_2818_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
lean_dec(v_bv_2819_);
lean_dec_ref(v_arg_2740_);
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51);
v___x_2826_ = l_Nat_reprFast(v_w_2818_);
v___x_2827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
v___x_2828_ = l_Lean_MessageData_ofFormat(v___x_2827_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 7);
lean_ctor_set(v___x_2821_, 1, v___x_2828_);
lean_ctor_set(v___x_2821_, 0, v___x_2825_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2832_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2833_;
}
}
else
{
lean_object* v___x_2835_; size_t v___x_2836_; size_t v___x_2837_; uint8_t v___x_2838_; 
lean_del_object(v___x_2821_);
v___x_2835_ = l_BitVec_toInt(v_w_2818_, v_bv_2819_);
lean_dec(v_w_2818_);
v___x_2836_ = lean_isize_of_int(v___x_2835_);
lean_dec(v___x_2835_);
v___x_2837_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2838_ = lean_isize_dec_le(v___x_2837_, v___x_2836_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2842_ = lean_isize_to_int(v___x_2836_);
v___x_2843_ = lean_int_neg(v___x_2842_);
lean_dec(v___x_2842_);
v___x_2844_ = l_Int_toNat(v___x_2843_);
lean_dec(v___x_2843_);
v___x_2845_ = l_Lean_instToExprISize_mkNat(v___x_2844_);
v___x_2846_ = l_Lean_mkApp3(v___x_2839_, v___x_2840_, v___x_2841_, v___x_2845_);
v___y_2746_ = v___x_2846_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_isize_to_int(v___x_2836_);
v___x_2848_ = l_Int_toNat(v___x_2847_);
lean_dec(v___x_2847_);
v___x_2849_ = l_Lean_instToExprISize_mkNat(v___x_2848_);
v___y_2746_ = v___x_2849_;
goto v___jp_2745_;
}
}
}
}
}
else
{
lean_object* v_w_2851_; lean_object* v_bv_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v___x_2749_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2851_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2852_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2854_ = v_value_2604_;
v_isShared_2855_ = v_isSharedCheck_2883_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_bv_2852_);
lean_inc(v_w_2851_);
lean_dec(v_value_2604_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2883_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = lean_unsigned_to_nat(64u);
v___x_2857_ = lean_nat_dec_eq(v_w_2851_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_dec(v_bv_2852_);
lean_dec_ref(v_arg_2740_);
v___x_2858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63);
v___x_2859_ = l_Nat_reprFast(v_w_2851_);
v___x_2860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
v___x_2861_ = l_Lean_MessageData_ofFormat(v___x_2860_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set_tag(v___x_2854_, 7);
lean_ctor_set(v___x_2854_, 1, v___x_2861_);
lean_ctor_set(v___x_2854_, 0, v___x_2858_);
v___x_2863_ = v___x_2854_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2865_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2866_;
}
}
else
{
lean_object* v___x_2868_; size_t v___x_2869_; size_t v___x_2870_; uint8_t v___x_2871_; 
lean_del_object(v___x_2854_);
v___x_2868_ = l_BitVec_toInt(v_w_2851_, v_bv_2852_);
lean_dec(v_w_2851_);
v___x_2869_ = lean_isize_of_int(v___x_2868_);
lean_dec(v___x_2868_);
v___x_2870_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2871_ = lean_isize_dec_le(v___x_2870_, v___x_2869_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2872_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2875_ = lean_isize_to_int(v___x_2869_);
v___x_2876_ = lean_int_neg(v___x_2875_);
lean_dec(v___x_2875_);
v___x_2877_ = l_Int_toNat(v___x_2876_);
lean_dec(v___x_2876_);
v___x_2878_ = l_Lean_instToExprISize_mkNat(v___x_2877_);
v___x_2879_ = l_Lean_mkApp3(v___x_2872_, v___x_2873_, v___x_2874_, v___x_2878_);
v___y_2742_ = v___x_2879_;
goto v___jp_2741_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_isize_to_int(v___x_2869_);
v___x_2881_ = l_Int_toNat(v___x_2880_);
lean_dec(v___x_2880_);
v___x_2882_ = l_Lean_instToExprISize_mkNat(v___x_2881_);
v___y_2742_ = v___x_2882_;
goto v___jp_2741_;
}
}
}
}
v___jp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v_arg_2740_);
lean_ctor_set(v___x_2743_, 1, v___y_2742_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
v___jp_2745_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_arg_2740_);
lean_ctor_set(v___x_2747_, 1, v___y_2746_);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
}
}
else
{
lean_object* v_w_2884_; lean_object* v_bv_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2884_ = lean_ctor_get(v_value_2604_, 0);
lean_inc(v_w_2884_);
v_bv_2885_ = lean_ctor_get(v_value_2604_, 1);
lean_inc(v_bv_2885_);
lean_dec_ref(v_value_2604_);
v___x_2886_ = lean_unsigned_to_nat(1u);
v___x_2887_ = l_BitVec_ofNat(v_w_2884_, v___x_2886_);
lean_dec(v_w_2884_);
v___x_2888_ = lean_nat_dec_eq(v_bv_2885_, v___x_2887_);
lean_dec(v___x_2887_);
lean_dec(v_bv_2885_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67);
v___y_2717_ = v___x_2889_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70);
v___y_2717_ = v___x_2890_;
goto v___jp_2716_;
}
}
}
else
{
lean_object* v_w_2891_; lean_object* v_bv_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2891_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2892_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2894_ = v_value_2604_;
v_isShared_2895_ = v_isSharedCheck_2920_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_bv_2892_);
lean_inc(v_w_2891_);
lean_dec(v_value_2604_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2920_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = lean_unsigned_to_nat(8u);
v___x_2897_ = lean_nat_dec_eq(v_w_2891_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec(v_bv_2892_);
lean_dec_ref(v_arg_2699_);
v___x_2898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72);
v___x_2899_ = l_Nat_reprFast(v_w_2891_);
v___x_2900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
v___x_2901_ = l_Lean_MessageData_ofFormat(v___x_2900_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 7);
lean_ctor_set(v___x_2894_, 1, v___x_2901_);
lean_ctor_set(v___x_2894_, 0, v___x_2898_);
v___x_2903_ = v___x_2894_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2905_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2906_;
}
}
else
{
uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v_r_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
lean_dec(v_w_2891_);
v___x_2908_ = lean_uint8_of_nat_mk(v_bv_2892_);
v___x_2909_ = lean_uint8_to_nat(v___x_2908_);
v_r_2910_ = l_Lean_mkRawNatLit(v___x_2909_);
v___x_2911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74);
v___x_2913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76);
lean_inc_ref(v_r_2910_);
v___x_2914_ = l_Lean_Expr_app___override(v___x_2913_, v_r_2910_);
v___x_2915_ = l_Lean_mkApp3(v___x_2911_, v___x_2912_, v_r_2910_, v___x_2914_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 1, v___x_2915_);
lean_ctor_set(v___x_2894_, 0, v_arg_2699_);
v___x_2917_ = v___x_2894_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_arg_2699_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
return v___x_2918_;
}
}
}
}
}
else
{
lean_object* v_w_2921_; lean_object* v_bv_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2921_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2922_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2924_ = v_value_2604_;
v_isShared_2925_ = v_isSharedCheck_2950_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_bv_2922_);
lean_inc(v_w_2921_);
lean_dec(v_value_2604_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2950_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2926_ = lean_unsigned_to_nat(16u);
v___x_2927_ = lean_nat_dec_eq(v_w_2921_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
lean_dec(v_bv_2922_);
lean_dec_ref(v_arg_2699_);
v___x_2928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78);
v___x_2929_ = l_Nat_reprFast(v_w_2921_);
v___x_2930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
v___x_2931_ = l_Lean_MessageData_ofFormat(v___x_2930_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 7);
lean_ctor_set(v___x_2924_, 1, v___x_2931_);
lean_ctor_set(v___x_2924_, 0, v___x_2928_);
v___x_2933_ = v___x_2924_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2933_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2935_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2936_;
}
}
else
{
uint16_t v___x_2938_; lean_object* v___x_2939_; lean_object* v_r_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_dec(v_w_2921_);
v___x_2938_ = lean_uint16_of_nat_mk(v_bv_2922_);
v___x_2939_ = lean_uint16_to_nat(v___x_2938_);
v_r_2940_ = l_Lean_mkRawNatLit(v___x_2939_);
v___x_2941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80);
v___x_2943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82);
lean_inc_ref(v_r_2940_);
v___x_2944_ = l_Lean_Expr_app___override(v___x_2943_, v_r_2940_);
v___x_2945_ = l_Lean_mkApp3(v___x_2941_, v___x_2942_, v_r_2940_, v___x_2944_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2945_);
lean_ctor_set(v___x_2924_, 0, v_arg_2699_);
v___x_2947_ = v___x_2924_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_arg_2699_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
}
}
}
else
{
lean_object* v_w_2951_; lean_object* v_bv_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2951_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2952_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2954_ = v_value_2604_;
v_isShared_2955_ = v_isSharedCheck_2980_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_bv_2952_);
lean_inc(v_w_2951_);
lean_dec(v_value_2604_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2980_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_unsigned_to_nat(32u);
v___x_2957_ = lean_nat_dec_eq(v_w_2951_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
lean_dec(v_bv_2952_);
lean_dec_ref(v_arg_2699_);
v___x_2958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84);
v___x_2959_ = l_Nat_reprFast(v_w_2951_);
v___x_2960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v___x_2961_ = l_Lean_MessageData_ofFormat(v___x_2960_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 7);
lean_ctor_set(v___x_2954_, 1, v___x_2961_);
lean_ctor_set(v___x_2954_, 0, v___x_2958_);
v___x_2963_ = v___x_2954_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2965_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2966_;
}
}
else
{
uint32_t v___x_2968_; lean_object* v___x_2969_; lean_object* v_r_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
lean_dec(v_w_2951_);
v___x_2968_ = lean_uint32_of_nat_mk(v_bv_2952_);
v___x_2969_ = lean_uint32_to_nat(v___x_2968_);
v_r_2970_ = l_Lean_mkRawNatLit(v___x_2969_);
v___x_2971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86);
v___x_2973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88);
lean_inc_ref(v_r_2970_);
v___x_2974_ = l_Lean_Expr_app___override(v___x_2973_, v_r_2970_);
v___x_2975_ = l_Lean_mkApp3(v___x_2971_, v___x_2972_, v_r_2970_, v___x_2974_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2975_);
lean_ctor_set(v___x_2954_, 0, v_arg_2699_);
v___x_2977_ = v___x_2954_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_arg_2699_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
}
}
}
else
{
lean_object* v_w_2981_; lean_object* v_bv_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_2981_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2982_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2984_ = v_value_2604_;
v_isShared_2985_ = v_isSharedCheck_3010_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_bv_2982_);
lean_inc(v_w_2981_);
lean_dec(v_value_2604_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3010_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = lean_unsigned_to_nat(64u);
v___x_2987_ = lean_nat_dec_eq(v_w_2981_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_dec(v_bv_2982_);
lean_dec_ref(v_arg_2699_);
v___x_2988_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90);
v___x_2989_ = l_Nat_reprFast(v_w_2981_);
v___x_2990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
v___x_2991_ = l_Lean_MessageData_ofFormat(v___x_2990_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 7);
lean_ctor_set(v___x_2984_, 1, v___x_2991_);
lean_ctor_set(v___x_2984_, 0, v___x_2988_);
v___x_2993_ = v___x_2984_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2995_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_2996_;
}
}
else
{
uint64_t v___x_2998_; lean_object* v___x_2999_; lean_object* v_r_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
lean_dec(v_w_2981_);
v___x_2998_ = lean_uint64_of_nat_mk(v_bv_2982_);
v___x_2999_ = lean_uint64_to_nat(v___x_2998_);
v_r_3000_ = l_Lean_mkRawNatLit(v___x_2999_);
v___x_3001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_3002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92);
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94);
lean_inc_ref(v_r_3000_);
v___x_3004_ = l_Lean_Expr_app___override(v___x_3003_, v_r_3000_);
v___x_3005_ = l_Lean_mkApp3(v___x_3001_, v___x_3002_, v_r_3000_, v___x_3004_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_3005_);
lean_ctor_set(v___x_2984_, 0, v_arg_2699_);
v___x_3007_ = v___x_2984_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_arg_2699_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
}
}
}
else
{
lean_object* v_w_3011_; lean_object* v_bv_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_3011_ = lean_ctor_get(v_value_2604_, 0);
v_bv_3012_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3014_ = v_value_2604_;
v_isShared_3015_ = v_isSharedCheck_3042_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_bv_3012_);
lean_inc(v_w_3011_);
lean_dec(v_value_2604_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3042_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = lean_unsigned_to_nat(8u);
v___x_3017_ = lean_nat_dec_eq(v_w_3011_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_dec(v_bv_3012_);
lean_dec_ref(v_arg_2699_);
v___x_3018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96);
v___x_3019_ = l_Nat_reprFast(v_w_3011_);
v___x_3020_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
v___x_3021_ = l_Lean_MessageData_ofFormat(v___x_3020_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 7);
lean_ctor_set(v___x_3014_, 1, v___x_3021_);
lean_ctor_set(v___x_3014_, 0, v___x_3018_);
v___x_3023_ = v___x_3014_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_3025_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_3026_;
}
}
else
{
uint8_t v___x_3028_; uint8_t v___x_3029_; uint8_t v___x_3030_; 
lean_del_object(v___x_3014_);
lean_dec(v_w_3011_);
v___x_3028_ = lean_uint8_of_nat_mk(v_bv_3012_);
v___x_3029_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97);
v___x_3030_ = lean_int8_dec_le(v___x_3029_, v___x_3028_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_3032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99);
v___x_3033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101);
v___x_3034_ = lean_int8_to_int(v___x_3028_);
v___x_3035_ = lean_int_neg(v___x_3034_);
v___x_3036_ = l_Int_toNat(v___x_3035_);
lean_dec(v___x_3035_);
v___x_3037_ = l_Lean_instToExprInt8_mkNat(v___x_3036_);
v___x_3038_ = l_Lean_mkApp3(v___x_3031_, v___x_3032_, v___x_3033_, v___x_3037_);
v___y_2713_ = v___x_3038_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_int8_to_int(v___x_3028_);
v___x_3040_ = l_Int_toNat(v___x_3039_);
v___x_3041_ = l_Lean_instToExprInt8_mkNat(v___x_3040_);
v___y_2713_ = v___x_3041_;
goto v___jp_2712_;
}
}
}
}
}
else
{
lean_object* v_w_3043_; lean_object* v_bv_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_3043_ = lean_ctor_get(v_value_2604_, 0);
v_bv_3044_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3046_ = v_value_2604_;
v_isShared_3047_ = v_isSharedCheck_3074_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_bv_3044_);
lean_inc(v_w_3043_);
lean_dec(v_value_2604_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3074_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = lean_unsigned_to_nat(16u);
v___x_3049_ = lean_nat_dec_eq(v_w_3043_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_dec(v_bv_3044_);
lean_dec_ref(v_arg_2699_);
v___x_3050_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103);
v___x_3051_ = l_Nat_reprFast(v_w_3043_);
v___x_3052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
v___x_3053_ = l_Lean_MessageData_ofFormat(v___x_3052_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 7);
lean_ctor_set(v___x_3046_, 1, v___x_3053_);
lean_ctor_set(v___x_3046_, 0, v___x_3050_);
v___x_3055_ = v___x_3046_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_3057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_3057_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_3058_;
}
}
else
{
uint16_t v___x_3060_; uint16_t v___x_3061_; uint8_t v___x_3062_; 
lean_del_object(v___x_3046_);
lean_dec(v_w_3043_);
v___x_3060_ = lean_uint16_of_nat_mk(v_bv_3044_);
v___x_3061_ = lean_uint16_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104);
v___x_3062_ = lean_int16_dec_le(v___x_3061_, v___x_3060_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_3064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106);
v___x_3065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108);
v___x_3066_ = lean_int16_to_int(v___x_3060_);
v___x_3067_ = lean_int_neg(v___x_3066_);
v___x_3068_ = l_Int_toNat(v___x_3067_);
lean_dec(v___x_3067_);
v___x_3069_ = l_Lean_instToExprInt16_mkNat(v___x_3068_);
v___x_3070_ = l_Lean_mkApp3(v___x_3063_, v___x_3064_, v___x_3065_, v___x_3069_);
v___y_2709_ = v___x_3070_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_int16_to_int(v___x_3060_);
v___x_3072_ = l_Int_toNat(v___x_3071_);
v___x_3073_ = l_Lean_instToExprInt16_mkNat(v___x_3072_);
v___y_2709_ = v___x_3073_;
goto v___jp_2708_;
}
}
}
}
}
else
{
lean_object* v_w_3075_; lean_object* v_bv_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_3075_ = lean_ctor_get(v_value_2604_, 0);
v_bv_3076_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3078_ = v_value_2604_;
v_isShared_3079_ = v_isSharedCheck_3106_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_bv_3076_);
lean_inc(v_w_3075_);
lean_dec(v_value_2604_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3106_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = lean_unsigned_to_nat(32u);
v___x_3081_ = lean_nat_dec_eq(v_w_3075_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
lean_dec(v_bv_3076_);
lean_dec_ref(v_arg_2699_);
v___x_3082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110);
v___x_3083_ = l_Nat_reprFast(v_w_3075_);
v___x_3084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
v___x_3085_ = l_Lean_MessageData_ofFormat(v___x_3084_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 7);
lean_ctor_set(v___x_3078_, 1, v___x_3085_);
lean_ctor_set(v___x_3078_, 0, v___x_3082_);
v___x_3087_ = v___x_3078_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_3089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3087_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_3089_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_3090_;
}
}
else
{
uint32_t v___x_3092_; uint32_t v___x_3093_; uint8_t v___x_3094_; 
lean_del_object(v___x_3078_);
lean_dec(v_w_3075_);
v___x_3092_ = lean_uint32_of_nat_mk(v_bv_3076_);
v___x_3093_ = lean_uint32_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111);
v___x_3094_ = lean_int32_dec_le(v___x_3093_, v___x_3092_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3095_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113);
v___x_3097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115);
v___x_3098_ = lean_int32_to_int(v___x_3092_);
v___x_3099_ = lean_int_neg(v___x_3098_);
lean_dec(v___x_3098_);
v___x_3100_ = l_Int_toNat(v___x_3099_);
lean_dec(v___x_3099_);
v___x_3101_ = l_Lean_instToExprInt32_mkNat(v___x_3100_);
v___x_3102_ = l_Lean_mkApp3(v___x_3095_, v___x_3096_, v___x_3097_, v___x_3101_);
v___y_2705_ = v___x_3102_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_int32_to_int(v___x_3092_);
v___x_3104_ = l_Int_toNat(v___x_3103_);
lean_dec(v___x_3103_);
v___x_3105_ = l_Lean_instToExprInt32_mkNat(v___x_3104_);
v___y_2705_ = v___x_3105_;
goto v___jp_2704_;
}
}
}
}
}
else
{
lean_object* v_w_3107_; lean_object* v_bv_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v___x_2720_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_var_2603_);
v_w_3107_ = lean_ctor_get(v_value_2604_, 0);
v_bv_3108_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3110_ = v_value_2604_;
v_isShared_3111_ = v_isSharedCheck_3138_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_bv_3108_);
lean_inc(v_w_3107_);
lean_dec(v_value_2604_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3138_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = lean_unsigned_to_nat(64u);
v___x_3113_ = lean_nat_dec_eq(v_w_3107_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
lean_dec(v_bv_3108_);
lean_dec_ref(v_arg_2699_);
v___x_3114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117);
v___x_3115_ = l_Nat_reprFast(v_w_3107_);
v___x_3116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
v___x_3117_ = l_Lean_MessageData_ofFormat(v___x_3116_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set_tag(v___x_3110_, 7);
lean_ctor_set(v___x_3110_, 1, v___x_3117_);
lean_ctor_set(v___x_3110_, 0, v___x_3114_);
v___x_3119_ = v___x_3110_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_3121_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
return v___x_3122_;
}
}
else
{
uint64_t v___x_3124_; uint64_t v___x_3125_; uint8_t v___x_3126_; 
lean_del_object(v___x_3110_);
lean_dec(v_w_3107_);
v___x_3124_ = lean_uint64_of_nat_mk(v_bv_3108_);
v___x_3125_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118);
v___x_3126_ = lean_int64_dec_le(v___x_3125_, v___x_3124_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_3128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120);
v___x_3129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122);
v___x_3130_ = lean_int64_to_int_sint(v___x_3124_);
v___x_3131_ = lean_int_neg(v___x_3130_);
lean_dec(v___x_3130_);
v___x_3132_ = l_Int_toNat(v___x_3131_);
lean_dec(v___x_3131_);
v___x_3133_ = l_Lean_instToExprInt64_mkNat(v___x_3132_);
v___x_3134_ = l_Lean_mkApp3(v___x_3127_, v___x_3128_, v___x_3129_, v___x_3133_);
v___y_2701_ = v___x_3134_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_int64_to_int_sint(v___x_3124_);
v___x_3136_ = l_Int_toNat(v___x_3135_);
lean_dec(v___x_3135_);
v___x_3137_ = l_Lean_instToExprInt64_mkNat(v___x_3136_);
v___y_2701_ = v___x_3137_;
goto v___jp_2700_;
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_arg_2699_);
lean_ctor_set(v___x_2702_, 1, v___y_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_arg_2699_);
lean_ctor_set(v___x_2706_, 1, v___y_2705_);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
v___jp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_arg_2699_);
lean_ctor_set(v___x_2710_, 1, v___y_2709_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
v___jp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_arg_2699_);
lean_ctor_set(v___x_2714_, 1, v___y_2713_);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_inc_ref(v___y_2717_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_arg_2699_);
lean_ctor_set(v___x_2718_, 1, v___y_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
v___jp_2633_:
{
if (lean_obj_tag(v_var_2603_) == 5)
{
lean_object* v_fn_2640_; 
v_fn_2640_ = lean_ctor_get(v_var_2603_, 0);
if (lean_obj_tag(v_fn_2640_) == 4)
{
lean_object* v_declName_2641_; 
v_declName_2641_ = lean_ctor_get(v_fn_2640_, 0);
if (lean_obj_tag(v_declName_2641_) == 1)
{
lean_object* v_arg_2642_; lean_object* v_us_2643_; lean_object* v_pre_2644_; lean_object* v_str_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_arg_2642_ = lean_ctor_get(v_var_2603_, 1);
v_us_2643_ = lean_ctor_get(v_fn_2640_, 1);
v_pre_2644_ = lean_ctor_get(v_declName_2641_, 0);
v_str_2645_ = lean_ctor_get(v_declName_2641_, 1);
v___x_2646_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix;
v___x_2647_ = lean_string_dec_eq(v_str_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v_w_2648_; lean_object* v_bv_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2663_; 
v_w_2648_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2649_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2651_ = v_value_2604_;
v_isShared_2652_ = v_isSharedCheck_2663_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_bv_2649_);
lean_inc(v_w_2648_);
lean_dec(v_value_2604_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2663_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2654_ = l_Lean_mkNatLit(v_w_2648_);
v___x_2655_ = l_Lean_mkNatLit(v_bv_2649_);
v___x_2656_ = l_Lean_mkAppB(v___x_2653_, v___x_2654_, v___x_2655_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2656_);
lean_ctor_set(v___x_2651_, 0, v_var_2603_);
v___x_2658_ = v___x_2651_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_var_2603_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2658_);
v___x_2660_ = v___x_2631_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v___x_2664_; 
lean_inc(v_pre_2644_);
lean_inc(v_us_2643_);
lean_inc_ref(v_arg_2642_);
lean_dec_ref_known(v_var_2603_, 2);
lean_del_object(v___x_2631_);
v___x_2664_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_pre_2644_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2688_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2688_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2688_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
if (lean_obj_tag(v_a_2665_) == 5)
{
lean_object* v_val_2669_; lean_object* v_ctors_2670_; lean_object* v_bv_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2684_; 
v_val_2669_ = lean_ctor_get(v_a_2665_, 0);
lean_inc_ref(v_val_2669_);
lean_dec_ref_known(v_a_2665_, 1);
v_ctors_2670_ = lean_ctor_get(v_val_2669_, 4);
lean_inc(v_ctors_2670_);
lean_dec_ref(v_val_2669_);
v_bv_2671_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; 
v_unused_2685_ = lean_ctor_get(v_value_2604_, 0);
lean_dec(v_unused_2685_);
v___x_2673_ = v_value_2604_;
v_isShared_2674_ = v_isSharedCheck_2684_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_bv_2671_);
lean_dec(v_value_2604_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2684_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2675_ = lean_box(0);
v___x_2676_ = l_List_get_x21Internal___redArg(v___x_2675_, v_ctors_2670_, v_bv_2671_);
lean_dec(v_ctors_2670_);
v___x_2677_ = l_Lean_mkConst(v___x_2676_, v_us_2643_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 1, v___x_2677_);
lean_ctor_set(v___x_2673_, 0, v_arg_2642_);
v___x_2679_ = v___x_2673_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_arg_2642_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2679_);
v___x_2681_ = v___x_2667_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_del_object(v___x_2667_);
lean_dec(v_a_2665_);
lean_dec(v_us_2643_);
lean_dec_ref(v_arg_2642_);
lean_dec_ref(v_value_2604_);
v___x_2686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6);
v___x_2687_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v___x_2686_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_us_2643_);
lean_dec_ref(v_arg_2642_);
lean_dec_ref(v_value_2604_);
v_a_2689_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2664_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2664_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
else
{
lean_del_object(v___x_2631_);
goto v___jp_2612_;
}
}
else
{
lean_del_object(v___x_2631_);
goto v___jp_2612_;
}
}
else
{
lean_del_object(v___x_2631_);
goto v___jp_2612_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_value_2604_);
lean_dec_ref(v_var_2603_);
v_a_3140_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_2628_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_2628_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_w_3148_; lean_object* v_bv_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3161_; 
v_w_3148_ = lean_ctor_get(v_value_2604_, 0);
v_bv_3149_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3151_ = v_value_2604_;
v_isShared_3152_ = v_isSharedCheck_3161_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_bv_3149_);
lean_inc(v_w_3148_);
lean_dec(v_value_2604_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3161_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_3154_ = l_Lean_mkNatLit(v_w_3148_);
v___x_3155_ = l_Lean_mkNatLit(v_bv_3149_);
v___x_3156_ = l_Lean_mkAppB(v___x_3153_, v___x_3154_, v___x_3155_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v___x_3156_);
lean_ctor_set(v___x_3151_, 0, v_var_2603_);
v___x_3158_ = v___x_3151_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_var_2603_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
}
}
v___jp_2612_:
{
lean_object* v_w_2613_; lean_object* v_bv_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2626_; 
v_w_2613_ = lean_ctor_get(v_value_2604_, 0);
v_bv_2614_ = lean_ctor_get(v_value_2604_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_value_2604_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2616_ = v_value_2604_;
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_bv_2614_);
lean_inc(v_w_2613_);
lean_dec(v_value_2604_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2619_ = l_Lean_mkNatLit(v_w_2613_);
v___x_2620_ = l_Lean_mkNatLit(v_bv_2614_);
v___x_2621_ = l_Lean_mkAppB(v___x_2618_, v___x_2619_, v___x_2620_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v___x_2621_);
lean_ctor_set(v___x_2616_, 0, v_var_2603_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_var_2603_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object* v_var_3162_, lean_object* v_value_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_3162_, v_value_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_object* v_00_u03b1_3172_, lean_object* v_msg_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_3173_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(lean_object* v_00_u03b1_3182_, lean_object* v_msg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(v_00_u03b1_3182_, v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object* v_00_u03b1_3192_, lean_object* v_constName_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3202_, lean_object* v_constName_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(v_00_u03b1_3202_, v_constName_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3212_, lean_object* v_ref_3213_, lean_object* v_constName_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_3213_, v_constName_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3223_, lean_object* v_ref_3224_, lean_object* v_constName_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(v_00_u03b1_3223_, v_ref_3224_, v_constName_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v_ref_3224_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_3234_, lean_object* v_ref_3235_, lean_object* v_msg_3236_, lean_object* v_declHint_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_3235_, v_msg_3236_, v_declHint_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3246_, lean_object* v_ref_3247_, lean_object* v_msg_3248_, lean_object* v_declHint_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_3246_, v_ref_3247_, v_msg_3248_, v_declHint_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v_ref_3247_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_3258_, lean_object* v_declHint_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_3258_, v_declHint_3259_, v___y_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3268_, lean_object* v_declHint_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_3268_, v_declHint_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3278_, lean_object* v_ref_3279_, lean_object* v_msg_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_3279_, v_msg_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3289_, lean_object* v_ref_3290_, lean_object* v_msg_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_3289_, v_ref_3290_, v_msg_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v_ref_3290_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object* v_m_3300_, lean_object* v_query_3301_, lean_object* v_x_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_zero_3305_; uint8_t v_isZero_3306_; 
v_zero_3305_ = lean_unsigned_to_nat(0u);
v_isZero_3306_ = lean_nat_dec_eq(v_x_3303_, v_zero_3305_);
if (v_isZero_3306_ == 1)
{
lean_dec(v_x_3304_);
lean_dec(v_x_3303_);
if (lean_obj_tag(v_x_3302_) == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_box(2);
return v___x_3307_;
}
else
{
lean_object* v_val_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_val_3308_ = lean_ctor_get(v_x_3302_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_x_3302_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v_x_3302_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_val_3308_);
lean_dec(v_x_3302_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_val_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_keyArray_3316_; lean_object* v_valueArray_3317_; lean_object* v___x_3318_; uint8_t v_isSome_3319_; 
v_keyArray_3316_ = lean_ctor_get(v_m_3300_, 1);
v_valueArray_3317_ = lean_ctor_get(v_m_3300_, 2);
v___x_3318_ = lean_array_fget_borrowed(v_keyArray_3316_, v_x_3304_);
v_isSome_3319_ = lean_noption_is_some(v___x_3318_);
if (v_isSome_3319_ == 0)
{
lean_dec(v_x_3303_);
if (lean_obj_tag(v_x_3302_) == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_x_3304_);
return v___x_3320_;
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_x_3304_);
v_val_3321_ = lean_ctor_get(v_x_3302_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_x_3302_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v_x_3302_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_val_3321_);
lean_dec(v_x_3302_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_val_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
else
{
lean_object* v_one_3329_; lean_object* v_n_3330_; lean_object* v___y_3332_; 
v_one_3329_ = lean_unsigned_to_nat(1u);
v_n_3330_ = lean_nat_sub(v_x_3303_, v_one_3329_);
lean_dec(v_x_3303_);
if (v_isSome_3319_ == 0)
{
goto v___jp_3338_;
}
else
{
lean_object* v___x_3340_; uint8_t v_isSome_3341_; 
v___x_3340_ = lean_array_fget_borrowed(v_valueArray_3317_, v_x_3304_);
v_isSome_3341_ = lean_noption_is_some(v___x_3340_);
if (v_isSome_3341_ == 0)
{
goto v___jp_3338_;
}
else
{
lean_object* v_val_3342_; uint8_t v___x_3343_; 
lean_inc(v___x_3318_);
v_val_3342_ = lean_noption_get(v___x_3318_);
v___x_3343_ = lean_expr_eqv(v_val_3342_, v_query_3301_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
lean_dec(v_val_3342_);
v___x_3344_ = lean_array_get_size(v_keyArray_3316_);
v___x_3345_ = lean_nat_add(v_x_3304_, v_one_3329_);
lean_dec(v_x_3304_);
v___x_3346_ = lean_nat_dec_lt(v___x_3345_, v___x_3344_);
if (v___x_3346_ == 0)
{
lean_dec(v___x_3345_);
v_x_3303_ = v_n_3330_;
v_x_3304_ = v_zero_3305_;
goto _start;
}
else
{
v_x_3303_ = v_n_3330_;
v_x_3304_ = v___x_3345_;
goto _start;
}
}
else
{
lean_object* v_val_3349_; lean_object* v___x_3350_; 
lean_dec(v_n_3330_);
lean_dec(v_x_3302_);
lean_inc(v___x_3340_);
v_val_3349_ = lean_noption_get(v___x_3340_);
v___x_3350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3350_, 0, v_x_3304_);
lean_ctor_set(v___x_3350_, 1, v_val_3342_);
lean_ctor_set(v___x_3350_, 2, v_val_3349_);
return v___x_3350_;
}
}
}
v___jp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3333_ = lean_array_get_size(v_keyArray_3316_);
v___x_3334_ = lean_nat_add(v_x_3304_, v_one_3329_);
lean_dec(v_x_3304_);
v___x_3335_ = lean_nat_dec_lt(v___x_3334_, v___x_3333_);
if (v___x_3335_ == 0)
{
lean_dec(v___x_3334_);
v_x_3302_ = v___y_3332_;
v_x_3303_ = v_n_3330_;
v_x_3304_ = v_zero_3305_;
goto _start;
}
else
{
v_x_3302_ = v___y_3332_;
v_x_3303_ = v_n_3330_;
v_x_3304_ = v___x_3334_;
goto _start;
}
}
v___jp_3338_:
{
if (lean_obj_tag(v_x_3302_) == 0)
{
lean_object* v___x_3339_; 
lean_inc(v_x_3304_);
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_x_3304_);
v___y_3332_ = v___x_3339_;
goto v___jp_3331_;
}
else
{
v___y_3332_ = v_x_3302_;
goto v___jp_3331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object* v_m_3351_, lean_object* v_query_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_m_3351_, v_query_3352_, v_x_3353_, v_x_3354_, v_x_3355_);
lean_dec_ref(v_query_3352_);
lean_dec_ref(v_m_3351_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object* v_m_3357_, lean_object* v_query_3358_){
_start:
{
lean_object* v_keyArray_3359_; lean_object* v___x_3360_; uint64_t v___x_3361_; uint64_t v___x_3362_; uint64_t v___x_3363_; uint64_t v_fold_3364_; uint64_t v___x_3365_; uint64_t v___x_3366_; uint64_t v___x_3367_; size_t v___x_3368_; size_t v___x_3369_; size_t v___x_3370_; size_t v___x_3371_; size_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_keyArray_3359_ = lean_ctor_get(v_m_3357_, 1);
v___x_3360_ = lean_array_get_size(v_keyArray_3359_);
v___x_3361_ = l_Lean_Expr_hash(v_query_3358_);
v___x_3362_ = 32ULL;
v___x_3363_ = lean_uint64_shift_right(v___x_3361_, v___x_3362_);
v_fold_3364_ = lean_uint64_xor(v___x_3361_, v___x_3363_);
v___x_3365_ = 16ULL;
v___x_3366_ = lean_uint64_shift_right(v_fold_3364_, v___x_3365_);
v___x_3367_ = lean_uint64_xor(v_fold_3364_, v___x_3366_);
v___x_3368_ = lean_uint64_to_usize(v___x_3367_);
v___x_3369_ = lean_usize_of_nat(v___x_3360_);
v___x_3370_ = ((size_t)1ULL);
v___x_3371_ = lean_usize_sub(v___x_3369_, v___x_3370_);
v___x_3372_ = lean_usize_land(v___x_3368_, v___x_3371_);
v___x_3373_ = lean_usize_to_nat(v___x_3372_);
v___x_3374_ = lean_box(0);
v___x_3375_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_m_3357_, v_query_3358_, v___x_3374_, v___x_3360_, v___x_3373_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg___boxed(lean_object* v_m_3376_, lean_object* v_query_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3376_, v_query_3377_);
lean_dec_ref(v_query_3377_);
lean_dec_ref(v_m_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(lean_object* v_b_3379_, lean_object* v_acc_3380_, lean_object* v_i_3381_){
_start:
{
lean_object* v___y_3383_; lean_object* v_keyArray_3391_; lean_object* v_valueArray_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v_keyArray_3391_ = lean_ctor_get(v_b_3379_, 1);
v_valueArray_3392_ = lean_ctor_get(v_b_3379_, 2);
v___x_3393_ = lean_array_get_size(v_keyArray_3391_);
v___x_3394_ = lean_nat_dec_lt(v_i_3381_, v___x_3393_);
if (v___x_3394_ == 0)
{
lean_dec(v_i_3381_);
return v_acc_3380_;
}
else
{
lean_object* v___x_3395_; uint8_t v_isSome_3396_; 
v___x_3395_ = lean_array_fget_borrowed(v_keyArray_3391_, v_i_3381_);
v_isSome_3396_ = lean_noption_is_some(v___x_3395_);
if (v_isSome_3396_ == 0)
{
goto v___jp_3387_;
}
else
{
lean_object* v___x_3397_; uint8_t v_isSome_3398_; 
v___x_3397_ = lean_array_fget_borrowed(v_valueArray_3392_, v_i_3381_);
v_isSome_3398_ = lean_noption_is_some(v___x_3397_);
if (v_isSome_3398_ == 0)
{
goto v___jp_3387_;
}
else
{
lean_object* v_val_3399_; lean_object* v_val_3400_; lean_object* v_i_3402_; lean_object* v___x_3407_; 
lean_inc(v___x_3395_);
v_val_3399_ = lean_noption_get(v___x_3395_);
lean_inc(v___x_3397_);
v_val_3400_ = lean_noption_get(v___x_3397_);
v___x_3407_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_acc_3380_, v_val_3399_);
switch(lean_obj_tag(v___x_3407_))
{
case 0:
{
lean_object* v_index_3408_; lean_object* v_size_3409_; lean_object* v___x_3410_; 
v_index_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_index_3408_);
lean_dec_ref_known(v___x_3407_, 3);
v_size_3409_ = lean_ctor_get(v_acc_3380_, 0);
lean_inc(v_size_3409_);
v___x_3410_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_3380_, v_size_3409_, v_index_3408_, v_val_3399_, v_val_3400_);
lean_dec(v_index_3408_);
v___y_3383_ = v___x_3410_;
goto v___jp_3382_;
}
case 1:
{
lean_object* v_index_3411_; 
v_index_3411_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_index_3411_);
lean_dec_ref_known(v___x_3407_, 1);
v_i_3402_ = v_index_3411_;
goto v___jp_3401_;
}
default: 
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_unsigned_to_nat(0u);
v___x_3413_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_3380_, v___x_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_index_3414_; 
v_index_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_index_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v_i_3402_ = v_index_3414_;
goto v___jp_3401_;
}
else
{
lean_dec(v_val_3400_);
lean_dec(v_val_3399_);
v___y_3383_ = v_acc_3380_;
goto v___jp_3382_;
}
}
}
v___jp_3401_:
{
lean_object* v_size_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_size_3403_ = lean_ctor_get(v_acc_3380_, 0);
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_add(v_size_3403_, v___x_3404_);
v___x_3406_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_3380_, v___x_3405_, v_i_3402_, v_val_3399_, v_val_3400_);
lean_dec(v_i_3402_);
v___y_3383_ = v___x_3406_;
goto v___jp_3382_;
}
}
}
}
v___jp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_unsigned_to_nat(1u);
v___x_3385_ = lean_nat_add(v_i_3381_, v___x_3384_);
lean_dec(v_i_3381_);
v_acc_3380_ = v___y_3383_;
v_i_3381_ = v___x_3385_;
goto _start;
}
v___jp_3387_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = lean_unsigned_to_nat(1u);
v___x_3389_ = lean_nat_add(v_i_3381_, v___x_3388_);
lean_dec(v_i_3381_);
v_i_3381_ = v___x_3389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_3415_, lean_object* v_acc_3416_, lean_object* v_i_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v_b_3415_, v_acc_3416_, v_i_3417_);
lean_dec_ref(v_b_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(lean_object* v_init_3419_, lean_object* v_b_3420_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v_b_3420_, v_init_3419_, v___x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg___boxed(lean_object* v_init_3423_, lean_object* v_b_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_init_3423_, v_b_3424_);
lean_dec_ref(v_b_3424_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(lean_object* v_m_3426_){
_start:
{
lean_object* v_keyArray_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v_cellCount_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v_target_3434_; lean_object* v___x_3435_; 
v_keyArray_3427_ = lean_ctor_get(v_m_3426_, 1);
v___x_3428_ = lean_array_get_size(v_keyArray_3427_);
v___x_3429_ = lean_unsigned_to_nat(2u);
v_cellCount_3430_ = lean_nat_mul(v___x_3428_, v___x_3429_);
v___x_3431_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_3430_);
v___x_3432_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3430_);
v___x_3433_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3430_);
v_target_3434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_3434_, 0, v___x_3431_);
lean_ctor_set(v_target_3434_, 1, v___x_3432_);
lean_ctor_set(v_target_3434_, 2, v___x_3433_);
v___x_3435_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_target_3434_, v_m_3426_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg___boxed(lean_object* v_m_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_m_3436_);
lean_dec_ref(v_m_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(lean_object* v_as_3438_, size_t v_sz_3439_, size_t v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_a_3450_; uint8_t v___x_3454_; 
v___x_3454_ = lean_usize_dec_lt(v_i_3440_, v_sz_3439_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_b_3441_);
return v___x_3455_;
}
else
{
lean_object* v_a_3456_; lean_object* v_fst_3457_; lean_object* v_snd_3458_; lean_object* v___x_3459_; 
v_a_3456_ = lean_array_uget_borrowed(v_as_3438_, v_i_3440_);
v_fst_3457_ = lean_ctor_get(v_a_3456_, 0);
v_snd_3458_ = lean_ctor_get(v_a_3456_, 1);
lean_inc(v_snd_3458_);
lean_inc(v_fst_3457_);
v___x_3459_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_3457_, v_snd_3458_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_fst_3461_; lean_object* v___x_3462_; lean_object* v_uninterpretedSymbols_3463_; lean_object* v_unusedRelevantHypotheses_3464_; lean_object* v_derivedEquations_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3552_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_fst_3461_ = lean_ctor_get(v_a_3460_, 0);
lean_inc(v_fst_3461_);
v___x_3462_ = lean_st_ref_take(v___y_3443_);
v_uninterpretedSymbols_3463_ = lean_ctor_get(v___x_3462_, 0);
v_unusedRelevantHypotheses_3464_ = lean_ctor_get(v___x_3462_, 1);
v_derivedEquations_3465_ = lean_ctor_get(v___x_3462_, 2);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3467_ = v___x_3462_;
v_isShared_3468_ = v_isSharedCheck_3552_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_derivedEquations_3465_);
lean_inc(v_unusedRelevantHypotheses_3464_);
lean_inc(v_uninterpretedSymbols_3463_);
lean_dec(v___x_3462_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3552_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3469_ = lean_array_push(v_derivedEquations_3465_, v_a_3460_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 2, v___x_3469_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_uninterpretedSymbols_3463_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_unusedRelevantHypotheses_3464_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_st_ref_put(v___y_3443_, v___x_3471_);
v___x_3473_ = lean_box(0);
if (lean_obj_tag(v_fst_3461_) == 1)
{
lean_object* v_fvarId_3474_; lean_object* v___x_3475_; 
v_fvarId_3474_ = lean_ctor_get(v_fst_3461_, 0);
lean_inc(v_fvarId_3474_);
lean_dec_ref_known(v_fst_3461_, 1);
v___x_3475_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvarId_3474_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v_fvarId_3474_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec_ref_known(v___x_3475_, 1);
v_a_3450_ = v___x_3473_;
goto v___jp_3449_;
}
else
{
return v___x_3475_;
}
}
else
{
lean_object* v___x_3476_; lean_object* v_uninterpretedSymbols_3477_; lean_object* v_unusedRelevantHypotheses_3478_; lean_object* v_derivedEquations_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3550_; 
v___x_3476_ = lean_st_ref_take(v___y_3443_);
v_uninterpretedSymbols_3477_ = lean_ctor_get(v___x_3476_, 0);
v_unusedRelevantHypotheses_3478_ = lean_ctor_get(v___x_3476_, 1);
v_derivedEquations_3479_ = lean_ctor_get(v___x_3476_, 2);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3481_ = v___x_3476_;
v_isShared_3482_ = v_isSharedCheck_3550_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_derivedEquations_3479_);
lean_inc(v_unusedRelevantHypotheses_3478_);
lean_inc(v_uninterpretedSymbols_3477_);
lean_dec(v___x_3476_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3550_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___y_3484_; lean_object* v___y_3490_; lean_object* v_i_3491_; lean_object* v___y_3497_; lean_object* v___y_3507_; lean_object* v_i_3508_; lean_object* v___x_3523_; 
v___x_3523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_uninterpretedSymbols_3477_, v_fst_3461_);
switch(lean_obj_tag(v___x_3523_))
{
case 0:
{
lean_dec_ref_known(v___x_3523_, 3);
lean_dec(v_fst_3461_);
v___y_3484_ = v_uninterpretedSymbols_3477_;
goto v___jp_3483_;
}
case 1:
{
lean_object* v_index_3524_; lean_object* v_size_3525_; lean_object* v_keyArray_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_index_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_index_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v_size_3525_ = lean_ctor_get(v_uninterpretedSymbols_3477_, 0);
v_keyArray_3526_ = lean_ctor_get(v_uninterpretedSymbols_3477_, 1);
v___x_3527_ = lean_unsigned_to_nat(1u);
v___x_3528_ = lean_nat_add(v_size_3525_, v___x_3527_);
v___x_3529_ = lean_array_get_size(v_keyArray_3526_);
v___x_3530_ = lean_nat_dec_lt(v___x_3528_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_dec(v___x_3528_);
lean_dec(v_index_3524_);
goto v___jp_3513_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3531_ = lean_unsigned_to_nat(4u);
v___x_3532_ = lean_nat_mul(v___x_3528_, v___x_3531_);
v___x_3533_ = lean_unsigned_to_nat(3u);
v___x_3534_ = lean_nat_mul(v___x_3529_, v___x_3533_);
v___x_3535_ = lean_nat_dec_le(v___x_3532_, v___x_3534_);
lean_dec(v___x_3534_);
lean_dec(v___x_3532_);
if (v___x_3535_ == 0)
{
lean_dec(v___x_3528_);
lean_dec(v_index_3524_);
goto v___jp_3513_;
}
else
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Std_DHashMap_Raw_setEntry___redArg(v_uninterpretedSymbols_3477_, v___x_3528_, v_index_3524_, v_fst_3461_, v___x_3473_);
lean_dec(v_index_3524_);
v___y_3484_ = v___x_3536_;
goto v___jp_3483_;
}
}
}
default: 
{
lean_object* v_size_3537_; lean_object* v_keyArray_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_size_3537_ = lean_ctor_get(v_uninterpretedSymbols_3477_, 0);
v_keyArray_3538_ = lean_ctor_get(v_uninterpretedSymbols_3477_, 1);
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_nat_add(v_size_3537_, v___x_3539_);
v___x_3541_ = lean_array_get_size(v_keyArray_3538_);
v___x_3542_ = lean_nat_dec_lt(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec(v___x_3540_);
v___x_3543_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_uninterpretedSymbols_3477_);
lean_dec_ref(v_uninterpretedSymbols_3477_);
v___y_3497_ = v___x_3543_;
goto v___jp_3496_;
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3544_ = lean_unsigned_to_nat(4u);
v___x_3545_ = lean_nat_mul(v___x_3540_, v___x_3544_);
lean_dec(v___x_3540_);
v___x_3546_ = lean_unsigned_to_nat(3u);
v___x_3547_ = lean_nat_mul(v___x_3541_, v___x_3546_);
v___x_3548_ = lean_nat_dec_le(v___x_3545_, v___x_3547_);
lean_dec(v___x_3547_);
lean_dec(v___x_3545_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_uninterpretedSymbols_3477_);
lean_dec_ref(v_uninterpretedSymbols_3477_);
v___y_3497_ = v___x_3549_;
goto v___jp_3496_;
}
else
{
v___y_3497_ = v_uninterpretedSymbols_3477_;
goto v___jp_3496_;
}
}
}
}
v___jp_3483_:
{
lean_object* v___x_3486_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___y_3484_);
v___x_3486_ = v___x_3481_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___y_3484_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_unusedRelevantHypotheses_3478_);
lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_derivedEquations_3479_);
v___x_3486_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_st_ref_put(v___y_3443_, v___x_3486_);
v_a_3450_ = v___x_3473_;
goto v___jp_3449_;
}
}
v___jp_3489_:
{
lean_object* v_size_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_size_3492_ = lean_ctor_get(v___y_3490_, 0);
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_add(v_size_3492_, v___x_3493_);
v___x_3495_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3490_, v___x_3494_, v_i_3491_, v_fst_3461_, v___x_3473_);
lean_dec(v_i_3491_);
v___y_3484_ = v___x_3495_;
goto v___jp_3483_;
}
v___jp_3496_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v___y_3497_, v_fst_3461_);
switch(lean_obj_tag(v___x_3498_))
{
case 0:
{
lean_object* v_index_3499_; lean_object* v_size_3500_; lean_object* v___x_3501_; 
v_index_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_index_3499_);
lean_dec_ref_known(v___x_3498_, 3);
v_size_3500_ = lean_ctor_get(v___y_3497_, 0);
lean_inc(v_size_3500_);
v___x_3501_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3497_, v_size_3500_, v_index_3499_, v_fst_3461_, v___x_3473_);
lean_dec(v_index_3499_);
v___y_3484_ = v___x_3501_;
goto v___jp_3483_;
}
case 1:
{
lean_object* v_index_3502_; 
v_index_3502_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_index_3502_);
lean_dec_ref_known(v___x_3498_, 1);
v___y_3490_ = v___y_3497_;
v_i_3491_ = v_index_3502_;
goto v___jp_3489_;
}
default: 
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3497_, v___x_3503_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_index_3505_; 
v_index_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_index_3505_);
lean_dec_ref_known(v___x_3504_, 1);
v___y_3490_ = v___y_3497_;
v_i_3491_ = v_index_3505_;
goto v___jp_3489_;
}
else
{
lean_dec(v_fst_3461_);
v___y_3484_ = v___y_3497_;
goto v___jp_3483_;
}
}
}
}
v___jp_3506_:
{
lean_object* v_size_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v_size_3509_ = lean_ctor_get(v___y_3507_, 0);
v___x_3510_ = lean_unsigned_to_nat(1u);
v___x_3511_ = lean_nat_add(v_size_3509_, v___x_3510_);
v___x_3512_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3507_, v___x_3511_, v_i_3508_, v_fst_3461_, v___x_3473_);
lean_dec(v_i_3508_);
v___y_3484_ = v___x_3512_;
goto v___jp_3483_;
}
v___jp_3513_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_uninterpretedSymbols_3477_);
lean_dec_ref(v_uninterpretedSymbols_3477_);
v___x_3515_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v___x_3514_, v_fst_3461_);
switch(lean_obj_tag(v___x_3515_))
{
case 0:
{
lean_object* v_index_3516_; lean_object* v_size_3517_; lean_object* v___x_3518_; 
v_index_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_index_3516_);
lean_dec_ref_known(v___x_3515_, 3);
v_size_3517_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_size_3517_);
v___x_3518_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3514_, v_size_3517_, v_index_3516_, v_fst_3461_, v___x_3473_);
lean_dec(v_index_3516_);
v___y_3484_ = v___x_3518_;
goto v___jp_3483_;
}
case 1:
{
lean_object* v_index_3519_; 
v_index_3519_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_index_3519_);
lean_dec_ref_known(v___x_3515_, 1);
v___y_3507_ = v___x_3514_;
v_i_3508_ = v_index_3519_;
goto v___jp_3506_;
}
default: 
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3514_, v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_index_3522_; 
v_index_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_index_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___y_3507_ = v___x_3514_;
v_i_3508_ = v_index_3522_;
goto v___jp_3506_;
}
else
{
lean_dec(v_fst_3461_);
v___y_3484_ = v___x_3514_;
goto v___jp_3483_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3459_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3459_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
v___jp_3449_:
{
size_t v___x_3451_; size_t v___x_3452_; 
v___x_3451_ = ((size_t)1ULL);
v___x_3452_ = lean_usize_add(v_i_3440_, v___x_3451_);
v_i_3440_ = v___x_3452_;
v_b_3441_ = v_a_3450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___boxed(lean_object* v_as_3561_, lean_object* v_sz_3562_, lean_object* v_i_3563_, lean_object* v_b_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
size_t v_sz_boxed_3572_; size_t v_i_boxed_3573_; lean_object* v_res_3574_; 
v_sz_boxed_3572_ = lean_unbox_usize(v_sz_3562_);
lean_dec(v_sz_3562_);
v_i_boxed_3573_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_res_3574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(v_as_3561_, v_sz_boxed_3572_, v_i_boxed_3573_, v_b_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_as_3561_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_equations_3582_; lean_object* v___x_3583_; size_t v_sz_3584_; size_t v___x_3585_; lean_object* v___x_3586_; 
v_equations_3582_ = lean_ctor_get(v_a_3575_, 2);
v___x_3583_ = lean_box(0);
v_sz_3584_ = lean_array_size(v_equations_3582_);
v___x_3585_ = ((size_t)0ULL);
v___x_3586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(v_equations_3582_, v_sz_3584_, v___x_3585_, v___x_3583_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v___x_3586_, 0);
lean_dec(v_unused_3594_);
v___x_3588_ = v___x_3586_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_dec(v___x_3586_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v___x_3583_);
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3583_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
else
{
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object* v_00_u03b2_3603_, lean_object* v_m_3604_, lean_object* v_query_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3604_, v_query_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___boxed(lean_object* v_00_u03b2_3607_, lean_object* v_m_3608_, lean_object* v_query_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(v_00_u03b2_3607_, v_m_3608_, v_query_3609_);
lean_dec_ref(v_query_3609_);
lean_dec_ref(v_m_3608_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object* v_00_u03b2_3611_, lean_object* v_m_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_m_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___boxed(lean_object* v_00_u03b2_3614_, lean_object* v_m_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_00_u03b2_3614_, v_m_3615_);
lean_dec_ref(v_m_3615_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object* v_00_u03b2_3617_, lean_object* v_m_3618_, lean_object* v_query_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_m_3618_, v_query_3619_, v_x_3620_, v_x_3621_, v_x_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3625_, lean_object* v_m_3626_, lean_object* v_query_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_3625_, v_m_3626_, v_query_3627_, v_x_3628_, v_x_3629_, v_x_3630_, v_x_3631_);
lean_dec_ref(v_query_3627_);
lean_dec_ref(v_m_3626_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(lean_object* v_00_u03b2_3633_, lean_object* v_init_3634_, lean_object* v_b_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_init_3634_, v_b_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3637_, lean_object* v_init_3638_, lean_object* v_b_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(v_00_u03b2_3637_, v_init_3638_, v_b_3639_);
lean_dec_ref(v_b_3639_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3641_, lean_object* v_b_3642_, lean_object* v_acc_3643_, lean_object* v_i_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v_b_3642_, v_acc_3643_, v_i_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3646_, lean_object* v_b_3647_, lean_object* v_acc_3648_, lean_object* v_i_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(v_00_u03b2_3646_, v_b_3647_, v_acc_3648_, v_i_3649_);
lean_dec_ref(v_b_3647_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object* v_b_3651_, lean_object* v_acc_3652_, lean_object* v_i_3653_){
_start:
{
lean_object* v_keyArray_3658_; lean_object* v_valueArray_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_keyArray_3658_ = lean_ctor_get(v_b_3651_, 1);
v_valueArray_3659_ = lean_ctor_get(v_b_3651_, 2);
v___x_3660_ = lean_array_get_size(v_keyArray_3658_);
v___x_3661_ = lean_nat_dec_lt(v_i_3653_, v___x_3660_);
if (v___x_3661_ == 0)
{
lean_dec(v_i_3653_);
lean_inc(v_acc_3652_);
return v_acc_3652_;
}
else
{
lean_object* v___x_3662_; uint8_t v_isSome_3663_; 
v___x_3662_ = lean_array_fget_borrowed(v_keyArray_3658_, v_i_3653_);
v_isSome_3663_ = lean_noption_is_some(v___x_3662_);
if (v_isSome_3663_ == 0)
{
goto v___jp_3654_;
}
else
{
lean_object* v___x_3664_; uint8_t v_isSome_3665_; 
v___x_3664_ = lean_array_fget_borrowed(v_valueArray_3659_, v_i_3653_);
v_isSome_3665_ = lean_noption_is_some(v___x_3664_);
if (v_isSome_3665_ == 0)
{
goto v___jp_3654_;
}
else
{
lean_object* v_val_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_inc(v___x_3662_);
v_val_3666_ = lean_noption_get(v___x_3662_);
v___x_3667_ = lean_unsigned_to_nat(1u);
v___x_3668_ = lean_nat_add(v_i_3653_, v___x_3667_);
lean_dec(v_i_3653_);
v___x_3669_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_b_3651_, v_acc_3652_, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3670_, 0, v_val_3666_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
return v___x_3670_;
}
}
}
v___jp_3654_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_unsigned_to_nat(1u);
v___x_3656_ = lean_nat_add(v_i_3653_, v___x_3655_);
lean_dec(v_i_3653_);
v_i_3653_ = v___x_3656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object* v_b_3671_, lean_object* v_acc_3672_, lean_object* v_i_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_b_3671_, v_acc_3672_, v_i_3673_);
lean_dec(v_acc_3672_);
lean_dec_ref(v_b_3671_);
return v_res_3674_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__0));
v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg(lean_object* v_as_x27_3678_, lean_object* v_b_3679_){
_start:
{
if (lean_obj_tag(v_as_x27_3678_) == 0)
{
lean_object* v___x_3680_; 
v___x_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3680_, 0, v_b_3679_);
return v___x_3680_;
}
else
{
lean_object* v_head_3681_; lean_object* v_tail_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_head_3681_ = lean_ctor_get(v_as_x27_3678_, 0);
v_tail_3682_ = lean_ctor_get(v_as_x27_3678_, 1);
v___x_3683_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1);
lean_inc(v_head_3681_);
v___x_3684_ = l_Lean_MessageData_ofExpr(v_head_3681_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v_b_3679_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v_as_x27_3678_ = v_tail_3682_;
v_b_3679_ = v___x_3686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___boxed(lean_object* v_as_x27_3688_, lean_object* v_b_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg(v_as_x27_3688_, v_b_3689_);
lean_dec(v_as_x27_3688_);
return v_res_3690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object* v_d_3694_){
_start:
{
lean_object* v_uninterpretedSymbols_3695_; lean_object* v_size_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v_uninterpretedSymbols_3695_ = lean_ctor_get(v_d_3694_, 0);
v_size_3696_ = lean_ctor_get(v_uninterpretedSymbols_3695_, 0);
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = lean_nat_dec_eq(v_size_3696_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3699_ = lean_box(0);
v___x_3700_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_uninterpretedSymbols_3695_, v___x_3699_, v___x_3697_);
v___x_3701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
v___x_3702_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg(v___x_3700_, v___x_3701_);
lean_dec(v___x_3700_);
return v___x_3702_;
}
else
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_box(0);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object* v_d_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_3704_);
lean_dec_ref(v_d_3704_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object* v_as_3706_, lean_object* v_as_x27_3707_, lean_object* v_b_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg(v_as_x27_3707_, v_b_3708_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object* v_as_3711_, lean_object* v_as_x27_3712_, lean_object* v_b_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_as_3711_, v_as_x27_3712_, v_b_3713_, v_a_3714_);
lean_dec(v_as_x27_3712_);
lean_dec(v_as_3711_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object* v_b_3716_, lean_object* v_acc_3717_, lean_object* v_i_3718_){
_start:
{
lean_object* v_keyArray_3723_; lean_object* v_valueArray_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v_keyArray_3723_ = lean_ctor_get(v_b_3716_, 1);
v_valueArray_3724_ = lean_ctor_get(v_b_3716_, 2);
v___x_3725_ = lean_array_get_size(v_keyArray_3723_);
v___x_3726_ = lean_nat_dec_lt(v_i_3718_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_dec(v_i_3718_);
lean_inc(v_acc_3717_);
return v_acc_3717_;
}
else
{
lean_object* v___x_3727_; uint8_t v_isSome_3728_; 
v___x_3727_ = lean_array_fget_borrowed(v_keyArray_3723_, v_i_3718_);
v_isSome_3728_ = lean_noption_is_some(v___x_3727_);
if (v_isSome_3728_ == 0)
{
goto v___jp_3719_;
}
else
{
lean_object* v___x_3729_; uint8_t v_isSome_3730_; 
v___x_3729_ = lean_array_fget_borrowed(v_valueArray_3724_, v_i_3718_);
v_isSome_3730_ = lean_noption_is_some(v___x_3729_);
if (v_isSome_3730_ == 0)
{
goto v___jp_3719_;
}
else
{
lean_object* v_val_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_inc(v___x_3727_);
v_val_3731_ = lean_noption_get(v___x_3727_);
v___x_3732_ = lean_unsigned_to_nat(1u);
v___x_3733_ = lean_nat_add(v_i_3718_, v___x_3732_);
lean_dec(v_i_3718_);
v___x_3734_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_b_3716_, v_acc_3717_, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_val_3731_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
return v___x_3735_;
}
}
}
v___jp_3719_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3721_ = lean_nat_add(v_i_3718_, v___x_3720_);
lean_dec(v_i_3718_);
v_i_3718_ = v___x_3721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object* v_b_3736_, lean_object* v_acc_3737_, lean_object* v_i_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_b_3736_, v_acc_3737_, v_i_3738_);
lean_dec(v_acc_3737_);
lean_dec_ref(v_b_3736_);
return v_res_3739_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__0));
v___x_3742_ = l_Lean_stringToMessageData(v___x_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg(lean_object* v_as_x27_3743_, lean_object* v_b_3744_){
_start:
{
if (lean_obj_tag(v_as_x27_3743_) == 0)
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_b_3744_);
return v___x_3745_;
}
else
{
lean_object* v_head_3746_; lean_object* v_tail_3747_; lean_object* v_type_3748_; lean_object* v_source_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v_head_3746_ = lean_ctor_get(v_as_x27_3743_, 0);
v_tail_3747_ = lean_ctor_get(v_as_x27_3743_, 1);
v_type_3748_ = lean_ctor_get(v_head_3746_, 1);
v_source_3749_ = lean_ctor_get(v_head_3746_, 3);
v___x_3750_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___redArg___closed__1);
lean_inc_ref(v_type_3748_);
v___x_3751_ = l_Lean_MessageData_ofExpr(v_type_3748_);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___closed__1);
v___x_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
lean_inc(v_source_3749_);
v___x_3755_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v_source_3749_);
v___x_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_b_3744_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v_as_x27_3743_ = v_tail_3747_;
v_b_3744_ = v___x_3757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg___boxed(lean_object* v_as_x27_3759_, lean_object* v_b_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg(v_as_x27_3759_, v_b_3760_);
lean_dec(v_as_x27_3759_);
return v_res_3761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0));
v___x_3764_ = l_Lean_stringToMessageData(v___x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object* v_d_3765_){
_start:
{
lean_object* v_unusedRelevantHypotheses_3766_; lean_object* v_size_3767_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
v_unusedRelevantHypotheses_3766_ = lean_ctor_get(v_d_3765_, 1);
v_size_3767_ = lean_ctor_get(v_unusedRelevantHypotheses_3766_, 0);
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = lean_nat_dec_eq(v_size_3767_, v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3770_ = lean_box(0);
v___x_3771_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_unusedRelevantHypotheses_3766_, v___x_3770_, v___x_3768_);
v___x_3772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
v___x_3773_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg(v___x_3771_, v___x_3772_);
lean_dec(v___x_3771_);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_box(0);
return v___x_3774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object* v_d_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_3775_);
lean_dec_ref(v_d_3775_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object* v_as_3777_, lean_object* v_as_x27_3778_, lean_object* v_b_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___redArg(v_as_x27_3778_, v_b_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* v_as_3782_, lean_object* v_as_x27_3783_, lean_object* v_b_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_as_3782_, v_as_x27_3783_, v_b_3784_, v_a_3785_);
lean_dec(v_as_x27_3783_);
lean_dec(v_as_3782_);
return v_res_3786_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0));
v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2));
v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object* v_as_3802_, size_t v_i_3803_, size_t v_stop_3804_, lean_object* v_b_3805_){
_start:
{
uint8_t v___x_3806_; 
v___x_3806_ = lean_usize_dec_eq(v_i_3803_, v_stop_3804_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; 
v___x_3807_ = lean_array_uget_borrowed(v_as_3802_, v_i_3803_);
v___x_3808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v_b_3805_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
lean_inc(v___x_3807_);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3807_);
v___x_3811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = ((size_t)1ULL);
v___x_3814_ = lean_usize_add(v_i_3803_, v___x_3813_);
v_i_3803_ = v___x_3814_;
v_b_3805_ = v___x_3812_;
goto _start;
}
else
{
return v_b_3805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object* v_as_3816_, lean_object* v_i_3817_, lean_object* v_stop_3818_, lean_object* v_b_3819_){
_start:
{
size_t v_i_boxed_3820_; size_t v_stop_boxed_3821_; lean_object* v_res_3822_; 
v_i_boxed_3820_ = lean_unbox_usize(v_i_3817_);
lean_dec(v_i_3817_);
v_stop_boxed_3821_ = lean_unbox_usize(v_stop_3818_);
lean_dec(v_stop_3818_);
v_res_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_3816_, v_i_boxed_3820_, v_stop_boxed_3821_, v_b_3819_);
lean_dec_ref(v_as_3816_);
return v_res_3822_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0));
v___x_3825_ = l_Lean_stringToMessageData(v___x_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object* v_as_3826_, size_t v_i_3827_, size_t v_stop_3828_, lean_object* v_b_3829_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_usize_dec_eq(v_i_3827_, v_stop_3828_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v_fst_3832_; lean_object* v_snd_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3850_; 
v___x_3831_ = lean_array_uget(v_as_3826_, v_i_3827_);
v_fst_3832_ = lean_ctor_get(v___x_3831_, 0);
v_snd_3833_ = lean_ctor_get(v___x_3831_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3835_ = v___x_3831_;
v_isShared_3836_ = v_isSharedCheck_3850_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_snd_3833_);
lean_inc(v_fst_3832_);
lean_dec(v___x_3831_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3850_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3837_ = l_Lean_MessageData_ofExpr(v_fst_3832_);
v___x_3838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 7);
lean_ctor_set(v___x_3835_, 1, v___x_3838_);
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3840_ = v___x_3835_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; size_t v___x_3846_; size_t v___x_3847_; 
v___x_3841_ = l_Lean_MessageData_ofExpr(v_snd_3833_);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v_b_3829_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3827_, v___x_3846_);
v_i_3827_ = v___x_3847_;
v_b_3829_ = v___x_3845_;
goto _start;
}
}
}
else
{
return v_b_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object* v_as_3851_, lean_object* v_i_3852_, lean_object* v_stop_3853_, lean_object* v_b_3854_){
_start:
{
size_t v_i_boxed_3855_; size_t v_stop_boxed_3856_; lean_object* v_res_3857_; 
v_i_boxed_3855_ = lean_unbox_usize(v_i_3852_);
lean_dec(v_i_3852_);
v_stop_boxed_3856_ = lean_unbox_usize(v_stop_3853_);
lean_dec(v_stop_3853_);
v_res_3857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_3851_, v_i_boxed_3855_, v_stop_boxed_3856_, v_b_3854_);
lean_dec_ref(v_as_3851_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object* v_a_3858_, lean_object* v_x_3859_, lean_object* v_x_3860_){
_start:
{
if (lean_obj_tag(v_x_3860_) == 0)
{
lean_dec_ref(v_a_3858_);
return v_x_3859_;
}
else
{
lean_object* v_head_3861_; lean_object* v_tail_3862_; lean_object* v___x_3863_; 
v_head_3861_ = lean_ctor_get(v_x_3860_, 0);
lean_inc(v_head_3861_);
v_tail_3862_ = lean_ctor_get(v_x_3860_, 1);
lean_inc(v_tail_3862_);
lean_dec_ref_known(v_x_3860_, 2);
lean_inc_ref(v_a_3858_);
v___x_3863_ = lean_apply_1(v_head_3861_, v_a_3858_);
if (lean_obj_tag(v___x_3863_) == 1)
{
lean_object* v_val_3864_; lean_object* v___x_3865_; 
v_val_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_val_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3865_ = lean_array_push(v_x_3859_, v_val_3864_);
v_x_3859_ = v___x_3865_;
v_x_3860_ = v_tail_3862_;
goto _start;
}
else
{
lean_dec(v___x_3863_);
v_x_3860_ = v_tail_3862_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1));
v___x_3872_ = l_Lean_stringToMessageData(v___x_3871_);
return v___x_3872_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3));
v___x_3875_ = l_Lean_stringToMessageData(v___x_3874_);
return v___x_3875_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4);
v___x_3877_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
lean_ctor_set(v___x_3878_, 1, v___x_3876_);
return v___x_3878_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6));
v___x_3881_ = l_Lean_stringToMessageData(v___x_3880_);
return v___x_3881_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8));
v___x_3884_ = l_Lean_stringToMessageData(v___x_3883_);
return v___x_3884_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9);
v___x_3886_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___x_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object* v_counterExample_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed), 7, 0);
v___x_3895_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_3894_, v_counterExample_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3947_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3947_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3947_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_err_3901_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3925_ = lean_unsigned_to_nat(0u);
v___x_3926_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0));
v___x_3927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers));
lean_inc(v_a_3896_);
v___x_3928_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3896_, v___x_3926_, v___x_3927_);
v___x_3929_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3930_ = lean_array_get_size(v___x_3928_);
v___x_3931_ = lean_nat_dec_eq(v___x_3930_, v___x_3925_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___y_3934_; uint8_t v___x_3938_; 
v___x_3932_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5);
v___x_3938_ = lean_nat_dec_lt(v___x_3925_, v___x_3930_);
if (v___x_3938_ == 0)
{
lean_dec_ref(v___x_3928_);
v___y_3934_ = v___x_3929_;
goto v___jp_3933_;
}
else
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_nat_dec_le(v___x_3930_, v___x_3930_);
if (v___x_3939_ == 0)
{
if (v___x_3938_ == 0)
{
lean_dec_ref(v___x_3928_);
v___y_3934_ = v___x_3929_;
goto v___jp_3933_;
}
else
{
size_t v___x_3940_; size_t v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = ((size_t)0ULL);
v___x_3941_ = lean_usize_of_nat(v___x_3930_);
v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3928_, v___x_3940_, v___x_3941_, v___x_3929_);
lean_dec_ref(v___x_3928_);
v___y_3934_ = v___x_3942_;
goto v___jp_3933_;
}
}
else
{
size_t v___x_3943_; size_t v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = ((size_t)0ULL);
v___x_3944_ = lean_usize_of_nat(v___x_3930_);
v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3928_, v___x_3943_, v___x_3944_, v___x_3929_);
lean_dec_ref(v___x_3928_);
v___y_3934_ = v___x_3945_;
goto v___jp_3933_;
}
}
v___jp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3932_);
lean_ctor_set(v___x_3935_, 1, v___y_3934_);
v___x_3936_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7);
v___x_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v_err_3901_ = v___x_3937_;
goto v___jp_3900_;
}
}
else
{
lean_object* v___x_3946_; 
lean_dec_ref(v___x_3928_);
v___x_3946_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10);
v_err_3901_ = v___x_3946_;
goto v___jp_3900_;
}
v___jp_3900_:
{
lean_object* v_derivedEquations_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; 
v_derivedEquations_3902_ = lean_ctor_get(v_a_3896_, 2);
lean_inc_ref(v_derivedEquations_3902_);
lean_dec(v_a_3896_);
v___x_3903_ = lean_unsigned_to_nat(0u);
v___x_3904_ = lean_array_get_size(v_derivedEquations_3902_);
v___x_3905_ = lean_nat_dec_lt(v___x_3903_, v___x_3904_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3907_; 
lean_dec_ref(v_derivedEquations_3902_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v_err_3901_);
v___x_3907_ = v___x_3898_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_err_3901_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
else
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_nat_dec_le(v___x_3904_, v___x_3904_);
if (v___x_3909_ == 0)
{
if (v___x_3905_ == 0)
{
lean_object* v___x_3911_; 
lean_dec_ref(v_derivedEquations_3902_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v_err_3901_);
v___x_3911_ = v___x_3898_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_err_3901_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
else
{
size_t v___x_3913_; size_t v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3913_ = ((size_t)0ULL);
v___x_3914_ = lean_usize_of_nat(v___x_3904_);
v___x_3915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3902_, v___x_3913_, v___x_3914_, v_err_3901_);
lean_dec_ref(v_derivedEquations_3902_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3915_);
v___x_3917_ = v___x_3898_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
else
{
size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3919_ = ((size_t)0ULL);
v___x_3920_ = lean_usize_of_nat(v___x_3904_);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3902_, v___x_3919_, v___x_3920_, v_err_3901_);
lean_dec_ref(v_derivedEquations_3902_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3921_);
v___x_3923_ = v___x_3898_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
v_a_3948_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3895_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3895_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object* v_counterExample_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
return v_res_3962_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
}
#ifdef __cplusplus
}
#endif

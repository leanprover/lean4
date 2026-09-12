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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\n  - "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "It abstracted the following unsupported expressions as opaque variables:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " derived via "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "The following potentially relevant hypotheses could not be used:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(lean_object* v_k_25_, lean_object* v_v_26_, lean_object* v_t_27_){
_start:
{
if (lean_obj_tag(v_t_27_) == 0)
{
lean_object* v_size_28_; lean_object* v_k_29_; lean_object* v_v_30_; lean_object* v_l_31_; lean_object* v_r_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_313_; 
v_size_28_ = lean_ctor_get(v_t_27_, 0);
v_k_29_ = lean_ctor_get(v_t_27_, 1);
v_v_30_ = lean_ctor_get(v_t_27_, 2);
v_l_31_ = lean_ctor_get(v_t_27_, 3);
v_r_32_ = lean_ctor_get(v_t_27_, 4);
v_isSharedCheck_313_ = !lean_is_exclusive(v_t_27_);
if (v_isSharedCheck_313_ == 0)
{
v___x_34_ = v_t_27_;
v_isShared_35_ = v_isSharedCheck_313_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_r_32_);
lean_inc(v_l_31_);
lean_inc(v_v_30_);
lean_inc(v_k_29_);
lean_inc(v_size_28_);
lean_dec(v_t_27_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_313_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
uint8_t v___x_36_; 
v___x_36_ = lean_nat_dec_lt(v_k_25_, v_k_29_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; 
v___x_37_ = lean_nat_dec_eq(v_k_25_, v_k_29_);
if (v___x_37_ == 0)
{
lean_object* v_impl_38_; lean_object* v___x_39_; 
lean_dec(v_size_28_);
v_impl_38_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_25_, v_v_26_, v_r_32_);
v___x_39_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_31_) == 0)
{
lean_object* v_size_40_; lean_object* v_size_41_; lean_object* v_k_42_; lean_object* v_v_43_; lean_object* v_l_44_; lean_object* v_r_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_size_40_ = lean_ctor_get(v_l_31_, 0);
v_size_41_ = lean_ctor_get(v_impl_38_, 0);
lean_inc(v_size_41_);
v_k_42_ = lean_ctor_get(v_impl_38_, 1);
lean_inc(v_k_42_);
v_v_43_ = lean_ctor_get(v_impl_38_, 2);
lean_inc(v_v_43_);
v_l_44_ = lean_ctor_get(v_impl_38_, 3);
lean_inc(v_l_44_);
v_r_45_ = lean_ctor_get(v_impl_38_, 4);
lean_inc(v_r_45_);
v___x_46_ = lean_unsigned_to_nat(3u);
v___x_47_ = lean_nat_mul(v___x_46_, v_size_40_);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v_size_41_);
lean_dec(v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
lean_dec(v_r_45_);
lean_dec(v_l_44_);
lean_dec(v_v_43_);
lean_dec(v_k_42_);
v___x_49_ = lean_nat_add(v___x_39_, v_size_40_);
v___x_50_ = lean_nat_add(v___x_49_, v_size_41_);
lean_dec(v_size_41_);
lean_dec(v___x_49_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_impl_38_);
lean_ctor_set(v___x_34_, 0, v___x_50_);
v___x_52_ = v___x_34_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_l_31_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_impl_38_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
else
{
lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_117_; 
v_isSharedCheck_117_ = !lean_is_exclusive(v_impl_38_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; lean_object* v_unused_119_; lean_object* v_unused_120_; lean_object* v_unused_121_; lean_object* v_unused_122_; 
v_unused_118_ = lean_ctor_get(v_impl_38_, 4);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_impl_38_, 3);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_impl_38_, 2);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_impl_38_, 1);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_impl_38_, 0);
lean_dec(v_unused_122_);
v___x_55_ = v_impl_38_;
v_isShared_56_ = v_isSharedCheck_117_;
goto v_resetjp_54_;
}
else
{
lean_dec(v_impl_38_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_117_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_size_57_; lean_object* v_k_58_; lean_object* v_v_59_; lean_object* v_l_60_; lean_object* v_r_61_; lean_object* v_size_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_size_57_ = lean_ctor_get(v_l_44_, 0);
v_k_58_ = lean_ctor_get(v_l_44_, 1);
v_v_59_ = lean_ctor_get(v_l_44_, 2);
v_l_60_ = lean_ctor_get(v_l_44_, 3);
v_r_61_ = lean_ctor_get(v_l_44_, 4);
v_size_62_ = lean_ctor_get(v_r_45_, 0);
v___x_63_ = lean_unsigned_to_nat(2u);
v___x_64_ = lean_nat_mul(v___x_63_, v_size_62_);
v___x_65_ = lean_nat_dec_lt(v_size_57_, v___x_64_);
lean_dec(v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_93_; 
lean_inc(v_r_61_);
lean_inc(v_l_60_);
lean_inc(v_v_59_);
lean_inc(v_k_58_);
v_isSharedCheck_93_ = !lean_is_exclusive(v_l_44_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; 
v_unused_94_ = lean_ctor_get(v_l_44_, 4);
lean_dec(v_unused_94_);
v_unused_95_ = lean_ctor_get(v_l_44_, 3);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_l_44_, 2);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_l_44_, 1);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_l_44_, 0);
lean_dec(v_unused_98_);
v___x_67_ = v_l_44_;
v_isShared_68_ = v_isSharedCheck_93_;
goto v_resetjp_66_;
}
else
{
lean_dec(v_l_44_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_93_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_83_; 
v___x_69_ = lean_nat_add(v___x_39_, v_size_40_);
v___x_70_ = lean_nat_add(v___x_69_, v_size_41_);
lean_dec(v_size_41_);
if (lean_obj_tag(v_l_60_) == 0)
{
lean_object* v_size_91_; 
v_size_91_ = lean_ctor_get(v_l_60_, 0);
lean_inc(v_size_91_);
v___y_83_ = v_size_91_;
goto v___jp_82_;
}
else
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v___y_83_ = v___x_92_;
goto v___jp_82_;
}
v___jp_71_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = lean_nat_add(v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec(v___y_73_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v_r_45_);
lean_ctor_set(v___x_67_, 3, v_r_61_);
lean_ctor_set(v___x_67_, 2, v_v_43_);
lean_ctor_set(v___x_67_, 1, v_k_42_);
lean_ctor_set(v___x_67_, 0, v___x_75_);
v___x_77_ = v___x_67_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_k_42_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_v_43_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_r_61_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v_r_45_);
v___x_77_ = v_reuseFailAlloc_81_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_79_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 4, v___x_77_);
lean_ctor_set(v___x_55_, 3, v___y_72_);
lean_ctor_set(v___x_55_, 2, v_v_59_);
lean_ctor_set(v___x_55_, 1, v_k_58_);
lean_ctor_set(v___x_55_, 0, v___x_70_);
v___x_79_ = v___x_55_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_k_58_);
lean_ctor_set(v_reuseFailAlloc_80_, 2, v_v_59_);
lean_ctor_set(v_reuseFailAlloc_80_, 3, v___y_72_);
lean_ctor_set(v_reuseFailAlloc_80_, 4, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_84_ = lean_nat_add(v___x_69_, v___y_83_);
lean_dec(v___y_83_);
lean_dec(v___x_69_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_l_60_);
lean_ctor_set(v___x_34_, 0, v___x_84_);
v___x_86_ = v___x_34_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_90_, 3, v_l_31_);
lean_ctor_set(v_reuseFailAlloc_90_, 4, v_l_60_);
v___x_86_ = v_reuseFailAlloc_90_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
v___x_87_ = lean_nat_add(v___x_39_, v_size_62_);
if (lean_obj_tag(v_r_61_) == 0)
{
lean_object* v_size_88_; 
v_size_88_ = lean_ctor_get(v_r_61_, 0);
lean_inc(v_size_88_);
v___y_72_ = v___x_86_;
v___y_73_ = v___x_87_;
v___y_74_ = v_size_88_;
goto v___jp_71_;
}
else
{
lean_object* v___x_89_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___y_72_ = v___x_86_;
v___y_73_ = v___x_87_;
v___y_74_ = v___x_89_;
goto v___jp_71_;
}
}
}
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
lean_del_object(v___x_34_);
v___x_99_ = lean_nat_add(v___x_39_, v_size_40_);
v___x_100_ = lean_nat_add(v___x_99_, v_size_41_);
lean_dec(v_size_41_);
v___x_101_ = lean_nat_add(v___x_99_, v_size_57_);
lean_dec(v___x_99_);
lean_inc_ref(v_l_31_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 4, v_l_44_);
lean_ctor_set(v___x_55_, 3, v_l_31_);
lean_ctor_set(v___x_55_, 2, v_v_30_);
lean_ctor_set(v___x_55_, 1, v_k_29_);
lean_ctor_set(v___x_55_, 0, v___x_101_);
v___x_103_ = v___x_55_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_l_31_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_l_44_);
v___x_103_ = v_reuseFailAlloc_116_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v_isSharedCheck_110_ = !lean_is_exclusive(v_l_31_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; lean_object* v_unused_112_; lean_object* v_unused_113_; lean_object* v_unused_114_; lean_object* v_unused_115_; 
v_unused_111_ = lean_ctor_get(v_l_31_, 4);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_l_31_, 3);
lean_dec(v_unused_112_);
v_unused_113_ = lean_ctor_get(v_l_31_, 2);
lean_dec(v_unused_113_);
v_unused_114_ = lean_ctor_get(v_l_31_, 1);
lean_dec(v_unused_114_);
v_unused_115_ = lean_ctor_get(v_l_31_, 0);
lean_dec(v_unused_115_);
v___x_105_ = v_l_31_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_dec(v_l_31_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 4, v_r_45_);
lean_ctor_set(v___x_105_, 3, v___x_103_);
lean_ctor_set(v___x_105_, 2, v_v_43_);
lean_ctor_set(v___x_105_, 1, v_k_42_);
lean_ctor_set(v___x_105_, 0, v___x_100_);
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_k_42_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_v_43_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v_r_45_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_123_; 
v_l_123_ = lean_ctor_get(v_impl_38_, 3);
lean_inc(v_l_123_);
if (lean_obj_tag(v_l_123_) == 0)
{
lean_object* v_r_124_; lean_object* v_k_125_; lean_object* v_v_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_149_; 
v_r_124_ = lean_ctor_get(v_impl_38_, 4);
v_k_125_ = lean_ctor_get(v_impl_38_, 1);
v_v_126_ = lean_ctor_get(v_impl_38_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v_impl_38_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; lean_object* v_unused_151_; 
v_unused_150_ = lean_ctor_get(v_impl_38_, 3);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v_impl_38_, 0);
lean_dec(v_unused_151_);
v___x_128_ = v_impl_38_;
v_isShared_129_ = v_isSharedCheck_149_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_r_124_);
lean_inc(v_v_126_);
lean_inc(v_k_125_);
lean_dec(v_impl_38_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_149_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_k_130_; lean_object* v_v_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_145_; 
v_k_130_ = lean_ctor_get(v_l_123_, 1);
v_v_131_ = lean_ctor_get(v_l_123_, 2);
v_isSharedCheck_145_ = !lean_is_exclusive(v_l_123_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; lean_object* v_unused_147_; lean_object* v_unused_148_; 
v_unused_146_ = lean_ctor_get(v_l_123_, 4);
lean_dec(v_unused_146_);
v_unused_147_ = lean_ctor_get(v_l_123_, 3);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_l_123_, 0);
lean_dec(v_unused_148_);
v___x_133_ = v_l_123_;
v_isShared_134_ = v_isSharedCheck_145_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_v_131_);
lean_inc(v_k_130_);
lean_dec(v_l_123_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_145_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_124_, 2);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 4, v_r_124_);
lean_ctor_set(v___x_133_, 3, v_r_124_);
lean_ctor_set(v___x_133_, 2, v_v_30_);
lean_ctor_set(v___x_133_, 1, v_k_29_);
lean_ctor_set(v___x_133_, 0, v___x_39_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_r_124_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_r_124_);
v___x_137_ = v_reuseFailAlloc_144_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
lean_inc(v_r_124_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 3, v_r_124_);
lean_ctor_set(v___x_128_, 0, v___x_39_);
v___x_139_ = v___x_128_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_k_125_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_v_126_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_r_124_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_r_124_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v___x_139_);
lean_ctor_set(v___x_34_, 3, v___x_137_);
lean_ctor_set(v___x_34_, 2, v_v_131_);
lean_ctor_set(v___x_34_, 1, v_k_130_);
lean_ctor_set(v___x_34_, 0, v___x_135_);
v___x_141_ = v___x_34_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_k_130_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_v_131_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
else
{
lean_object* v_r_152_; 
v_r_152_ = lean_ctor_get(v_impl_38_, 4);
lean_inc(v_r_152_);
if (lean_obj_tag(v_r_152_) == 0)
{
lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_165_; 
v_k_153_ = lean_ctor_get(v_impl_38_, 1);
v_v_154_ = lean_ctor_get(v_impl_38_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v_impl_38_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; lean_object* v_unused_167_; lean_object* v_unused_168_; 
v_unused_166_ = lean_ctor_get(v_impl_38_, 4);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_impl_38_, 3);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_impl_38_, 0);
lean_dec(v_unused_168_);
v___x_156_ = v_impl_38_;
v_isShared_157_ = v_isSharedCheck_165_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_v_154_);
lean_inc(v_k_153_);
lean_dec(v_impl_38_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_165_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(3u);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 4, v_l_123_);
lean_ctor_set(v___x_156_, 2, v_v_30_);
lean_ctor_set(v___x_156_, 1, v_k_29_);
lean_ctor_set(v___x_156_, 0, v___x_39_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_l_123_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v_l_123_);
v___x_160_ = v_reuseFailAlloc_164_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_r_152_);
lean_ctor_set(v___x_34_, 3, v___x_160_);
lean_ctor_set(v___x_34_, 2, v_v_154_);
lean_ctor_set(v___x_34_, 1, v_k_153_);
lean_ctor_set(v___x_34_, 0, v___x_158_);
v___x_162_ = v___x_34_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v_r_152_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(2u);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_impl_38_);
lean_ctor_set(v___x_34_, 3, v_r_152_);
lean_ctor_set(v___x_34_, 0, v___x_169_);
v___x_171_ = v___x_34_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_r_152_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_impl_38_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v___x_174_; 
lean_dec(v_v_30_);
lean_dec(v_k_29_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 2, v_v_26_);
lean_ctor_set(v___x_34_, 1, v_k_25_);
v___x_174_ = v___x_34_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_size_28_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_l_31_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_32_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_impl_176_; lean_object* v___x_177_; 
lean_dec(v_size_28_);
v_impl_176_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_25_, v_v_26_, v_l_31_);
v___x_177_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_32_) == 0)
{
lean_object* v_size_178_; lean_object* v_size_179_; lean_object* v_k_180_; lean_object* v_v_181_; lean_object* v_l_182_; lean_object* v_r_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_size_178_ = lean_ctor_get(v_r_32_, 0);
v_size_179_ = lean_ctor_get(v_impl_176_, 0);
lean_inc(v_size_179_);
v_k_180_ = lean_ctor_get(v_impl_176_, 1);
lean_inc(v_k_180_);
v_v_181_ = lean_ctor_get(v_impl_176_, 2);
lean_inc(v_v_181_);
v_l_182_ = lean_ctor_get(v_impl_176_, 3);
lean_inc(v_l_182_);
v_r_183_ = lean_ctor_get(v_impl_176_, 4);
lean_inc(v_r_183_);
v___x_184_ = lean_unsigned_to_nat(3u);
v___x_185_ = lean_nat_mul(v___x_184_, v_size_178_);
v___x_186_ = lean_nat_dec_lt(v___x_185_, v_size_179_);
lean_dec(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec(v_r_183_);
lean_dec(v_l_182_);
lean_dec(v_v_181_);
lean_dec(v_k_180_);
v___x_187_ = lean_nat_add(v___x_177_, v_size_179_);
lean_dec(v_size_179_);
v___x_188_ = lean_nat_add(v___x_187_, v_size_178_);
lean_dec(v___x_187_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 3, v_impl_176_);
lean_ctor_set(v___x_34_, 0, v___x_188_);
v___x_190_ = v___x_34_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_impl_176_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_r_32_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_257_; 
v_isSharedCheck_257_ = !lean_is_exclusive(v_impl_176_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_258_ = lean_ctor_get(v_impl_176_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_impl_176_, 3);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_impl_176_, 2);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_impl_176_, 1);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_impl_176_, 0);
lean_dec(v_unused_262_);
v___x_193_ = v_impl_176_;
v_isShared_194_ = v_isSharedCheck_257_;
goto v_resetjp_192_;
}
else
{
lean_dec(v_impl_176_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_257_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_size_195_; lean_object* v_size_196_; lean_object* v_k_197_; lean_object* v_v_198_; lean_object* v_l_199_; lean_object* v_r_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_size_195_ = lean_ctor_get(v_l_182_, 0);
v_size_196_ = lean_ctor_get(v_r_183_, 0);
v_k_197_ = lean_ctor_get(v_r_183_, 1);
v_v_198_ = lean_ctor_get(v_r_183_, 2);
v_l_199_ = lean_ctor_get(v_r_183_, 3);
v_r_200_ = lean_ctor_get(v_r_183_, 4);
v___x_201_ = lean_unsigned_to_nat(2u);
v___x_202_ = lean_nat_mul(v___x_201_, v_size_195_);
v___x_203_ = lean_nat_dec_lt(v_size_196_, v___x_202_);
lean_dec(v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_232_; 
lean_inc(v_r_200_);
lean_inc(v_l_199_);
lean_inc(v_v_198_);
lean_inc(v_k_197_);
v_isSharedCheck_232_ = !lean_is_exclusive(v_r_183_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; 
v_unused_233_ = lean_ctor_get(v_r_183_, 4);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_r_183_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_r_183_, 2);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_r_183_, 1);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_r_183_, 0);
lean_dec(v_unused_237_);
v___x_205_ = v_r_183_;
v_isShared_206_ = v_isSharedCheck_232_;
goto v_resetjp_204_;
}
else
{
lean_dec(v_r_183_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_232_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___x_220_; lean_object* v___y_222_; 
v___x_207_ = lean_nat_add(v___x_177_, v_size_179_);
lean_dec(v_size_179_);
v___x_208_ = lean_nat_add(v___x_207_, v_size_178_);
lean_dec(v___x_207_);
v___x_220_ = lean_nat_add(v___x_177_, v_size_195_);
if (lean_obj_tag(v_l_199_) == 0)
{
lean_object* v_size_230_; 
v_size_230_ = lean_ctor_get(v_l_199_, 0);
lean_inc(v_size_230_);
v___y_222_ = v_size_230_;
goto v___jp_221_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___y_222_ = v___x_231_;
goto v___jp_221_;
}
v___jp_209_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_nat_add(v___y_210_, v___y_212_);
lean_dec(v___y_212_);
lean_dec(v___y_210_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 4, v_r_32_);
lean_ctor_set(v___x_205_, 3, v_r_200_);
lean_ctor_set(v___x_205_, 2, v_v_30_);
lean_ctor_set(v___x_205_, 1, v_k_29_);
lean_ctor_set(v___x_205_, 0, v___x_213_);
v___x_215_ = v___x_205_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_r_200_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_r_32_);
v___x_215_ = v_reuseFailAlloc_219_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 4, v___x_215_);
lean_ctor_set(v___x_193_, 3, v___y_211_);
lean_ctor_set(v___x_193_, 2, v_v_198_);
lean_ctor_set(v___x_193_, 1, v_k_197_);
lean_ctor_set(v___x_193_, 0, v___x_208_);
v___x_217_ = v___x_193_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_197_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_198_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v___y_211_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_nat_add(v___x_220_, v___y_222_);
lean_dec(v___y_222_);
lean_dec(v___x_220_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_l_199_);
lean_ctor_set(v___x_34_, 3, v_l_182_);
lean_ctor_set(v___x_34_, 2, v_v_181_);
lean_ctor_set(v___x_34_, 1, v_k_180_);
lean_ctor_set(v___x_34_, 0, v___x_223_);
v___x_225_ = v___x_34_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_k_180_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_v_181_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v_l_199_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = lean_nat_add(v___x_177_, v_size_178_);
if (lean_obj_tag(v_r_200_) == 0)
{
lean_object* v_size_227_; 
v_size_227_ = lean_ctor_get(v_r_200_, 0);
lean_inc(v_size_227_);
v___y_210_ = v___x_226_;
v___y_211_ = v___x_225_;
v___y_212_ = v_size_227_;
goto v___jp_209_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___y_210_ = v___x_226_;
v___y_211_ = v___x_225_;
v___y_212_ = v___x_228_;
goto v___jp_209_;
}
}
}
}
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
lean_del_object(v___x_34_);
v___x_238_ = lean_nat_add(v___x_177_, v_size_179_);
lean_dec(v_size_179_);
v___x_239_ = lean_nat_add(v___x_238_, v_size_178_);
lean_dec(v___x_238_);
v___x_240_ = lean_nat_add(v___x_177_, v_size_178_);
v___x_241_ = lean_nat_add(v___x_240_, v_size_196_);
lean_dec(v___x_240_);
lean_inc_ref(v_r_32_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 4, v_r_32_);
lean_ctor_set(v___x_193_, 3, v_r_183_);
lean_ctor_set(v___x_193_, 2, v_v_30_);
lean_ctor_set(v___x_193_, 1, v_k_29_);
lean_ctor_set(v___x_193_, 0, v___x_241_);
v___x_243_ = v___x_193_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_r_183_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_r_32_);
v___x_243_ = v_reuseFailAlloc_256_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
v_isSharedCheck_250_ = !lean_is_exclusive(v_r_32_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; lean_object* v_unused_252_; lean_object* v_unused_253_; lean_object* v_unused_254_; lean_object* v_unused_255_; 
v_unused_251_ = lean_ctor_get(v_r_32_, 4);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_r_32_, 3);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_r_32_, 2);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_r_32_, 1);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_r_32_, 0);
lean_dec(v_unused_255_);
v___x_245_ = v_r_32_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_r_32_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v___x_243_);
lean_ctor_set(v___x_245_, 3, v_l_182_);
lean_ctor_set(v___x_245_, 2, v_v_181_);
lean_ctor_set(v___x_245_, 1, v_k_180_);
lean_ctor_set(v___x_245_, 0, v___x_239_);
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_k_180_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_v_181_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v___x_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_263_; 
v_l_263_ = lean_ctor_get(v_impl_176_, 3);
lean_inc(v_l_263_);
if (lean_obj_tag(v_l_263_) == 0)
{
lean_object* v_r_264_; lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_277_; 
v_r_264_ = lean_ctor_get(v_impl_176_, 4);
v_k_265_ = lean_ctor_get(v_impl_176_, 1);
v_v_266_ = lean_ctor_get(v_impl_176_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_impl_176_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; 
v_unused_278_ = lean_ctor_get(v_impl_176_, 3);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_impl_176_, 0);
lean_dec(v_unused_279_);
v___x_268_ = v_impl_176_;
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_r_264_);
lean_inc(v_v_266_);
lean_inc(v_k_265_);
lean_dec(v_impl_176_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 3, v_r_264_);
lean_ctor_set(v___x_268_, 2, v_v_30_);
lean_ctor_set(v___x_268_, 1, v_k_29_);
lean_ctor_set(v___x_268_, 0, v___x_177_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v_r_264_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v_r_264_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v___x_272_);
lean_ctor_set(v___x_34_, 3, v_l_263_);
lean_ctor_set(v___x_34_, 2, v_v_266_);
lean_ctor_set(v___x_34_, 1, v_k_265_);
lean_ctor_set(v___x_34_, 0, v___x_270_);
v___x_274_ = v___x_34_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_l_263_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_r_280_; 
v_r_280_ = lean_ctor_get(v_impl_176_, 4);
lean_inc(v_r_280_);
if (lean_obj_tag(v_r_280_) == 0)
{
lean_object* v_k_281_; lean_object* v_v_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_305_; 
v_k_281_ = lean_ctor_get(v_impl_176_, 1);
v_v_282_ = lean_ctor_get(v_impl_176_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_impl_176_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; 
v_unused_306_ = lean_ctor_get(v_impl_176_, 4);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_impl_176_, 3);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_impl_176_, 0);
lean_dec(v_unused_308_);
v___x_284_ = v_impl_176_;
v_isShared_285_ = v_isSharedCheck_305_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_v_282_);
lean_inc(v_k_281_);
lean_dec(v_impl_176_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_305_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_k_286_; lean_object* v_v_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_301_; 
v_k_286_ = lean_ctor_get(v_r_280_, 1);
v_v_287_ = lean_ctor_get(v_r_280_, 2);
v_isSharedCheck_301_ = !lean_is_exclusive(v_r_280_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_302_ = lean_ctor_get(v_r_280_, 4);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_r_280_, 3);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_r_280_, 0);
lean_dec(v_unused_304_);
v___x_289_ = v_r_280_;
v_isShared_290_ = v_isSharedCheck_301_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_v_287_);
lean_inc(v_k_286_);
lean_dec(v_r_280_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_301_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_unsigned_to_nat(3u);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 4, v_l_263_);
lean_ctor_set(v___x_289_, 3, v_l_263_);
lean_ctor_set(v___x_289_, 2, v_v_282_);
lean_ctor_set(v___x_289_, 1, v_k_281_);
lean_ctor_set(v___x_289_, 0, v___x_177_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_k_281_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_v_282_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_l_263_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v_l_263_);
v___x_293_ = v_reuseFailAlloc_300_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 4, v_l_263_);
lean_ctor_set(v___x_284_, 2, v_v_30_);
lean_ctor_set(v___x_284_, 1, v_k_29_);
lean_ctor_set(v___x_284_, 0, v___x_177_);
v___x_295_ = v___x_284_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_l_263_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_l_263_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v___x_295_);
lean_ctor_set(v___x_34_, 3, v___x_293_);
lean_ctor_set(v___x_34_, 2, v_v_287_);
lean_ctor_set(v___x_34_, 1, v_k_286_);
lean_ctor_set(v___x_34_, 0, v___x_291_);
v___x_297_ = v___x_34_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_287_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(2u);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 4, v_r_280_);
lean_ctor_set(v___x_34_, 3, v_impl_176_);
lean_ctor_set(v___x_34_, 0, v___x_309_);
v___x_311_ = v___x_34_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_29_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_30_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_impl_176_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_r_280_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_k_25_);
lean_ctor_set(v___x_315_, 2, v_v_26_);
lean_ctor_set(v___x_315_, 3, v_t_27_);
lean_ctor_set(v___x_315_, 4, v_t_27_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(lean_object* v_a_316_, lean_object* v_fallback_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_inc(v_fallback_317_);
return v_fallback_317_;
}
else
{
lean_object* v_key_319_; lean_object* v_value_320_; lean_object* v_tail_321_; uint8_t v___x_322_; 
v_key_319_ = lean_ctor_get(v_x_318_, 0);
v_value_320_ = lean_ctor_get(v_x_318_, 1);
v_tail_321_ = lean_ctor_get(v_x_318_, 2);
v___x_322_ = lean_nat_dec_eq(v_key_319_, v_a_316_);
if (v___x_322_ == 0)
{
v_x_318_ = v_tail_321_;
goto _start;
}
else
{
lean_inc(v_value_320_);
return v_value_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg___boxed(lean_object* v_a_324_, lean_object* v_fallback_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_324_, v_fallback_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_fallback_325_);
lean_dec(v_a_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(lean_object* v_m_328_, lean_object* v_a_329_, lean_object* v_fallback_330_){
_start:
{
lean_object* v_buckets_331_; lean_object* v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v_fold_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_buckets_331_ = lean_ctor_get(v_m_328_, 1);
v___x_332_ = lean_array_get_size(v_buckets_331_);
v___x_333_ = lean_uint64_of_nat(v_a_329_);
v___x_334_ = 32ULL;
v___x_335_ = lean_uint64_shift_right(v___x_333_, v___x_334_);
v_fold_336_ = lean_uint64_xor(v___x_333_, v___x_335_);
v___x_337_ = 16ULL;
v___x_338_ = lean_uint64_shift_right(v_fold_336_, v___x_337_);
v___x_339_ = lean_uint64_xor(v_fold_336_, v___x_338_);
v___x_340_ = lean_uint64_to_usize(v___x_339_);
v___x_341_ = lean_usize_of_nat(v___x_332_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v___x_341_, v___x_342_);
v___x_344_ = lean_usize_land(v___x_340_, v___x_343_);
v___x_345_ = lean_array_uget_borrowed(v_buckets_331_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_329_, v_fallback_330_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg___boxed(lean_object* v_m_347_, lean_object* v_a_348_, lean_object* v_fallback_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_347_, v_a_348_, v_fallback_349_);
lean_dec(v_fallback_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_m_347_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(lean_object* v_a_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
else
{
lean_object* v_key_354_; lean_object* v_tail_355_; uint8_t v___x_356_; 
v_key_354_ = lean_ctor_get(v_x_352_, 0);
v_tail_355_ = lean_ctor_get(v_x_352_, 2);
v___x_356_ = lean_nat_dec_eq(v_key_354_, v_a_351_);
if (v___x_356_ == 0)
{
v_x_352_ = v_tail_355_;
goto _start;
}
else
{
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg___boxed(lean_object* v_a_358_, lean_object* v_x_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec(v_a_358_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_dec(v_b_363_);
lean_dec(v_a_362_);
return v_x_364_;
}
else
{
lean_object* v_key_365_; lean_object* v_value_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_379_; 
v_key_365_ = lean_ctor_get(v_x_364_, 0);
v_value_366_ = lean_ctor_get(v_x_364_, 1);
v_tail_367_ = lean_ctor_get(v_x_364_, 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_379_ == 0)
{
v___x_369_ = v_x_364_;
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_value_366_);
lean_inc(v_key_365_);
lean_dec(v_x_364_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v___x_371_; 
v___x_371_ = lean_nat_dec_eq(v_key_365_, v_a_362_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_362_, v_b_363_, v_tail_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 2, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_key_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_value_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_object* v___x_377_; 
lean_dec(v_value_366_);
lean_dec(v_key_365_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_b_363_);
lean_ctor_set(v___x_369_, 0, v_a_362_);
v___x_377_ = v___x_369_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_362_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_b_363_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_tail_367_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
return v_x_380_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_407_; 
v_key_382_ = lean_ctor_get(v_x_381_, 0);
v_value_383_ = lean_ctor_get(v_x_381_, 1);
v_tail_384_ = lean_ctor_get(v_x_381_, 2);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_407_ == 0)
{
v___x_386_ = v_x_381_;
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_tail_384_);
lean_inc(v_value_383_);
lean_inc(v_key_382_);
lean_dec(v_x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v_fold_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_388_ = lean_array_get_size(v_x_380_);
v___x_389_ = lean_uint64_of_nat(v_key_382_);
v___x_390_ = 32ULL;
v___x_391_ = lean_uint64_shift_right(v___x_389_, v___x_390_);
v_fold_392_ = lean_uint64_xor(v___x_389_, v___x_391_);
v___x_393_ = 16ULL;
v___x_394_ = lean_uint64_shift_right(v_fold_392_, v___x_393_);
v___x_395_ = lean_uint64_xor(v_fold_392_, v___x_394_);
v___x_396_ = lean_uint64_to_usize(v___x_395_);
v___x_397_ = lean_usize_of_nat(v___x_388_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_sub(v___x_397_, v___x_398_);
v___x_400_ = lean_usize_land(v___x_396_, v___x_399_);
v___x_401_ = lean_array_uget_borrowed(v_x_380_, v___x_400_);
lean_inc(v___x_401_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_401_);
v___x_403_ = v___x_386_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_key_382_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_value_383_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = lean_array_uset(v_x_380_, v___x_400_, v___x_403_);
v_x_380_ = v___x_404_;
v_x_381_ = v_tail_384_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(lean_object* v_i_408_, lean_object* v_source_409_, lean_object* v_target_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_source_409_);
v___x_412_ = lean_nat_dec_lt(v_i_408_, v___x_411_);
if (v___x_412_ == 0)
{
lean_dec_ref(v_source_409_);
lean_dec(v_i_408_);
return v_target_410_;
}
else
{
lean_object* v_es_413_; lean_object* v___x_414_; lean_object* v_source_415_; lean_object* v_target_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_es_413_ = lean_array_fget(v_source_409_, v_i_408_);
v___x_414_ = lean_box(0);
v_source_415_ = lean_array_fset(v_source_409_, v_i_408_, v___x_414_);
v_target_416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(v_target_410_, v_es_413_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_i_408_, v___x_417_);
lean_dec(v_i_408_);
v_i_408_ = v___x_418_;
v_source_409_ = v_source_415_;
v_target_410_ = v_target_416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(lean_object* v_data_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_nbuckets_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_421_ = lean_array_get_size(v_data_420_);
v___x_422_ = lean_unsigned_to_nat(2u);
v_nbuckets_423_ = lean_nat_mul(v___x_421_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_box(0);
v___x_426_ = lean_mk_array(v_nbuckets_423_, v___x_425_);
v___x_427_ = lean_array_propagate_mark(v_data_420_, v___x_426_);
v___x_428_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(v___x_424_, v_data_420_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(lean_object* v_m_429_, lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
lean_object* v_size_432_; lean_object* v_buckets_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_476_; 
v_size_432_ = lean_ctor_get(v_m_429_, 0);
v_buckets_433_ = lean_ctor_get(v_m_429_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_m_429_);
if (v_isSharedCheck_476_ == 0)
{
v___x_435_ = v_m_429_;
v_isShared_436_ = v_isSharedCheck_476_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_buckets_433_);
lean_inc(v_size_432_);
lean_dec(v_m_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_476_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v_fold_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v_bkt_450_; uint8_t v___x_451_; 
v___x_437_ = lean_array_get_size(v_buckets_433_);
v___x_438_ = lean_uint64_of_nat(v_a_430_);
v___x_439_ = 32ULL;
v___x_440_ = lean_uint64_shift_right(v___x_438_, v___x_439_);
v_fold_441_ = lean_uint64_xor(v___x_438_, v___x_440_);
v___x_442_ = 16ULL;
v___x_443_ = lean_uint64_shift_right(v_fold_441_, v___x_442_);
v___x_444_ = lean_uint64_xor(v_fold_441_, v___x_443_);
v___x_445_ = lean_uint64_to_usize(v___x_444_);
v___x_446_ = lean_usize_of_nat(v___x_437_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_sub(v___x_446_, v___x_447_);
v___x_449_ = lean_usize_land(v___x_445_, v___x_448_);
v_bkt_450_ = lean_array_uget_borrowed(v_buckets_433_, v___x_449_);
v___x_451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_430_, v_bkt_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v_size_x27_453_; lean_object* v___x_454_; lean_object* v_buckets_x27_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v_size_x27_453_ = lean_nat_add(v_size_432_, v___x_452_);
lean_dec(v_size_432_);
lean_inc(v_bkt_450_);
v___x_454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_454_, 0, v_a_430_);
lean_ctor_set(v___x_454_, 1, v_b_431_);
lean_ctor_set(v___x_454_, 2, v_bkt_450_);
v_buckets_x27_455_ = lean_array_uset(v_buckets_433_, v___x_449_, v___x_454_);
v___x_456_ = lean_unsigned_to_nat(4u);
v___x_457_ = lean_nat_mul(v_size_x27_453_, v___x_456_);
v___x_458_ = lean_unsigned_to_nat(3u);
v___x_459_ = lean_nat_div(v___x_457_, v___x_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_array_get_size(v_buckets_x27_455_);
v___x_461_ = lean_nat_dec_le(v___x_459_, v___x_460_);
lean_dec(v___x_459_);
if (v___x_461_ == 0)
{
lean_object* v_val_462_; lean_object* v___x_464_; 
v_val_462_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(v_buckets_x27_455_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v_val_462_);
lean_ctor_set(v___x_435_, 0, v_size_x27_453_);
v___x_464_ = v___x_435_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_size_x27_453_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_val_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
lean_object* v___x_467_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v_buckets_x27_455_);
lean_ctor_set(v___x_435_, 0, v_size_x27_453_);
v___x_467_ = v___x_435_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_size_x27_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_buckets_x27_455_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v___x_469_; lean_object* v_buckets_x27_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_inc(v_bkt_450_);
v___x_469_ = lean_box(0);
v_buckets_x27_470_ = lean_array_uset(v_buckets_433_, v___x_449_, v___x_469_);
v___x_471_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_430_, v_b_431_, v_bkt_450_);
v___x_472_ = lean_array_uset(v_buckets_x27_470_, v___x_449_, v___x_471_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_472_);
v___x_474_ = v___x_435_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_size_432_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object* v_aigSize_477_, lean_object* v_assignment_478_, lean_object* v_as_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_b_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_483_ == 0)
{
return v_b_482_;
}
else
{
lean_object* v_a_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; uint8_t v___y_488_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_a_484_ = lean_array_uget_borrowed(v_as_479_, v_i_481_);
v_fst_485_ = lean_ctor_get(v_a_484_, 0);
v_snd_486_ = lean_ctor_get(v_a_484_, 1);
v___x_499_ = lean_nat_add(v_snd_486_, v_aigSize_477_);
v___x_500_ = lean_array_get_size(v_assignment_478_);
v___x_501_ = lean_nat_dec_lt(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_dec(v___x_499_);
v___y_488_ = v___x_483_;
goto v___jp_487_;
}
else
{
lean_object* v___x_502_; lean_object* v_fst_503_; uint8_t v___x_504_; 
v___x_502_ = lean_array_fget_borrowed(v_assignment_478_, v___x_499_);
lean_dec(v___x_499_);
v_fst_503_ = lean_ctor_get(v___x_502_, 0);
v___x_504_ = lean_unbox(v_fst_503_);
v___y_488_ = v___x_504_;
goto v___jp_487_;
}
v___jp_487_:
{
lean_object* v_var_489_; lean_object* v_idx_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; size_t v___x_496_; size_t v___x_497_; 
v_var_489_ = lean_ctor_get(v_fst_485_, 0);
v_idx_490_ = lean_ctor_get(v_fst_485_, 2);
v___x_491_ = lean_box(1);
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_b_482_, v_var_489_, v___x_491_);
v___x_493_ = lean_box(v___y_488_);
lean_inc(v_idx_490_);
v___x_494_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_idx_490_, v___x_493_, v___x_492_);
lean_inc(v_var_489_);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_b_482_, v_var_489_, v___x_494_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_481_, v___x_496_);
v_i_481_ = v___x_497_;
v_b_482_ = v___x_495_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object* v_aigSize_505_, lean_object* v_assignment_506_, lean_object* v_as_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_b_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_aigSize_505_, v_assignment_506_, v_as_507_, v_sz_boxed_511_, v_i_boxed_512_, v_b_510_);
lean_dec_ref(v_as_507_);
lean_dec_ref(v_assignment_506_);
lean_dec(v_aigSize_505_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
return v_x_514_;
}
else
{
lean_object* v_key_516_; lean_object* v_value_517_; lean_object* v_tail_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_key_516_ = lean_ctor_get(v_x_515_, 0);
v_value_517_ = lean_ctor_get(v_x_515_, 1);
v_tail_518_ = lean_ctor_get(v_x_515_, 2);
lean_inc(v_value_517_);
lean_inc(v_key_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_key_516_);
lean_ctor_set(v___x_519_, 1, v_value_517_);
v___x_520_ = lean_array_push(v_x_514_, v___x_519_);
v_x_514_ = v___x_520_;
v_x_515_ = v_tail_518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_x_522_, v_x_523_);
lean_dec(v_x_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object* v_as_525_, size_t v_i_526_, size_t v_stop_527_, lean_object* v_b_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = lean_usize_dec_eq(v_i_526_, v_stop_527_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; 
v___x_530_ = lean_array_uget_borrowed(v_as_525_, v_i_526_);
v___x_531_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_b_528_, v___x_530_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_526_, v___x_532_);
v_i_526_ = v___x_533_;
v_b_528_ = v___x_531_;
goto _start;
}
else
{
return v_b_528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_, lean_object* v_b_538_){
_start:
{
size_t v_i_boxed_539_; size_t v_stop_boxed_540_; lean_object* v_res_541_; 
v_i_boxed_539_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_540_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_as_535_, v_i_boxed_539_, v_stop_boxed_540_, v_b_538_);
lean_dec_ref(v_as_535_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
return v_x_542_;
}
else
{
lean_object* v_key_544_; lean_object* v_value_545_; lean_object* v_tail_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_key_544_ = lean_ctor_get(v_x_543_, 0);
v_value_545_ = lean_ctor_get(v_x_543_, 1);
v_tail_546_ = lean_ctor_get(v_x_543_, 2);
lean_inc(v_value_545_);
lean_inc(v_key_544_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_key_544_);
lean_ctor_set(v___x_547_, 1, v_value_545_);
v___x_548_ = lean_array_push(v_x_542_, v___x_547_);
v_x_542_ = v___x_548_;
v_x_543_ = v_tail_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_x_550_, v_x_551_);
lean_dec(v_x_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(lean_object* v_as_553_, size_t v_i_554_, size_t v_stop_555_, lean_object* v_b_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_eq(v_i_554_, v_stop_555_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; size_t v___x_560_; size_t v___x_561_; 
v___x_558_ = lean_array_uget_borrowed(v_as_553_, v_i_554_);
v___x_559_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_b_556_, v___x_558_);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_554_, v___x_560_);
v_i_554_ = v___x_561_;
v_b_556_ = v___x_559_;
goto _start;
}
else
{
return v_b_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13___boxed(lean_object* v_as_563_, lean_object* v_i_564_, lean_object* v_stop_565_, lean_object* v_b_566_){
_start:
{
size_t v_i_boxed_567_; size_t v_stop_boxed_568_; lean_object* v_res_569_; 
v_i_boxed_567_ = lean_unbox_usize(v_i_564_);
lean_dec(v_i_564_);
v_stop_boxed_568_ = lean_unbox_usize(v_stop_565_);
lean_dec(v_stop_565_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_as_563_, v_i_boxed_567_, v_stop_boxed_568_, v_b_566_);
lean_dec_ref(v_as_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(lean_object* v_as_570_, size_t v_i_571_, size_t v_stop_572_, lean_object* v_b_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_eq(v_i_571_, v_stop_572_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; 
v___x_575_ = lean_array_uget_borrowed(v_as_570_, v_i_571_);
v___x_576_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_575_);
v___x_577_ = lean_nat_add(v_b_573_, v___x_576_);
lean_dec(v___x_576_);
lean_dec(v_b_573_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_571_, v___x_578_);
v_i_571_ = v___x_579_;
v_b_573_ = v___x_577_;
goto _start;
}
else
{
return v_b_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18___boxed(lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_, lean_object* v_b_584_){
_start:
{
size_t v_i_boxed_585_; size_t v_stop_boxed_586_; lean_object* v_res_587_; 
v_i_boxed_585_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_586_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_as_581_, v_i_boxed_585_, v_stop_boxed_586_, v_b_584_);
lean_dec_ref(v_as_581_);
return v_res_587_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = 0;
v___x_589_ = l_Lean_instInhabitedExpr;
v___x_590_ = lean_box(v___x_588_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(lean_object* v_msg_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_panic_fn_borrowed(v___x_595_, v_msg_592_);
lean_dec_ref_known(v___x_595_, 2);
return v___x_596_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_600_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2));
v___x_601_ = lean_unsigned_to_nat(11u);
v___x_602_ = lean_unsigned_to_nat(163u);
v___x_603_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1));
v___x_604_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0));
v___x_605_ = l_mkPanicMessageWithDecl(v___x_604_, v___x_603_, v___x_602_, v___x_601_, v___x_600_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object* v_a_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3);
v___x_609_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(v___x_608_);
return v___x_609_;
}
else
{
lean_object* v_key_610_; lean_object* v_value_611_; lean_object* v_tail_612_; uint8_t v___x_613_; 
v_key_610_ = lean_ctor_get(v_x_607_, 0);
v_value_611_ = lean_ctor_get(v_x_607_, 1);
v_tail_612_ = lean_ctor_get(v_x_607_, 2);
v___x_613_ = lean_nat_dec_eq(v_key_610_, v_a_606_);
if (v___x_613_ == 0)
{
v_x_607_ = v_tail_612_;
goto _start;
}
else
{
lean_inc(v_value_611_);
return v_value_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_a_615_, v_x_616_);
lean_dec(v_x_616_);
lean_dec(v_a_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object* v_m_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_buckets_620_; lean_object* v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; uint64_t v___x_624_; uint64_t v_fold_625_; uint64_t v___x_626_; uint64_t v___x_627_; uint64_t v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_buckets_620_ = lean_ctor_get(v_m_618_, 1);
v___x_621_ = lean_array_get_size(v_buckets_620_);
v___x_622_ = lean_uint64_of_nat(v_a_619_);
v___x_623_ = 32ULL;
v___x_624_ = lean_uint64_shift_right(v___x_622_, v___x_623_);
v_fold_625_ = lean_uint64_xor(v___x_622_, v___x_624_);
v___x_626_ = 16ULL;
v___x_627_ = lean_uint64_shift_right(v_fold_625_, v___x_626_);
v___x_628_ = lean_uint64_xor(v_fold_625_, v___x_627_);
v___x_629_ = lean_uint64_to_usize(v___x_628_);
v___x_630_ = lean_usize_of_nat(v___x_621_);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_sub(v___x_630_, v___x_631_);
v___x_633_ = lean_usize_land(v___x_629_, v___x_632_);
v___x_634_ = lean_array_uget_borrowed(v_buckets_620_, v___x_633_);
v___x_635_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_a_619_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object* v_m_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_m_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_m_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(lean_object* v_atomsAssignment_639_, lean_object* v_acc_640_, lean_object* v_a_641_){
_start:
{
if (lean_obj_tag(v_a_641_) == 0)
{
return v_acc_640_;
}
else
{
lean_object* v_key_642_; lean_object* v_value_643_; lean_object* v_tail_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_658_; 
v_key_642_ = lean_ctor_get(v_a_641_, 0);
v_value_643_ = lean_ctor_get(v_a_641_, 1);
v_tail_644_ = lean_ctor_get(v_a_641_, 2);
v_isSharedCheck_658_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_658_ == 0)
{
v___x_646_ = v_a_641_;
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_tail_644_);
lean_inc(v_value_643_);
lean_inc(v_key_642_);
lean_dec(v_a_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_var_648_; lean_object* v___x_649_; lean_object* v_snd_650_; lean_object* v_snd_651_; uint8_t v___x_652_; 
v_var_648_ = lean_ctor_get(v_key_642_, 0);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_639_, v_var_648_);
v_snd_650_ = lean_ctor_get(v___x_649_, 1);
lean_inc(v_snd_650_);
lean_dec_ref(v___x_649_);
v_snd_651_ = lean_ctor_get(v_snd_650_, 1);
lean_inc(v_snd_651_);
lean_dec(v_snd_650_);
v___x_652_ = lean_unbox(v_snd_651_);
lean_dec(v_snd_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_654_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 2, v_acc_640_);
v___x_654_ = v___x_646_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_key_642_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_value_643_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_acc_640_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v_acc_640_ = v___x_654_;
v_a_641_ = v_tail_644_;
goto _start;
}
}
else
{
lean_del_object(v___x_646_);
lean_dec(v_value_643_);
lean_dec(v_key_642_);
v_a_641_ = v_tail_644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16___boxed(lean_object* v_atomsAssignment_659_, lean_object* v_acc_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(v_atomsAssignment_659_, v_acc_660_, v_a_661_);
lean_dec_ref(v_atomsAssignment_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(lean_object* v_atomsAssignment_663_, size_t v_sz_664_, size_t v_i_665_, lean_object* v_bs_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = lean_usize_dec_lt(v_i_665_, v_sz_664_);
if (v___x_667_ == 0)
{
return v_bs_666_;
}
else
{
lean_object* v_v_668_; lean_object* v___x_669_; lean_object* v_bs_x27_670_; lean_object* v___x_671_; lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v_v_668_ = lean_array_uget(v_bs_666_, v_i_665_);
v___x_669_ = lean_unsigned_to_nat(0u);
v_bs_x27_670_ = lean_array_uset(v_bs_666_, v_i_665_, v___x_669_);
v___x_671_ = lean_box(0);
v___x_672_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(v_atomsAssignment_663_, v___x_671_, v_v_668_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_665_, v___x_673_);
v___x_675_ = lean_array_uset(v_bs_x27_670_, v_i_665_, v___x_672_);
v_i_665_ = v___x_674_;
v_bs_666_ = v___x_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17___boxed(lean_object* v_atomsAssignment_677_, lean_object* v_sz_678_, lean_object* v_i_679_, lean_object* v_bs_680_){
_start:
{
size_t v_sz_boxed_681_; size_t v_i_boxed_682_; lean_object* v_res_683_; 
v_sz_boxed_681_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_682_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_atomsAssignment_677_, v_sz_boxed_681_, v_i_boxed_682_, v_bs_680_);
lean_dec_ref(v_atomsAssignment_677_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object* v_atomsAssignment_684_, lean_object* v_m_685_){
_start:
{
lean_object* v_buckets_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_704_; 
v_buckets_686_ = lean_ctor_get(v_m_685_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_m_685_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_m_685_, 0);
lean_dec(v_unused_705_);
v___x_688_ = v_m_685_;
v_isShared_689_ = v_isSharedCheck_704_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_buckets_686_);
lean_dec(v_m_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_704_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
size_t v_sz_690_; size_t v___x_691_; lean_object* v_newBuckets_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_sz_690_ = lean_array_size(v_buckets_686_);
v___x_691_ = ((size_t)0ULL);
v_newBuckets_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_atomsAssignment_684_, v_sz_690_, v___x_691_, v_buckets_686_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_array_get_size(v_newBuckets_692_);
v___x_695_ = lean_nat_dec_lt(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_697_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_newBuckets_692_);
lean_ctor_set(v___x_688_, 0, v___x_693_);
v___x_697_ = v___x_688_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_newBuckets_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = lean_usize_of_nat(v___x_694_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_newBuckets_692_, v___x_691_, v___x_699_, v___x_693_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_newBuckets_692_);
lean_ctor_set(v___x_688_, 0, v___x_700_);
v___x_702_ = v___x_688_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_newBuckets_692_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object* v_atomsAssignment_706_, lean_object* v_m_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_atomsAssignment_706_, v_m_707_);
lean_dec_ref(v_atomsAssignment_706_);
return v_res_708_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_712_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2));
v___x_713_ = lean_unsigned_to_nat(6u);
v___x_714_ = lean_unsigned_to_nat(67u);
v___x_715_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1));
v___x_716_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0));
v___x_717_ = l_mkPanicMessageWithDecl(v___x_716_, v___x_715_, v___x_714_, v___x_713_, v___x_712_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object* v_as_x27_718_, lean_object* v_b_719_){
_start:
{
if (lean_obj_tag(v_as_x27_718_) == 0)
{
return v_b_719_;
}
else
{
lean_object* v_head_720_; lean_object* v_tail_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_747_; 
v_head_720_ = lean_ctor_get(v_as_x27_718_, 0);
v_tail_721_ = lean_ctor_get(v_as_x27_718_, 1);
v_fst_722_ = lean_ctor_get(v_head_720_, 0);
v_snd_723_ = lean_ctor_get(v_head_720_, 1);
v_fst_724_ = lean_ctor_get(v_b_719_, 0);
v_snd_725_ = lean_ctor_get(v_b_719_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_b_719_);
if (v_isSharedCheck_747_ == 0)
{
v___x_727_ = v_b_719_;
v_isShared_728_ = v_isSharedCheck_747_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_inc(v_fst_724_);
lean_dec(v_b_719_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_747_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_value_730_; uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_eq(v_fst_722_, v_snd_725_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_del_object(v___x_727_);
lean_dec(v_snd_725_);
lean_dec(v_fst_724_);
v___x_738_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3);
v___x_739_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(v___x_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
return v_a_740_;
}
else
{
lean_object* v_a_741_; 
v_a_741_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_739_, 1);
v_as_x27_718_ = v_tail_721_;
v_b_719_ = v_a_741_;
goto _start;
}
}
else
{
uint8_t v___x_743_; 
v___x_743_ = lean_unbox(v_snd_723_);
if (v___x_743_ == 0)
{
v_value_730_ = v_fst_724_;
goto v___jp_729_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_shiftl(v___x_744_, v_snd_725_);
v___x_746_ = lean_nat_lor(v_fst_724_, v___x_745_);
lean_dec(v___x_745_);
lean_dec(v_fst_724_);
v_value_730_ = v___x_746_;
goto v___jp_729_;
}
}
v___jp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_snd_725_, v___x_731_);
lean_dec(v_snd_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___x_732_);
lean_ctor_set(v___x_727_, 0, v_value_730_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_value_730_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v_as_x27_718_ = v_tail_721_;
v_b_719_ = v___x_734_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___boxed(lean_object* v_as_x27_748_, lean_object* v_b_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_748_, v_b_749_);
lean_dec(v_as_x27_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object* v_init_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v_l_755_; lean_object* v_r_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_k_753_ = lean_ctor_get(v_x_752_, 1);
v_v_754_ = lean_ctor_get(v_x_752_, 2);
v_l_755_ = lean_ctor_get(v_x_752_, 3);
v_r_756_ = lean_ctor_get(v_x_752_, 4);
v___x_757_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_751_, v_r_756_);
lean_inc(v_v_754_);
lean_inc(v_k_753_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_k_753_);
lean_ctor_set(v___x_758_, 1, v_v_754_);
v___x_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
v_init_751_ = v___x_759_;
v_x_752_ = v_l_755_;
goto _start;
}
else
{
return v_init_751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___boxed(lean_object* v_init_761_, lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_761_, v_x_762_);
lean_dec(v_x_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object* v_atomsAssignment_766_, lean_object* v_as_767_, size_t v_sz_768_, size_t v_i_769_, lean_object* v_b_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_lt(v_i_769_, v_sz_768_);
if (v___x_771_ == 0)
{
return v_b_770_;
}
else
{
lean_object* v_a_772_; lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_snd_777_; lean_object* v_fst_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_802_; 
v_a_772_ = lean_array_uget_borrowed(v_as_767_, v_i_769_);
v_fst_773_ = lean_ctor_get(v_a_772_, 0);
v_snd_774_ = lean_ctor_get(v_a_772_, 1);
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0));
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_766_, v_fst_773_);
v_snd_777_ = lean_ctor_get(v___x_776_, 1);
lean_inc(v_snd_777_);
lean_dec_ref(v___x_776_);
v_fst_778_ = lean_ctor_get(v_snd_777_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_snd_777_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_snd_777_, 1);
lean_dec(v_unused_803_);
v___x_780_ = v_snd_777_;
v_isShared_781_ = v_isSharedCheck_802_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_fst_778_);
lean_dec(v_snd_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_802_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_801_; 
v___x_782_ = lean_box(0);
v___x_783_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v___x_782_, v_snd_774_);
v___x_784_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v___x_783_, v___x_775_);
lean_dec(v___x_783_);
v_fst_785_ = lean_ctor_get(v___x_784_, 0);
v_snd_786_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_801_ == 0)
{
v___x_788_ = v___x_784_;
v_isShared_789_ = v_isSharedCheck_801_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_inc(v_fst_785_);
lean_dec(v___x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_801_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = l_BitVec_ofNat(v_snd_786_, v_fst_785_);
lean_dec(v_fst_785_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v___x_790_);
lean_ctor_set(v___x_780_, 0, v_snd_786_);
v___x_792_ = v___x_780_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_snd_786_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_800_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_792_);
lean_ctor_set(v___x_788_, 0, v_fst_778_);
v___x_794_ = v___x_788_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_fst_778_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_799_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; size_t v___x_796_; size_t v___x_797_; 
v___x_795_ = lean_array_push(v_b_770_, v___x_794_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_769_, v___x_796_);
v_i_769_ = v___x_797_;
v_b_770_ = v___x_795_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object* v_atomsAssignment_804_, lean_object* v_as_805_, lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_b_808_){
_start:
{
size_t v_sz_boxed_809_; size_t v_i_boxed_810_; lean_object* v_res_811_; 
v_sz_boxed_809_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_810_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_804_, v_as_805_, v_sz_boxed_809_, v_i_boxed_810_, v_b_808_);
lean_dec_ref(v_as_805_);
lean_dec_ref(v_atomsAssignment_804_);
return v_res_811_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_box(0);
v___x_813_ = lean_unsigned_to_nat(16u);
v___x_814_ = lean_mk_array(v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_sparseMap_817_; 
v___x_815_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0);
v___x_816_ = lean_unsigned_to_nat(0u);
v_sparseMap_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_sparseMap_817_, 0, v___x_816_);
lean_ctor_set(v_sparseMap_817_, 1, v___x_815_);
return v_sparseMap_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object* v_var2Cnf_820_, lean_object* v_assignment_821_, lean_object* v_aigSize_822_, lean_object* v_atomsAssignment_823_){
_start:
{
size_t v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___x_830_; lean_object* v_size_831_; lean_object* v_buckets_832_; lean_object* v___x_833_; lean_object* v_sparseMap_834_; lean_object* v___y_836_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_atomsAssignment_823_, v_var2Cnf_820_);
v_size_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_size_831_);
v_buckets_832_ = lean_ctor_get(v___x_830_, 1);
lean_inc_ref(v_buckets_832_);
lean_dec_ref(v___x_830_);
v___x_833_ = lean_unsigned_to_nat(0u);
v_sparseMap_834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1);
v___x_848_ = lean_mk_empty_array_with_capacity(v_size_831_);
lean_dec(v_size_831_);
v___x_849_ = lean_array_get_size(v_buckets_832_);
v___x_850_ = lean_nat_dec_lt(v___x_833_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_buckets_832_);
v___y_836_ = v___x_848_;
goto v___jp_835_;
}
else
{
size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((size_t)0ULL);
v___x_852_ = lean_usize_of_nat(v___x_849_);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_buckets_832_, v___x_851_, v___x_852_, v___x_848_);
lean_dec_ref(v_buckets_832_);
v___y_836_ = v___x_853_;
goto v___jp_835_;
}
v___jp_824_:
{
size_t v_sz_828_; lean_object* v___x_829_; 
v_sz_828_ = lean_array_size(v___y_827_);
lean_inc_ref(v___y_826_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_823_, v___y_827_, v_sz_828_, v___y_825_, v___y_826_);
lean_dec_ref(v___y_827_);
return v___x_829_;
}
v___jp_835_:
{
size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v_size_840_; lean_object* v_buckets_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_sz_837_ = lean_array_size(v___y_836_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_aigSize_822_, v_assignment_821_, v___y_836_, v_sz_837_, v___x_838_, v_sparseMap_834_);
lean_dec_ref(v___y_836_);
v_size_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_size_840_);
v_buckets_841_ = lean_ctor_get(v___x_839_, 1);
lean_inc_ref(v_buckets_841_);
lean_dec_ref(v___x_839_);
v___x_842_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2));
v___x_843_ = lean_mk_empty_array_with_capacity(v_size_840_);
lean_dec(v_size_840_);
v___x_844_ = lean_array_get_size(v_buckets_841_);
v___x_845_ = lean_nat_dec_lt(v___x_833_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec_ref(v_buckets_841_);
v___y_825_ = v___x_838_;
v___y_826_ = v___x_842_;
v___y_827_ = v___x_843_;
goto v___jp_824_;
}
else
{
size_t v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_usize_of_nat(v___x_844_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_buckets_841_, v___x_838_, v___x_846_, v___x_843_);
lean_dec_ref(v_buckets_841_);
v___y_825_ = v___x_838_;
v___y_826_ = v___x_842_;
v___y_827_ = v___x_847_;
goto v___jp_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object* v_var2Cnf_854_, lean_object* v_assignment_855_, lean_object* v_aigSize_856_, lean_object* v_atomsAssignment_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_var2Cnf_854_, v_assignment_855_, v_aigSize_856_, v_atomsAssignment_857_);
lean_dec_ref(v_atomsAssignment_857_);
lean_dec(v_aigSize_856_);
lean_dec_ref(v_assignment_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object* v_as_859_, lean_object* v_as_x27_860_, lean_object* v_b_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_860_, v_b_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___boxed(lean_object* v_as_864_, lean_object* v_as_x27_865_, lean_object* v_b_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(v_as_864_, v_as_x27_865_, v_b_866_, v_a_867_);
lean_dec(v_as_x27_865_);
lean_dec(v_as_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object* v_00_u03b2_869_, lean_object* v_m_870_, lean_object* v_a_871_, lean_object* v_fallback_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_870_, v_a_871_, v_fallback_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object* v_00_u03b2_874_, lean_object* v_m_875_, lean_object* v_a_876_, lean_object* v_fallback_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_00_u03b2_874_, v_m_875_, v_a_876_, v_fallback_877_);
lean_dec(v_fallback_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_m_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object* v_00_u03b2_879_, lean_object* v_k_880_, lean_object* v_v_881_, lean_object* v_t_882_, lean_object* v_hl_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_880_, v_v_881_, v_t_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object* v_00_u03b2_885_, lean_object* v_m_886_, lean_object* v_a_887_, lean_object* v_b_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_m_886_, v_a_887_, v_b_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(lean_object* v_00_u03b2_890_, lean_object* v_a_891_, lean_object* v_fallback_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_891_, v_fallback_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___boxed(lean_object* v_00_u03b2_895_, lean_object* v_a_896_, lean_object* v_fallback_897_, lean_object* v_x_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(v_00_u03b2_895_, v_a_896_, v_fallback_897_, v_x_898_);
lean_dec(v_x_898_);
lean_dec(v_fallback_897_);
lean_dec(v_a_896_);
return v_res_899_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(lean_object* v_00_u03b2_900_, lean_object* v_a_901_, lean_object* v_x_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___boxed(lean_object* v_00_u03b2_904_, lean_object* v_a_905_, lean_object* v_x_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(v_00_u03b2_904_, v_a_905_, v_x_906_);
lean_dec(v_x_906_);
lean_dec(v_a_905_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9(lean_object* v_00_u03b2_909_, lean_object* v_data_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(v_data_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10(lean_object* v_00_u03b2_912_, lean_object* v_a_913_, lean_object* v_b_914_, lean_object* v_x_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_913_, v_b_914_, v_x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_917_, lean_object* v_i_918_, lean_object* v_source_919_, lean_object* v_target_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(v_i_918_, v_source_919_, v_target_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19(lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(v_x_923_, v_x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(lean_object* v_mvarId_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_926_, v_x_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_933_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_933_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(lean_object* v_mvarId_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_950_, v_x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_object* v_00_u03b1_958_, lean_object* v_mvarId_959_, lean_object* v_x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_959_, v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(lean_object* v_00_u03b1_967_, lean_object* v_mvarId_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(v_00_u03b1_967_, v_mvarId_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(lean_object* v___x_976_, lean_object* v_x_977_, lean_object* v_counterExample_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_st_mk_ref(v___x_976_);
lean_inc(v___x_984_);
v___x_985_ = lean_apply_7(v_x_977_, v_counterExample_978_, v___x_984_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_994_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_st_ref_get(v___x_984_);
lean_dec(v___x_984_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v___x_984_);
v_a_995_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_985_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_985_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(lean_object* v___x_1003_, lean_object* v_x_1004_, lean_object* v_counterExample_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_1003_, v_x_1004_, v_counterExample_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v_res_1011_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_unsigned_to_nat(16u);
v___x_1014_ = lean_mk_array(v___x_1013_, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1015_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2));
v___x_1021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1);
v___x_1022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
lean_ctor_set(v___x_1022_, 2, v___x_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(lean_object* v_x_1023_, lean_object* v_counterExample_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_goal_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; 
v_goal_1030_ = lean_ctor_get(v_counterExample_1024_, 0);
lean_inc(v_goal_1030_);
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3);
v___f_1032_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1032_, 0, v___x_1031_);
lean_closure_set(v___f_1032_, 1, v_x_1023_);
lean_closure_set(v___f_1032_, 2, v_counterExample_1024_);
v___x_1033_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_goal_1030_, v___f_1032_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(lean_object* v_x_1034_, lean_object* v_counterExample_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_1034_, v_counterExample_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(lean_object* v_a_1042_){
_start:
{
lean_object* v_unusedHypotheses_1044_; lean_object* v___x_1045_; 
v_unusedHypotheses_1044_ = lean_ctor_get(v_a_1042_, 1);
lean_inc_ref(v_unusedHypotheses_1044_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_unusedHypotheses_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_1046_);
lean_dec_ref(v_a_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_unusedHypotheses_1056_; lean_object* v___x_1057_; 
v_unusedHypotheses_1056_ = lean_ctor_get(v_a_1049_, 1);
lean_inc_ref(v_unusedHypotheses_1056_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_unusedHypotheses_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(lean_object* v_a_1066_){
_start:
{
lean_object* v_equations_1068_; lean_object* v___x_1069_; 
v_equations_1068_ = lean_ctor_get(v_a_1066_, 2);
lean_inc_ref(v_equations_1068_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_equations_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_1070_);
lean_dec_ref(v_a_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_equations_1080_; lean_object* v___x_1081_; 
v_equations_1080_ = lean_ctor_get(v_a_1073_, 2);
lean_inc_ref(v_equations_1080_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_equations_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(lean_object* v_e_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_uninterpretedSymbols_1098_; lean_object* v_unusedRelevantHypotheses_1099_; lean_object* v_derivedEquations_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1111_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1097_ = lean_st_ref_take(v_a_1093_);
v_uninterpretedSymbols_1098_ = lean_ctor_get(v___x_1097_, 0);
v_unusedRelevantHypotheses_1099_ = lean_ctor_get(v___x_1097_, 1);
v_derivedEquations_1100_ = lean_ctor_get(v___x_1097_, 2);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1102_ = v___x_1097_;
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_derivedEquations_1100_);
lean_inc(v_unusedRelevantHypotheses_1099_);
lean_inc(v_uninterpretedSymbols_1098_);
lean_dec(v___x_1097_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1095_, v___x_1096_, v_uninterpretedSymbols_1098_, v_e_1092_, v___x_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_unusedRelevantHypotheses_1099_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_derivedEquations_1100_);
v___x_1107_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_st_ref_put(v_a_1093_, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1104_);
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object* v_e_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_1112_, v_a_1113_);
lean_dec(v_a_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(lean_object* v_e_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_uninterpretedSymbols_1127_; lean_object* v_unusedRelevantHypotheses_1128_; lean_object* v_derivedEquations_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1140_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1126_ = lean_st_ref_take(v_a_1118_);
v_uninterpretedSymbols_1127_ = lean_ctor_get(v___x_1126_, 0);
v_unusedRelevantHypotheses_1128_ = lean_ctor_get(v___x_1126_, 1);
v_derivedEquations_1129_ = lean_ctor_get(v___x_1126_, 2);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1131_ = v___x_1126_;
v_isShared_1132_ = v_isSharedCheck_1140_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_derivedEquations_1129_);
lean_inc(v_unusedRelevantHypotheses_1128_);
lean_inc(v_uninterpretedSymbols_1127_);
lean_dec(v___x_1126_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1140_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1124_, v___x_1125_, v_uninterpretedSymbols_1127_, v_e_1116_, v___x_1133_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_unusedRelevantHypotheses_1128_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_derivedEquations_1129_);
v___x_1136_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_st_ref_put(v_a_1118_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1133_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(lean_object* v_e_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object* v_hyp_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v_uninterpretedSymbols_1158_; lean_object* v_unusedRelevantHypotheses_1159_; lean_object* v_derivedEquations_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1171_; 
v___f_1155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1157_ = lean_st_ref_take(v_a_1153_);
v_uninterpretedSymbols_1158_ = lean_ctor_get(v___x_1157_, 0);
v_unusedRelevantHypotheses_1159_ = lean_ctor_get(v___x_1157_, 1);
v_derivedEquations_1160_ = lean_ctor_get(v___x_1157_, 2);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1162_ = v___x_1157_;
v_isShared_1163_ = v_isSharedCheck_1171_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_derivedEquations_1160_);
lean_inc(v_unusedRelevantHypotheses_1159_);
lean_inc(v_uninterpretedSymbols_1158_);
lean_dec(v___x_1157_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1171_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1155_, v___f_1156_, v_unusedRelevantHypotheses_1159_, v_hyp_1152_, v___x_1164_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_uninterpretedSymbols_1158_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_derivedEquations_1160_);
v___x_1167_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_st_ref_put(v_a_1153_, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1164_);
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object* v_hyp_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_hyp_1172_, v_a_1173_);
lean_dec(v_a_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(lean_object* v_hyp_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v_uninterpretedSymbols_1187_; lean_object* v_unusedRelevantHypotheses_1188_; lean_object* v_derivedEquations_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1200_; 
v___f_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1186_ = lean_st_ref_take(v_a_1178_);
v_uninterpretedSymbols_1187_ = lean_ctor_get(v___x_1186_, 0);
v_unusedRelevantHypotheses_1188_ = lean_ctor_get(v___x_1186_, 1);
v_derivedEquations_1189_ = lean_ctor_get(v___x_1186_, 2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1191_ = v___x_1186_;
v_isShared_1192_ = v_isSharedCheck_1200_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_derivedEquations_1189_);
lean_inc(v_unusedRelevantHypotheses_1188_);
lean_inc(v_uninterpretedSymbols_1187_);
lean_dec(v___x_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1200_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_box(0);
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1184_, v___f_1185_, v_unusedRelevantHypotheses_1188_, v_hyp_1176_, v___x_1193_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_uninterpretedSymbols_1187_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_derivedEquations_1189_);
v___x_1196_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_st_ref_put(v_a_1178_, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1193_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object* v_hyp_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_hyp_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(lean_object* v_var_1210_, lean_object* v_value_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_uninterpretedSymbols_1215_; lean_object* v_unusedRelevantHypotheses_1216_; lean_object* v_derivedEquations_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1229_; 
v___x_1214_ = lean_st_ref_take(v_a_1212_);
v_uninterpretedSymbols_1215_ = lean_ctor_get(v___x_1214_, 0);
v_unusedRelevantHypotheses_1216_ = lean_ctor_get(v___x_1214_, 1);
v_derivedEquations_1217_ = lean_ctor_get(v___x_1214_, 2);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1219_ = v___x_1214_;
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_derivedEquations_1217_);
lean_inc(v_unusedRelevantHypotheses_1216_);
lean_inc(v_uninterpretedSymbols_1215_);
lean_dec(v___x_1214_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_var_1210_);
lean_ctor_set(v___x_1222_, 1, v_value_1211_);
v___x_1223_ = lean_array_push(v_derivedEquations_1217_, v___x_1222_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 2, v___x_1223_);
v___x_1225_ = v___x_1219_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_uninterpretedSymbols_1215_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_unusedRelevantHypotheses_1216_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_st_ref_put(v_a_1212_, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1221_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object* v_var_1230_, lean_object* v_value_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_1230_, v_value_1231_, v_a_1232_);
lean_dec(v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(lean_object* v_var_1235_, lean_object* v_value_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v_uninterpretedSymbols_1245_; lean_object* v_unusedRelevantHypotheses_1246_; lean_object* v_derivedEquations_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
v___x_1244_ = lean_st_ref_take(v_a_1238_);
v_uninterpretedSymbols_1245_ = lean_ctor_get(v___x_1244_, 0);
v_unusedRelevantHypotheses_1246_ = lean_ctor_get(v___x_1244_, 1);
v_derivedEquations_1247_ = lean_ctor_get(v___x_1244_, 2);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1249_ = v___x_1244_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_derivedEquations_1247_);
lean_inc(v_unusedRelevantHypotheses_1246_);
lean_inc(v_uninterpretedSymbols_1245_);
lean_dec(v___x_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_var_1235_);
lean_ctor_set(v___x_1252_, 1, v_value_1236_);
v___x_1253_ = lean_array_push(v_derivedEquations_1247_, v___x_1252_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 2, v___x_1253_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_uninterpretedSymbols_1245_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_unusedRelevantHypotheses_1246_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_st_ref_put(v_a_1238_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1251_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(lean_object* v_var_1260_, lean_object* v_value_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_1260_, v_value_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object* v_a_1270_, lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = 0;
return v___x_1272_;
}
else
{
lean_object* v_key_1273_; lean_object* v_tail_1274_; lean_object* v_type_1275_; lean_object* v_type_1276_; uint8_t v___x_1277_; 
v_key_1273_ = lean_ctor_get(v_x_1271_, 0);
v_tail_1274_ = lean_ctor_get(v_x_1271_, 2);
v_type_1275_ = lean_ctor_get(v_key_1273_, 1);
v_type_1276_ = lean_ctor_get(v_a_1270_, 1);
v___x_1277_ = lean_expr_eqv(v_type_1275_, v_type_1276_);
if (v___x_1277_ == 0)
{
v_x_1271_ = v_tail_1274_;
goto _start;
}
else
{
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object* v_a_1279_, lean_object* v_x_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1279_, v_x_1280_);
lean_dec(v_x_1280_);
lean_dec_ref(v_a_1279_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1284_) == 0)
{
return v_x_1283_;
}
else
{
lean_object* v_key_1285_; lean_object* v_value_1286_; lean_object* v_tail_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1311_; 
v_key_1285_ = lean_ctor_get(v_x_1284_, 0);
v_value_1286_ = lean_ctor_get(v_x_1284_, 1);
v_tail_1287_ = lean_ctor_get(v_x_1284_, 2);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1284_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1289_ = v_x_1284_;
v_isShared_1290_ = v_isSharedCheck_1311_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_tail_1287_);
lean_inc(v_value_1286_);
lean_inc(v_key_1285_);
lean_dec(v_x_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1311_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_type_1291_; lean_object* v___x_1292_; uint64_t v___x_1293_; uint64_t v___x_1294_; uint64_t v___x_1295_; uint64_t v_fold_1296_; uint64_t v___x_1297_; uint64_t v___x_1298_; uint64_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v_type_1291_ = lean_ctor_get(v_key_1285_, 1);
v___x_1292_ = lean_array_get_size(v_x_1283_);
v___x_1293_ = l_Lean_Expr_hash(v_type_1291_);
v___x_1294_ = 32ULL;
v___x_1295_ = lean_uint64_shift_right(v___x_1293_, v___x_1294_);
v_fold_1296_ = lean_uint64_xor(v___x_1293_, v___x_1295_);
v___x_1297_ = 16ULL;
v___x_1298_ = lean_uint64_shift_right(v_fold_1296_, v___x_1297_);
v___x_1299_ = lean_uint64_xor(v_fold_1296_, v___x_1298_);
v___x_1300_ = lean_uint64_to_usize(v___x_1299_);
v___x_1301_ = lean_usize_of_nat(v___x_1292_);
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_sub(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_usize_land(v___x_1300_, v___x_1303_);
v___x_1305_ = lean_array_uget_borrowed(v_x_1283_, v___x_1304_);
lean_inc(v___x_1305_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 2, v___x_1305_);
v___x_1307_ = v___x_1289_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_key_1285_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_value_1286_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_array_uset(v_x_1283_, v___x_1304_, v___x_1307_);
v_x_1283_ = v___x_1308_;
v_x_1284_ = v_tail_1287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1312_, lean_object* v_source_1313_, lean_object* v_target_1314_){
_start:
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_array_get_size(v_source_1313_);
v___x_1316_ = lean_nat_dec_lt(v_i_1312_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_source_1313_);
lean_dec(v_i_1312_);
return v_target_1314_;
}
else
{
lean_object* v_es_1317_; lean_object* v___x_1318_; lean_object* v_source_1319_; lean_object* v_target_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_es_1317_ = lean_array_fget(v_source_1313_, v_i_1312_);
v___x_1318_ = lean_box(0);
v_source_1319_ = lean_array_fset(v_source_1313_, v_i_1312_, v___x_1318_);
v_target_1320_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_target_1314_, v_es_1317_);
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_add(v_i_1312_, v___x_1321_);
lean_dec(v_i_1312_);
v_i_1312_ = v___x_1322_;
v_source_1313_ = v_source_1319_;
v_target_1314_ = v_target_1320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(lean_object* v_data_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_nbuckets_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1325_ = lean_array_get_size(v_data_1324_);
v___x_1326_ = lean_unsigned_to_nat(2u);
v_nbuckets_1327_ = lean_nat_mul(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_mk_array(v_nbuckets_1327_, v___x_1329_);
v___x_1331_ = lean_array_propagate_mark(v_data_1324_, v___x_1330_);
v___x_1332_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v___x_1328_, v_data_1324_, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object* v_m_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_){
_start:
{
lean_object* v_size_1336_; lean_object* v_buckets_1337_; lean_object* v_type_1338_; lean_object* v___x_1339_; uint64_t v___x_1340_; uint64_t v___x_1341_; uint64_t v___x_1342_; uint64_t v_fold_1343_; uint64_t v___x_1344_; uint64_t v___x_1345_; uint64_t v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; lean_object* v_bkt_1352_; uint8_t v___x_1353_; 
v_size_1336_ = lean_ctor_get(v_m_1333_, 0);
v_buckets_1337_ = lean_ctor_get(v_m_1333_, 1);
v_type_1338_ = lean_ctor_get(v_a_1334_, 1);
v___x_1339_ = lean_array_get_size(v_buckets_1337_);
v___x_1340_ = l_Lean_Expr_hash(v_type_1338_);
v___x_1341_ = 32ULL;
v___x_1342_ = lean_uint64_shift_right(v___x_1340_, v___x_1341_);
v_fold_1343_ = lean_uint64_xor(v___x_1340_, v___x_1342_);
v___x_1344_ = 16ULL;
v___x_1345_ = lean_uint64_shift_right(v_fold_1343_, v___x_1344_);
v___x_1346_ = lean_uint64_xor(v_fold_1343_, v___x_1345_);
v___x_1347_ = lean_uint64_to_usize(v___x_1346_);
v___x_1348_ = lean_usize_of_nat(v___x_1339_);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_sub(v___x_1348_, v___x_1349_);
v___x_1351_ = lean_usize_land(v___x_1347_, v___x_1350_);
v_bkt_1352_ = lean_array_uget_borrowed(v_buckets_1337_, v___x_1351_);
v___x_1353_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1334_, v_bkt_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1374_; 
lean_inc_ref(v_buckets_1337_);
lean_inc(v_size_1336_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_m_1333_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v_m_1333_, 1);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_m_1333_, 0);
lean_dec(v_unused_1376_);
v___x_1355_ = v_m_1333_;
v_isShared_1356_ = v_isSharedCheck_1374_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_m_1333_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1374_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v_size_x27_1358_; lean_object* v___x_1359_; lean_object* v_buckets_x27_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1357_ = lean_unsigned_to_nat(1u);
v_size_x27_1358_ = lean_nat_add(v_size_1336_, v___x_1357_);
lean_dec(v_size_1336_);
lean_inc(v_bkt_1352_);
v___x_1359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1359_, 0, v_a_1334_);
lean_ctor_set(v___x_1359_, 1, v_b_1335_);
lean_ctor_set(v___x_1359_, 2, v_bkt_1352_);
v_buckets_x27_1360_ = lean_array_uset(v_buckets_1337_, v___x_1351_, v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(4u);
v___x_1362_ = lean_nat_mul(v_size_x27_1358_, v___x_1361_);
v___x_1363_ = lean_unsigned_to_nat(3u);
v___x_1364_ = lean_nat_div(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_array_get_size(v_buckets_x27_1360_);
v___x_1366_ = lean_nat_dec_le(v___x_1364_, v___x_1365_);
lean_dec(v___x_1364_);
if (v___x_1366_ == 0)
{
lean_object* v_val_1367_; lean_object* v___x_1369_; 
v_val_1367_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_buckets_x27_1360_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v_val_1367_);
lean_ctor_set(v___x_1355_, 0, v_size_x27_1358_);
v___x_1369_ = v___x_1355_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_size_x27_1358_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_val_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1372_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v_buckets_x27_1360_);
lean_ctor_set(v___x_1355_, 0, v_size_x27_1358_);
v___x_1372_ = v___x_1355_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_size_x27_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_buckets_x27_1360_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_dec(v_b_1335_);
lean_dec_ref(v_a_1334_);
return v_m_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object* v_fvar_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v___y_1380_){
_start:
{
if (lean_obj_tag(v_a_1378_) == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_a_1379_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
else
{
lean_object* v_key_1384_; lean_object* v_tail_1385_; lean_object* v_type_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_key_1384_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_key_1384_);
v_tail_1385_ = lean_ctor_get(v_a_1378_, 2);
lean_inc(v_tail_1385_);
lean_dec_ref_known(v_a_1378_, 3);
v_type_1386_ = lean_ctor_get(v_key_1384_, 1);
v___x_1387_ = lean_box(0);
v___x_1388_ = l_Lean_Expr_containsFVar(v_type_1386_, v_fvar_1377_);
if (v___x_1388_ == 0)
{
lean_dec(v_key_1384_);
v_a_1378_ = v_tail_1385_;
v_a_1379_ = v___x_1387_;
goto _start;
}
else
{
lean_object* v___x_1390_; lean_object* v_uninterpretedSymbols_1391_; lean_object* v_unusedRelevantHypotheses_1392_; lean_object* v_derivedEquations_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1403_; 
v___x_1390_ = lean_st_ref_take(v___y_1380_);
v_uninterpretedSymbols_1391_ = lean_ctor_get(v___x_1390_, 0);
v_unusedRelevantHypotheses_1392_ = lean_ctor_get(v___x_1390_, 1);
v_derivedEquations_1393_ = lean_ctor_get(v___x_1390_, 2);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1395_ = v___x_1390_;
v_isShared_1396_ = v_isSharedCheck_1403_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_derivedEquations_1393_);
lean_inc(v_unusedRelevantHypotheses_1392_);
lean_inc(v_uninterpretedSymbols_1391_);
lean_dec(v___x_1390_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1403_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_unusedRelevantHypotheses_1392_, v_key_1384_, v___x_1387_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_uninterpretedSymbols_1391_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_derivedEquations_1393_);
v___x_1399_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_st_ref_put(v___y_1380_, v___x_1399_);
v_a_1378_ = v_tail_1385_;
v_a_1379_ = v___x_1387_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object* v_fvar_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1404_, v_a_1405_, v_a_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec(v_fvar_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object* v_fvar_1410_, lean_object* v_as_1411_, size_t v_sz_1412_, size_t v_i_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_lt(v_i_1413_, v_sz_1412_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_b_1414_);
return v___x_1423_;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_array_uget_borrowed(v_as_1411_, v_i_1413_);
lean_inc(v_a_1424_);
v___x_1425_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1410_, v_a_1424_, v_b_1414_, v___y_1416_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1438_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1438_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1438_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
if (lean_obj_tag(v_a_1426_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; 
v_a_1430_ = lean_ctor_get(v_a_1426_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v_a_1426_, 1);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v_a_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
lean_object* v_a_1434_; size_t v___x_1435_; size_t v___x_1436_; 
lean_del_object(v___x_1428_);
v_a_1434_ = lean_ctor_get(v_a_1426_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v_a_1426_, 1);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_add(v_i_1413_, v___x_1435_);
v_i_1413_ = v___x_1436_;
v_b_1414_ = v_a_1434_;
goto _start;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1425_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1425_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object* v_fvar_1447_, lean_object* v_as_1448_, lean_object* v_sz_1449_, lean_object* v_i_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1449_);
lean_dec(v_sz_1449_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1447_, v_as_1448_, v_sz_boxed_1459_, v_i_boxed_1460_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v_as_1448_);
lean_dec(v_fvar_1447_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object* v_fvar_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_unusedHypotheses_1470_; lean_object* v_buckets_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v_unusedHypotheses_1470_ = lean_ctor_get(v_a_1463_, 1);
v_buckets_1471_ = lean_ctor_get(v_unusedHypotheses_1470_, 1);
v___x_1472_ = lean_box(0);
v_sz_1473_ = lean_array_size(v_buckets_1471_);
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1462_, v_buckets_1471_, v_sz_1473_, v___x_1474_, v___x_1472_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v___x_1475_, 0);
lean_dec(v_unused_1483_);
v___x_1477_ = v___x_1475_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v___x_1475_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1472_);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1472_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object* v_fvar_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_fvar_1484_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object* v_00_u03b2_1493_, lean_object* v_m_1494_, lean_object* v_a_1495_, lean_object* v_b_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_1494_, v_a_1495_, v_b_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object* v_fvar_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1498_, v_a_1499_, v_a_1500_, v___y_1502_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object* v_fvar_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_fvar_1509_, v_a_1510_, v_a_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v_fvar_1509_);
return v_res_1519_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object* v_00_u03b2_1520_, lean_object* v_a_1521_, lean_object* v_x_1522_){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1521_, v_x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1524_, lean_object* v_a_1525_, lean_object* v_x_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(v_00_u03b2_1524_, v_a_1525_, v_x_1526_);
lean_dec(v_x_1526_);
lean_dec_ref(v_a_1525_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1(lean_object* v_00_u03b2_1529_, lean_object* v_data_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_data_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1532_, lean_object* v_i_1533_, lean_object* v_source_1534_, lean_object* v_target_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v_i_1533_, v_source_1534_, v_target_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_x_1538_, v_x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_instMonadEIO___redArg();
return v___x_1541_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = l_Lean_instInhabitedExpr;
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(lean_object* v_msg_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_toApplicative_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1621_; 
v___x_1556_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0);
v___x_1557_ = l_StateRefT_x27_instMonad___redArg(v___x_1556_);
v_toApplicative_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1557_, 1);
lean_dec(v_unused_1622_);
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1621_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_toApplicative_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1621_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_toFunctor_1562_; lean_object* v_toSeq_1563_; lean_object* v_toSeqLeft_1564_; lean_object* v_toSeqRight_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1619_; 
v_toFunctor_1562_ = lean_ctor_get(v_toApplicative_1558_, 0);
v_toSeq_1563_ = lean_ctor_get(v_toApplicative_1558_, 2);
v_toSeqLeft_1564_ = lean_ctor_get(v_toApplicative_1558_, 3);
v_toSeqRight_1565_ = lean_ctor_get(v_toApplicative_1558_, 4);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_toApplicative_1558_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; 
v_unused_1620_ = lean_ctor_get(v_toApplicative_1558_, 1);
lean_dec(v_unused_1620_);
v___x_1567_ = v_toApplicative_1558_;
v_isShared_1568_ = v_isSharedCheck_1619_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_toSeqRight_1565_);
lean_inc(v_toSeqLeft_1564_);
lean_inc(v_toSeq_1563_);
lean_inc(v_toFunctor_1562_);
lean_dec(v_toApplicative_1558_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1619_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___f_1569_; lean_object* v___f_1570_; lean_object* v___f_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___f_1575_; lean_object* v___f_1576_; lean_object* v___x_1578_; 
v___f_1569_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1));
v___f_1570_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1562_);
v___f_1571_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1571_, 0, v_toFunctor_1562_);
v___f_1572_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1572_, 0, v_toFunctor_1562_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___f_1571_);
lean_ctor_set(v___x_1573_, 1, v___f_1572_);
v___f_1574_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1574_, 0, v_toSeqRight_1565_);
v___f_1575_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1575_, 0, v_toSeqLeft_1564_);
v___f_1576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1576_, 0, v_toSeq_1563_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v___f_1574_);
lean_ctor_set(v___x_1567_, 3, v___f_1575_);
lean_ctor_set(v___x_1567_, 2, v___f_1576_);
lean_ctor_set(v___x_1567_, 1, v___f_1569_);
lean_ctor_set(v___x_1567_, 0, v___x_1573_);
v___x_1578_ = v___x_1567_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___f_1569_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v___f_1576_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v___f_1575_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v___f_1574_);
v___x_1578_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v___f_1570_);
lean_ctor_set(v___x_1560_, 0, v___x_1578_);
v___x_1580_ = v___x_1560_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___f_1570_);
v___x_1580_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v_toApplicative_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1615_; 
v___x_1581_ = l_StateRefT_x27_instMonad___redArg(v___x_1580_);
v_toApplicative_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1581_, 1);
lean_dec(v_unused_1616_);
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1615_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_toApplicative_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1615_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_toFunctor_1586_; lean_object* v_toSeq_1587_; lean_object* v_toSeqLeft_1588_; lean_object* v_toSeqRight_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1613_; 
v_toFunctor_1586_ = lean_ctor_get(v_toApplicative_1582_, 0);
v_toSeq_1587_ = lean_ctor_get(v_toApplicative_1582_, 2);
v_toSeqLeft_1588_ = lean_ctor_get(v_toApplicative_1582_, 3);
v_toSeqRight_1589_ = lean_ctor_get(v_toApplicative_1582_, 4);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_toApplicative_1582_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_toApplicative_1582_, 1);
lean_dec(v_unused_1614_);
v___x_1591_ = v_toApplicative_1582_;
v_isShared_1592_ = v_isSharedCheck_1613_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_toSeqRight_1589_);
lean_inc(v_toSeqLeft_1588_);
lean_inc(v_toSeq_1587_);
lean_inc(v_toFunctor_1586_);
lean_dec(v_toApplicative_1582_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1613_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___f_1593_; lean_object* v___f_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___f_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; lean_object* v___x_1602_; 
v___f_1593_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3));
v___f_1594_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1586_);
v___f_1595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1595_, 0, v_toFunctor_1586_);
v___f_1596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1596_, 0, v_toFunctor_1586_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___f_1595_);
lean_ctor_set(v___x_1597_, 1, v___f_1596_);
v___f_1598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1598_, 0, v_toSeqRight_1589_);
v___f_1599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1599_, 0, v_toSeqLeft_1588_);
v___f_1600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1600_, 0, v_toSeq_1587_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 4, v___f_1598_);
lean_ctor_set(v___x_1591_, 3, v___f_1599_);
lean_ctor_set(v___x_1591_, 2, v___f_1600_);
lean_ctor_set(v___x_1591_, 1, v___f_1593_);
lean_ctor_set(v___x_1591_, 0, v___x_1597_);
v___x_1602_ = v___x_1591_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___f_1593_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v___f_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___f_1599_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___f_1598_);
v___x_1602_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1604_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v___f_1594_);
lean_ctor_set(v___x_1584_, 0, v___x_1602_);
v___x_1604_ = v___x_1584_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___f_1594_);
v___x_1604_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___x_11566__overap_1609_; lean_object* v___x_1610_; 
v___x_1605_ = l_StateRefT_x27_instMonad___redArg(v___x_1604_);
v___x_1606_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5);
v___x_1607_ = l_instInhabitedOfMonad___redArg(v___x_1605_, v___x_1606_);
v___f_1608_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1608_, 0, v___x_1607_);
v___x_11566__overap_1609_ = lean_panic_fn_borrowed(v___f_1608_, v_msg_1548_);
lean_dec_ref(v___f_1608_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc_ref(v___y_1549_);
v___x_1610_ = lean_apply_7(v___x_11566__overap_1609_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
return v___x_1610_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(lean_object* v_msg_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(lean_object* v_msgData_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_env_1639_; lean_object* v___x_1640_; lean_object* v_toCold_1641_; lean_object* v_mctx_1642_; lean_object* v_lctx_1643_; lean_object* v_options_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1638_ = lean_st_ref_get(v___y_1636_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1640_ = lean_st_ref_get(v___y_1634_);
v_toCold_1641_ = lean_ctor_get(v___y_1635_, 0);
v_mctx_1642_ = lean_ctor_get(v___x_1640_, 0);
lean_inc_ref(v_mctx_1642_);
lean_dec(v___x_1640_);
v_lctx_1643_ = lean_ctor_get(v___y_1633_, 2);
v_options_1644_ = lean_ctor_get(v_toCold_1641_, 2);
lean_inc_ref(v_options_1644_);
lean_inc_ref(v_lctx_1643_);
v___x_1645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1645_, 0, v_env_1639_);
lean_ctor_set(v___x_1645_, 1, v_mctx_1642_);
lean_ctor_set(v___x_1645_, 2, v_lctx_1643_);
lean_ctor_set(v___x_1645_, 3, v_options_1644_);
v___x_1646_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_msgData_1632_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(lean_object* v_msgData_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_ref_1661_; lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1671_; 
v_ref_1661_ = lean_ctor_get(v___y_1658_, 2);
v___x_1662_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msg_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_inc(v_ref_1661_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_ref_1661_);
lean_ctor_set(v___x_1667_, 1, v_a_1663_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1679_, lean_object* v_msg_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_toCold_1688_; lean_object* v_currRecDepth_1689_; lean_object* v_ref_1690_; uint8_t v_diag_1691_; uint8_t v_suppressElabErrors_1692_; lean_object* v_ref_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_toCold_1688_ = lean_ctor_get(v___y_1685_, 0);
v_currRecDepth_1689_ = lean_ctor_get(v___y_1685_, 1);
v_ref_1690_ = lean_ctor_get(v___y_1685_, 2);
v_diag_1691_ = lean_ctor_get_uint8(v___y_1685_, sizeof(void*)*3);
v_suppressElabErrors_1692_ = lean_ctor_get_uint8(v___y_1685_, sizeof(void*)*3 + 1);
v_ref_1693_ = l_Lean_replaceRef(v_ref_1679_, v_ref_1690_);
lean_inc(v_currRecDepth_1689_);
lean_inc_ref(v_toCold_1688_);
v___x_1694_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1694_, 0, v_toCold_1688_);
lean_ctor_set(v___x_1694_, 1, v_currRecDepth_1689_);
lean_ctor_set(v___x_1694_, 2, v_ref_1693_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3, v_diag_1691_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 1, v_suppressElabErrors_1692_);
v___x_1695_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1680_, v___y_1683_, v___y_1684_, v___x_1694_, v___y_1686_);
lean_dec_ref_known(v___x_1694_, 3);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1696_, lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1696_, v_msg_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v_ref_1696_);
return v_res_1705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
lean_ctor_set(v___x_1711_, 2, v___x_1710_);
lean_ctor_set(v___x_1711_, 3, v___x_1710_);
lean_ctor_set(v___x_1711_, 4, v___x_1709_);
lean_ctor_set(v___x_1711_, 5, v___x_1709_);
lean_ctor_set(v___x_1711_, 6, v___x_1709_);
lean_ctor_set(v___x_1711_, 7, v___x_1709_);
lean_ctor_set(v___x_1711_, 8, v___x_1709_);
lean_ctor_set(v___x_1711_, 9, v___x_1709_);
lean_ctor_set(v___x_1711_, 10, v___x_1709_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_unsigned_to_nat(32u);
v___x_1713_ = lean_mk_empty_array_with_capacity(v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = ((size_t)5ULL);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_unsigned_to_nat(32u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1720_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___x_1718_);
lean_ctor_set(v___x_1720_, 2, v___x_1716_);
lean_ctor_set(v___x_1720_, 3, v___x_1716_);
lean_ctor_set_usize(v___x_1720_, 4, v___x_1715_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_box(1);
v___x_1722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_1723_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1722_);
lean_ctor_set(v___x_1724_, 2, v___x_1721_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1730_ = l_Lean_stringToMessageData(v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
return v___x_1739_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_1742_ = l_Lean_stringToMessageData(v___x_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1746_, lean_object* v_declHint_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; uint8_t v___x_1753_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_st_ref_get(v___y_1748_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = l_Lean_Name_isAnonymous(v_declHint_1747_);
if (v___x_1753_ == 0)
{
uint8_t v_isExporting_1754_; 
v_isExporting_1754_ = lean_ctor_get_uint8(v_env_1752_, sizeof(void*)*8);
if (v_isExporting_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_dec_ref(v_env_1752_);
lean_dec(v_declHint_1747_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_msg_1746_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
lean_inc_ref(v_env_1752_);
v___x_1756_ = l_Lean_Environment_setExporting(v_env_1752_, v___x_1753_);
lean_inc(v_declHint_1747_);
lean_inc_ref(v___x_1756_);
v___x_1757_ = l_Lean_Environment_contains(v___x_1756_, v_declHint_1747_, v_isExporting_1754_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_env_1752_);
lean_dec(v_declHint_1747_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_msg_1746_);
return v___x_1758_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_c_1764_; lean_object* v___x_1765_; 
v___x_1759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_1760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1761_ = l_Lean_Options_empty;
v___x_1762_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1756_);
lean_ctor_set(v___x_1762_, 1, v___x_1759_);
lean_ctor_set(v___x_1762_, 2, v___x_1760_);
lean_ctor_set(v___x_1762_, 3, v___x_1761_);
lean_inc(v_declHint_1747_);
v___x_1763_ = l_Lean_MessageData_ofConstName(v_declHint_1747_, v___x_1753_);
v_c_1764_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1764_, 0, v___x_1762_);
lean_ctor_set(v_c_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1752_, v_declHint_1747_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_env_1752_);
lean_dec(v_declHint_1747_);
v___x_1766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_c_1764_);
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_MessageData_note(v___x_1769_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_msg_1746_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
else
{
lean_object* v_val_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1807_; 
v_val_1773_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1775_ = v___x_1765_;
v_isShared_1776_ = v_isSharedCheck_1807_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_val_1773_);
lean_dec(v___x_1765_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1807_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_mod_1779_; uint8_t v___x_1780_; 
v___x_1777_ = l_Lean_Environment_header(v_env_1752_);
lean_dec_ref(v_env_1752_);
v___x_1778_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1777_);
v_mod_1779_ = lean_array_get(v___x_1750_, v___x_1778_, v_val_1773_);
lean_dec(v_val_1773_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = l_Lean_isPrivateName(v_declHint_1747_);
lean_dec(v_declHint_1747_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_c_1764_);
v___x_1783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_MessageData_ofName(v_mod_1779_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_MessageData_note(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_msg_1746_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1790_);
v___x_1792_ = v___x_1775_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_c_1764_);
v___x_1796_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_MessageData_ofName(v_mod_1779_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Lean_MessageData_note(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_msg_1746_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1803_);
v___x_1805_ = v___x_1775_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v_env_1752_);
lean_dec(v_declHint_1747_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_msg_1746_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1809_, lean_object* v_declHint_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1809_, v_declHint_1810_, v___y_1811_);
lean_dec(v___y_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_1814_, lean_object* v_declHint_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1833_; 
v___x_1823_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1814_, v_declHint_1815_, v___y_1821_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1828_ = l_Lean_unknownIdentifierMessageTag;
v___x_1829_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_a_1824_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1829_);
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_1834_, lean_object* v_declHint_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1834_, v_declHint_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_1844_, lean_object* v_msg_1845_, lean_object* v_declHint_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v_a_1855_; lean_object* v___x_1856_; 
v___x_1854_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1845_, v_declHint_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1844_, v_a_1855_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1857_, lean_object* v_msg_1858_, lean_object* v_declHint_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1857_, v_msg_1858_, v_declHint_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_ref_1857_);
return v_res_1867_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1874_, lean_object* v_constName_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1883_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1884_ = 0;
lean_inc(v_constName_1875_);
v___x_1885_ = l_Lean_MessageData_ofConstName(v_constName_1875_, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1883_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1874_, v___x_1888_, v_constName_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1890_, lean_object* v_constName_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1890_, v_constName_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v_ref_1890_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object* v_constName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_ref_1908_; lean_object* v___x_1909_; 
v_ref_1908_ = lean_ctor_get(v___y_1905_, 2);
v___x_1909_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1908_, v_constName_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(lean_object* v_constName_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v_env_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1927_ = lean_st_ref_get(v___y_1925_);
v_env_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_ref(v_env_1928_);
lean_dec(v___x_1927_);
v___x_1929_ = 0;
lean_inc(v_constName_1919_);
v___x_1930_ = l_Lean_Environment_find_x3f(v_env_1928_, v_constName_1919_, v___x_1929_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1931_;
}
else
{
lean_object* v_val_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_constName_1919_);
v_val_1932_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1930_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_val_1932_);
lean_dec(v___x_1930_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 0);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_val_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object* v_constName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1948_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2));
v___x_1956_ = l_Lean_Expr_const___override(v___x_1955_, v___x_1954_);
return v___x_1956_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5));
v___x_1960_ = lean_unsigned_to_nat(61u);
v___x_1961_ = lean_unsigned_to_nat(219u);
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4));
v___x_1963_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0));
v___x_1964_ = l_mkPanicMessageWithDecl(v___x_1963_, v___x_1962_, v___x_1961_, v___x_1960_, v___x_1959_);
return v___x_1964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36));
v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
return v___x_2023_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = l_Lean_Level_ofNat(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
v___x_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2030_);
return v___x_2032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39));
v___x_2035_ = l_Lean_Expr_const___override(v___x_2034_, v___x_2033_);
return v___x_2035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43));
v___x_2040_ = l_Lean_mkConst(v___x_2039_, v___x_2038_);
return v___x_2040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46));
v___x_2047_ = l_Lean_Expr_const___override(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48));
v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
return v___x_2050_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50));
v___x_2053_ = l_Lean_stringToMessageData(v___x_2052_);
return v___x_2053_;
}
}
static size_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52(void){
_start:
{
lean_object* v___x_2054_; size_t v___x_2055_; 
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_isize_of_nat(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55));
v___x_2063_ = l_Lean_Expr_const___override(v___x_2062_, v___x_2061_);
return v___x_2063_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57));
v___x_2068_ = l_Lean_Expr_const___override(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60));
v___x_2075_ = l_Lean_Expr_const___override(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62));
v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_box(0);
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66));
v___x_2086_ = l_Lean_mkConst(v___x_2085_, v___x_2084_);
return v___x_2086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69));
v___x_2093_ = l_Lean_mkConst(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73));
v___x_2101_ = l_Lean_mkConst(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75));
v___x_2107_ = l_Lean_Expr_const___override(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79));
v___x_2115_ = l_Lean_mkConst(v___x_2114_, v___x_2113_);
return v___x_2115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81));
v___x_2121_ = l_Lean_Expr_const___override(v___x_2120_, v___x_2119_);
return v___x_2121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83));
v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
return v___x_2124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85));
v___x_2129_ = l_Lean_mkConst(v___x_2128_, v___x_2127_);
return v___x_2129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87));
v___x_2135_ = l_Lean_Expr_const___override(v___x_2134_, v___x_2133_);
return v___x_2135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91));
v___x_2143_ = l_Lean_mkConst(v___x_2142_, v___x_2141_);
return v___x_2143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93));
v___x_2149_ = l_Lean_Expr_const___override(v___x_2148_, v___x_2147_);
return v___x_2149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97(void){
_start:
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
v___x_2154_ = lean_int8_of_nat(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98));
v___x_2159_ = l_Lean_Expr_const___override(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_box(0);
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100));
v___x_2165_ = l_Lean_Expr_const___override(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102));
v___x_2168_ = l_Lean_stringToMessageData(v___x_2167_);
return v___x_2168_;
}
}
static uint16_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104(void){
_start:
{
lean_object* v___x_2169_; uint16_t v___x_2170_; 
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = lean_int16_of_nat(v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105));
v___x_2175_ = l_Lean_Expr_const___override(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107));
v___x_2181_ = l_Lean_Expr_const___override(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
static uint32_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111(void){
_start:
{
lean_object* v___x_2185_; uint32_t v___x_2186_; 
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = lean_int32_of_nat(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = lean_box(0);
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112));
v___x_2191_ = l_Lean_Expr_const___override(v___x_2190_, v___x_2189_);
return v___x_2191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_box(0);
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114));
v___x_2197_ = l_Lean_Expr_const___override(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116));
v___x_2200_ = l_Lean_stringToMessageData(v___x_2199_);
return v___x_2200_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118(void){
_start:
{
lean_object* v___x_2201_; uint64_t v___x_2202_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_int64_of_nat(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_box(0);
v___x_2206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119));
v___x_2207_ = l_Lean_Expr_const___override(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121));
v___x_2213_ = l_Lean_Expr_const___override(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object* v_var_2214_, lean_object* v_value_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = l_Lean_Expr_isFVar(v_var_2214_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___x_2301_; 
v___x_2239_ = lean_box(0);
lean_inc_ref(v_var_2214_);
v___x_2301_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_2214_, v_a_2219_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2750_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2750_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2750_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = l_Lean_Expr_cleanupAnnotations(v_a_2302_);
v___x_2307_ = l_Lean_Expr_isApp(v___x_2306_);
if (v___x_2307_ == 0)
{
lean_dec_ref(v___x_2306_);
lean_del_object(v___x_2304_);
v___y_2241_ = v_a_2216_;
v___y_2242_ = v_a_2217_;
v___y_2243_ = v_a_2218_;
v___y_2244_ = v_a_2219_;
v___y_2245_ = v_a_2220_;
v___y_2246_ = v_a_2221_;
goto v___jp_2240_;
}
else
{
lean_object* v_arg_2308_; lean_object* v___y_2310_; lean_object* v___y_2316_; lean_object* v___y_2320_; lean_object* v___y_2324_; lean_object* v___y_2328_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v_arg_2308_ = lean_ctor_get(v___x_2306_, 1);
lean_inc_ref(v_arg_2308_);
v___x_2331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2306_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9));
v___x_2333_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
lean_del_object(v___x_2304_);
v___x_2334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11));
v___x_2335_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13));
v___x_2337_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15));
v___x_2339_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17));
v___x_2341_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19));
v___x_2343_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21));
v___x_2345_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2344_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23));
v___x_2347_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25));
v___x_2349_ = l_Lean_Expr_isConstOf(v___x_2331_, v___x_2348_);
if (v___x_2349_ == 0)
{
uint8_t v___x_2350_; 
lean_dec_ref(v_arg_2308_);
v___x_2350_ = l_Lean_Expr_isApp(v___x_2331_);
if (v___x_2350_ == 0)
{
lean_dec_ref(v___x_2331_);
v___y_2241_ = v_a_2216_;
v___y_2242_ = v_a_2217_;
v___y_2243_ = v_a_2218_;
v___y_2244_ = v_a_2219_;
v___y_2245_ = v_a_2220_;
v___y_2246_ = v_a_2221_;
goto v___jp_2240_;
}
else
{
lean_object* v_arg_2351_; lean_object* v___y_2353_; lean_object* v___y_2357_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_arg_2351_ = lean_ctor_get(v___x_2331_, 1);
lean_inc_ref(v_arg_2351_);
v___x_2360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2331_);
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28));
v___x_2362_ = l_Lean_Expr_isConstOf(v___x_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30));
v___x_2364_ = l_Lean_Expr_isConstOf(v___x_2360_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32));
v___x_2366_ = l_Lean_Expr_isConstOf(v___x_2360_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33));
v___x_2368_ = l_Lean_Expr_isConstOf(v___x_2360_, v___x_2367_);
lean_dec_ref(v___x_2360_);
if (v___x_2368_ == 0)
{
lean_dec_ref(v_arg_2351_);
v___y_2241_ = v_a_2216_;
v___y_2242_ = v_a_2217_;
v___y_2243_ = v_a_2218_;
v___y_2244_ = v_a_2219_;
v___y_2245_ = v_a_2220_;
v___y_2246_ = v_a_2221_;
goto v___jp_2240_;
}
else
{
lean_object* v_w_2369_; lean_object* v_bv_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_var_2214_);
v_w_2369_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2370_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2372_ = v_value_2215_;
v_isShared_2373_ = v_isSharedCheck_2398_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_bv_2370_);
lean_inc(v_w_2369_);
lean_dec(v_value_2215_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2398_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(32u);
v___x_2375_ = lean_nat_dec_eq(v_w_2369_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_dec(v_bv_2370_);
lean_dec_ref(v_arg_2351_);
v___x_2376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35);
v___x_2377_ = l_Nat_reprFast(v_w_2369_);
v___x_2378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___x_2379_ = l_Lean_MessageData_ofFormat(v___x_2378_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 7);
lean_ctor_set(v___x_2372_, 1, v___x_2379_);
lean_ctor_set(v___x_2372_, 0, v___x_2376_);
v___x_2381_ = v___x_2372_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2383_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2384_;
}
}
else
{
size_t v___x_2386_; lean_object* v___x_2387_; lean_object* v_r_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec(v_w_2369_);
v___x_2386_ = lean_usize_of_nat(v_bv_2370_);
lean_dec(v_bv_2370_);
v___x_2387_ = lean_usize_to_nat(v___x_2386_);
v_r_2388_ = l_Lean_mkRawNatLit(v___x_2387_);
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2388_);
v___x_2392_ = l_Lean_Expr_app___override(v___x_2391_, v_r_2388_);
v___x_2393_ = l_Lean_mkApp3(v___x_2389_, v___x_2390_, v_r_2388_, v___x_2392_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v___x_2393_);
lean_ctor_set(v___x_2372_, 0, v_arg_2351_);
v___x_2395_ = v___x_2372_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_arg_2351_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
}
}
}
else
{
lean_object* v_w_2399_; lean_object* v_bv_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___x_2360_);
lean_dec_ref(v_var_2214_);
v_w_2399_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2400_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2402_ = v_value_2215_;
v_isShared_2403_ = v_isSharedCheck_2428_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_bv_2400_);
lean_inc(v_w_2399_);
lean_dec(v_value_2215_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2428_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = lean_unsigned_to_nat(64u);
v___x_2405_ = lean_nat_dec_eq(v_w_2399_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_dec(v_bv_2400_);
lean_dec_ref(v_arg_2351_);
v___x_2406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49);
v___x_2407_ = l_Nat_reprFast(v_w_2399_);
v___x_2408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = l_Lean_MessageData_ofFormat(v___x_2408_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set_tag(v___x_2402_, 7);
lean_ctor_set(v___x_2402_, 1, v___x_2409_);
lean_ctor_set(v___x_2402_, 0, v___x_2406_);
v___x_2411_ = v___x_2402_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2413_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2414_;
}
}
else
{
size_t v___x_2416_; lean_object* v___x_2417_; lean_object* v_r_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec(v_w_2399_);
v___x_2416_ = lean_usize_of_nat(v_bv_2400_);
lean_dec(v_bv_2400_);
v___x_2417_ = lean_usize_to_nat(v___x_2416_);
v_r_2418_ = l_Lean_mkRawNatLit(v___x_2417_);
v___x_2419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2418_);
v___x_2422_ = l_Lean_Expr_app___override(v___x_2421_, v_r_2418_);
v___x_2423_ = l_Lean_mkApp3(v___x_2419_, v___x_2420_, v_r_2418_, v___x_2422_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v___x_2423_);
lean_ctor_set(v___x_2402_, 0, v_arg_2351_);
v___x_2425_ = v___x_2402_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_arg_2351_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
}
}
}
else
{
lean_object* v_w_2429_; lean_object* v_bv_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___x_2360_);
lean_dec_ref(v_var_2214_);
v_w_2429_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2430_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2432_ = v_value_2215_;
v_isShared_2433_ = v_isSharedCheck_2461_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_bv_2430_);
lean_inc(v_w_2429_);
lean_dec(v_value_2215_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2461_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = lean_unsigned_to_nat(32u);
v___x_2435_ = lean_nat_dec_eq(v_w_2429_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_dec(v_bv_2430_);
lean_dec_ref(v_arg_2351_);
v___x_2436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51);
v___x_2437_ = l_Nat_reprFast(v_w_2429_);
v___x_2438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
v___x_2439_ = l_Lean_MessageData_ofFormat(v___x_2438_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 7);
lean_ctor_set(v___x_2432_, 1, v___x_2439_);
lean_ctor_set(v___x_2432_, 0, v___x_2436_);
v___x_2441_ = v___x_2432_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2443_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2444_;
}
}
else
{
lean_object* v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; uint8_t v___x_2449_; 
lean_del_object(v___x_2432_);
v___x_2446_ = l_BitVec_toInt(v_w_2429_, v_bv_2430_);
lean_dec(v_w_2429_);
v___x_2447_ = lean_isize_of_int(v___x_2446_);
lean_dec(v___x_2446_);
v___x_2448_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2449_ = lean_isize_dec_le(v___x_2448_, v___x_2447_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2453_ = lean_isize_to_int(v___x_2447_);
v___x_2454_ = lean_int_neg(v___x_2453_);
lean_dec(v___x_2453_);
v___x_2455_ = l_Int_toNat(v___x_2454_);
lean_dec(v___x_2454_);
v___x_2456_ = l_Lean_instToExprISize_mkNat(v___x_2455_);
v___x_2457_ = l_Lean_mkApp3(v___x_2450_, v___x_2451_, v___x_2452_, v___x_2456_);
v___y_2357_ = v___x_2457_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_isize_to_int(v___x_2447_);
v___x_2459_ = l_Int_toNat(v___x_2458_);
lean_dec(v___x_2458_);
v___x_2460_ = l_Lean_instToExprISize_mkNat(v___x_2459_);
v___y_2357_ = v___x_2460_;
goto v___jp_2356_;
}
}
}
}
}
else
{
lean_object* v_w_2462_; lean_object* v_bv_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v___x_2360_);
lean_dec_ref(v_var_2214_);
v_w_2462_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2463_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2465_ = v_value_2215_;
v_isShared_2466_ = v_isSharedCheck_2494_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_bv_2463_);
lean_inc(v_w_2462_);
lean_dec(v_value_2215_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2494_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = lean_unsigned_to_nat(64u);
v___x_2468_ = lean_nat_dec_eq(v_w_2462_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_bv_2463_);
lean_dec_ref(v_arg_2351_);
v___x_2469_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63);
v___x_2470_ = l_Nat_reprFast(v_w_2462_);
v___x_2471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
v___x_2472_ = l_Lean_MessageData_ofFormat(v___x_2471_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 7);
lean_ctor_set(v___x_2465_, 1, v___x_2472_);
lean_ctor_set(v___x_2465_, 0, v___x_2469_);
v___x_2474_ = v___x_2465_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2476_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2477_;
}
}
else
{
lean_object* v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; uint8_t v___x_2482_; 
lean_del_object(v___x_2465_);
v___x_2479_ = l_BitVec_toInt(v_w_2462_, v_bv_2463_);
lean_dec(v_w_2462_);
v___x_2480_ = lean_isize_of_int(v___x_2479_);
lean_dec(v___x_2479_);
v___x_2481_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2482_ = lean_isize_dec_le(v___x_2481_, v___x_2480_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2483_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2484_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2486_ = lean_isize_to_int(v___x_2480_);
v___x_2487_ = lean_int_neg(v___x_2486_);
lean_dec(v___x_2486_);
v___x_2488_ = l_Int_toNat(v___x_2487_);
lean_dec(v___x_2487_);
v___x_2489_ = l_Lean_instToExprISize_mkNat(v___x_2488_);
v___x_2490_ = l_Lean_mkApp3(v___x_2483_, v___x_2484_, v___x_2485_, v___x_2489_);
v___y_2353_ = v___x_2490_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_isize_to_int(v___x_2480_);
v___x_2492_ = l_Int_toNat(v___x_2491_);
lean_dec(v___x_2491_);
v___x_2493_ = l_Lean_instToExprISize_mkNat(v___x_2492_);
v___y_2353_ = v___x_2493_;
goto v___jp_2352_;
}
}
}
}
v___jp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_arg_2351_);
lean_ctor_set(v___x_2354_, 1, v___y_2353_);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
v___jp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_arg_2351_);
lean_ctor_set(v___x_2358_, 1, v___y_2357_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
else
{
lean_object* v_w_2495_; lean_object* v_bv_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2495_ = lean_ctor_get(v_value_2215_, 0);
lean_inc(v_w_2495_);
v_bv_2496_ = lean_ctor_get(v_value_2215_, 1);
lean_inc(v_bv_2496_);
lean_dec_ref(v_value_2215_);
v___x_2497_ = lean_unsigned_to_nat(1u);
v___x_2498_ = l_BitVec_ofNat(v_w_2495_, v___x_2497_);
lean_dec(v_w_2495_);
v___x_2499_ = lean_nat_dec_eq(v_bv_2496_, v___x_2498_);
lean_dec(v___x_2498_);
lean_dec(v_bv_2496_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67);
v___y_2328_ = v___x_2500_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70);
v___y_2328_ = v___x_2501_;
goto v___jp_2327_;
}
}
}
else
{
lean_object* v_w_2502_; lean_object* v_bv_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2502_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2503_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2505_ = v_value_2215_;
v_isShared_2506_ = v_isSharedCheck_2531_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_bv_2503_);
lean_inc(v_w_2502_);
lean_dec(v_value_2215_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2531_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = lean_unsigned_to_nat(8u);
v___x_2508_ = lean_nat_dec_eq(v_w_2502_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
lean_dec(v_bv_2503_);
lean_dec_ref(v_arg_2308_);
v___x_2509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72);
v___x_2510_ = l_Nat_reprFast(v_w_2502_);
v___x_2511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
v___x_2512_ = l_Lean_MessageData_ofFormat(v___x_2511_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 7);
lean_ctor_set(v___x_2505_, 1, v___x_2512_);
lean_ctor_set(v___x_2505_, 0, v___x_2509_);
v___x_2514_ = v___x_2505_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2516_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2517_;
}
}
else
{
uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v_r_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec(v_w_2502_);
v___x_2519_ = lean_uint8_of_nat_mk(v_bv_2503_);
v___x_2520_ = lean_uint8_to_nat(v___x_2519_);
v_r_2521_ = l_Lean_mkRawNatLit(v___x_2520_);
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74);
v___x_2524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76);
lean_inc_ref(v_r_2521_);
v___x_2525_ = l_Lean_Expr_app___override(v___x_2524_, v_r_2521_);
v___x_2526_ = l_Lean_mkApp3(v___x_2522_, v___x_2523_, v_r_2521_, v___x_2525_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v___x_2526_);
lean_ctor_set(v___x_2505_, 0, v_arg_2308_);
v___x_2528_ = v___x_2505_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_arg_2308_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
}
}
}
else
{
lean_object* v_w_2532_; lean_object* v_bv_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2532_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2533_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2535_ = v_value_2215_;
v_isShared_2536_ = v_isSharedCheck_2561_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_bv_2533_);
lean_inc(v_w_2532_);
lean_dec(v_value_2215_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2561_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = lean_unsigned_to_nat(16u);
v___x_2538_ = lean_nat_dec_eq(v_w_2532_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
lean_dec(v_bv_2533_);
lean_dec_ref(v_arg_2308_);
v___x_2539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78);
v___x_2540_ = l_Nat_reprFast(v_w_2532_);
v___x_2541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = l_Lean_MessageData_ofFormat(v___x_2541_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 7);
lean_ctor_set(v___x_2535_, 1, v___x_2542_);
lean_ctor_set(v___x_2535_, 0, v___x_2539_);
v___x_2544_ = v___x_2535_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2546_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2547_;
}
}
else
{
uint16_t v___x_2549_; lean_object* v___x_2550_; lean_object* v_r_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_dec(v_w_2532_);
v___x_2549_ = lean_uint16_of_nat_mk(v_bv_2533_);
v___x_2550_ = lean_uint16_to_nat(v___x_2549_);
v_r_2551_ = l_Lean_mkRawNatLit(v___x_2550_);
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80);
v___x_2554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82);
lean_inc_ref(v_r_2551_);
v___x_2555_ = l_Lean_Expr_app___override(v___x_2554_, v_r_2551_);
v___x_2556_ = l_Lean_mkApp3(v___x_2552_, v___x_2553_, v_r_2551_, v___x_2555_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v___x_2556_);
lean_ctor_set(v___x_2535_, 0, v_arg_2308_);
v___x_2558_ = v___x_2535_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_arg_2308_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
}
}
}
else
{
lean_object* v_w_2562_; lean_object* v_bv_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2562_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2563_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2565_ = v_value_2215_;
v_isShared_2566_ = v_isSharedCheck_2591_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_bv_2563_);
lean_inc(v_w_2562_);
lean_dec(v_value_2215_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2591_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_unsigned_to_nat(32u);
v___x_2568_ = lean_nat_dec_eq(v_w_2562_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_dec(v_bv_2563_);
lean_dec_ref(v_arg_2308_);
v___x_2569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84);
v___x_2570_ = l_Nat_reprFast(v_w_2562_);
v___x_2571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
v___x_2572_ = l_Lean_MessageData_ofFormat(v___x_2571_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 7);
lean_ctor_set(v___x_2565_, 1, v___x_2572_);
lean_ctor_set(v___x_2565_, 0, v___x_2569_);
v___x_2574_ = v___x_2565_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2576_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2577_;
}
}
else
{
uint32_t v___x_2579_; lean_object* v___x_2580_; lean_object* v_r_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_dec(v_w_2562_);
v___x_2579_ = lean_uint32_of_nat_mk(v_bv_2563_);
v___x_2580_ = lean_uint32_to_nat(v___x_2579_);
v_r_2581_ = l_Lean_mkRawNatLit(v___x_2580_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86);
v___x_2584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88);
lean_inc_ref(v_r_2581_);
v___x_2585_ = l_Lean_Expr_app___override(v___x_2584_, v_r_2581_);
v___x_2586_ = l_Lean_mkApp3(v___x_2582_, v___x_2583_, v_r_2581_, v___x_2585_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v___x_2586_);
lean_ctor_set(v___x_2565_, 0, v_arg_2308_);
v___x_2588_ = v___x_2565_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_arg_2308_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
}
}
}
}
else
{
lean_object* v_w_2592_; lean_object* v_bv_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2592_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2593_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2595_ = v_value_2215_;
v_isShared_2596_ = v_isSharedCheck_2621_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_bv_2593_);
lean_inc(v_w_2592_);
lean_dec(v_value_2215_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2621_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = lean_unsigned_to_nat(64u);
v___x_2598_ = lean_nat_dec_eq(v_w_2592_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_dec(v_bv_2593_);
lean_dec_ref(v_arg_2308_);
v___x_2599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90);
v___x_2600_ = l_Nat_reprFast(v_w_2592_);
v___x_2601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
v___x_2602_ = l_Lean_MessageData_ofFormat(v___x_2601_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 7);
lean_ctor_set(v___x_2595_, 1, v___x_2602_);
lean_ctor_set(v___x_2595_, 0, v___x_2599_);
v___x_2604_ = v___x_2595_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2606_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2607_;
}
}
else
{
uint64_t v___x_2609_; lean_object* v___x_2610_; lean_object* v_r_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec(v_w_2592_);
v___x_2609_ = lean_uint64_of_nat_mk(v_bv_2593_);
v___x_2610_ = lean_uint64_to_nat(v___x_2609_);
v_r_2611_ = l_Lean_mkRawNatLit(v___x_2610_);
v___x_2612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92);
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94);
lean_inc_ref(v_r_2611_);
v___x_2615_ = l_Lean_Expr_app___override(v___x_2614_, v_r_2611_);
v___x_2616_ = l_Lean_mkApp3(v___x_2612_, v___x_2613_, v_r_2611_, v___x_2615_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 1, v___x_2616_);
lean_ctor_set(v___x_2595_, 0, v_arg_2308_);
v___x_2618_ = v___x_2595_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_arg_2308_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
}
}
}
else
{
lean_object* v_w_2622_; lean_object* v_bv_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2622_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2623_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2625_ = v_value_2215_;
v_isShared_2626_ = v_isSharedCheck_2653_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_bv_2623_);
lean_inc(v_w_2622_);
lean_dec(v_value_2215_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2653_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_unsigned_to_nat(8u);
v___x_2628_ = lean_nat_dec_eq(v_w_2622_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_dec(v_bv_2623_);
lean_dec_ref(v_arg_2308_);
v___x_2629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96);
v___x_2630_ = l_Nat_reprFast(v_w_2622_);
v___x_2631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = l_Lean_MessageData_ofFormat(v___x_2631_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 7);
lean_ctor_set(v___x_2625_, 1, v___x_2632_);
lean_ctor_set(v___x_2625_, 0, v___x_2629_);
v___x_2634_ = v___x_2625_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2634_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2636_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2637_;
}
}
else
{
uint8_t v___x_2639_; uint8_t v___x_2640_; uint8_t v___x_2641_; 
lean_del_object(v___x_2625_);
lean_dec(v_w_2622_);
v___x_2639_ = lean_uint8_of_nat_mk(v_bv_2623_);
v___x_2640_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97);
v___x_2641_ = lean_int8_dec_le(v___x_2640_, v___x_2639_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99);
v___x_2644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101);
v___x_2645_ = lean_int8_to_int(v___x_2639_);
v___x_2646_ = lean_int_neg(v___x_2645_);
v___x_2647_ = l_Int_toNat(v___x_2646_);
lean_dec(v___x_2646_);
v___x_2648_ = l_Lean_instToExprInt8_mkNat(v___x_2647_);
v___x_2649_ = l_Lean_mkApp3(v___x_2642_, v___x_2643_, v___x_2644_, v___x_2648_);
v___y_2324_ = v___x_2649_;
goto v___jp_2323_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_int8_to_int(v___x_2639_);
v___x_2651_ = l_Int_toNat(v___x_2650_);
v___x_2652_ = l_Lean_instToExprInt8_mkNat(v___x_2651_);
v___y_2324_ = v___x_2652_;
goto v___jp_2323_;
}
}
}
}
}
else
{
lean_object* v_w_2654_; lean_object* v_bv_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2654_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2655_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2657_ = v_value_2215_;
v_isShared_2658_ = v_isSharedCheck_2685_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_bv_2655_);
lean_inc(v_w_2654_);
lean_dec(v_value_2215_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2685_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = lean_unsigned_to_nat(16u);
v___x_2660_ = lean_nat_dec_eq(v_w_2654_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
lean_dec(v_bv_2655_);
lean_dec_ref(v_arg_2308_);
v___x_2661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103);
v___x_2662_ = l_Nat_reprFast(v_w_2654_);
v___x_2663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
v___x_2664_ = l_Lean_MessageData_ofFormat(v___x_2663_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 7);
lean_ctor_set(v___x_2657_, 1, v___x_2664_);
lean_ctor_set(v___x_2657_, 0, v___x_2661_);
v___x_2666_ = v___x_2657_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2668_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2669_;
}
}
else
{
uint16_t v___x_2671_; uint16_t v___x_2672_; uint8_t v___x_2673_; 
lean_del_object(v___x_2657_);
lean_dec(v_w_2654_);
v___x_2671_ = lean_uint16_of_nat_mk(v_bv_2655_);
v___x_2672_ = lean_uint16_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104);
v___x_2673_ = lean_int16_dec_le(v___x_2672_, v___x_2671_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2674_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106);
v___x_2676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108);
v___x_2677_ = lean_int16_to_int(v___x_2671_);
v___x_2678_ = lean_int_neg(v___x_2677_);
v___x_2679_ = l_Int_toNat(v___x_2678_);
lean_dec(v___x_2678_);
v___x_2680_ = l_Lean_instToExprInt16_mkNat(v___x_2679_);
v___x_2681_ = l_Lean_mkApp3(v___x_2674_, v___x_2675_, v___x_2676_, v___x_2680_);
v___y_2320_ = v___x_2681_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_int16_to_int(v___x_2671_);
v___x_2683_ = l_Int_toNat(v___x_2682_);
v___x_2684_ = l_Lean_instToExprInt16_mkNat(v___x_2683_);
v___y_2320_ = v___x_2684_;
goto v___jp_2319_;
}
}
}
}
}
else
{
lean_object* v_w_2686_; lean_object* v_bv_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2686_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2687_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2689_ = v_value_2215_;
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_bv_2687_);
lean_inc(v_w_2686_);
lean_dec(v_value_2215_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2691_ = lean_unsigned_to_nat(32u);
v___x_2692_ = lean_nat_dec_eq(v_w_2686_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
lean_dec(v_bv_2687_);
lean_dec_ref(v_arg_2308_);
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110);
v___x_2694_ = l_Nat_reprFast(v_w_2686_);
v___x_2695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
v___x_2696_ = l_Lean_MessageData_ofFormat(v___x_2695_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 7);
lean_ctor_set(v___x_2689_, 1, v___x_2696_);
lean_ctor_set(v___x_2689_, 0, v___x_2693_);
v___x_2698_ = v___x_2689_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2700_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2701_;
}
}
else
{
uint32_t v___x_2703_; uint32_t v___x_2704_; uint8_t v___x_2705_; 
lean_del_object(v___x_2689_);
lean_dec(v_w_2686_);
v___x_2703_ = lean_uint32_of_nat_mk(v_bv_2687_);
v___x_2704_ = lean_uint32_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111);
v___x_2705_ = lean_int32_dec_le(v___x_2704_, v___x_2703_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113);
v___x_2708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115);
v___x_2709_ = lean_int32_to_int(v___x_2703_);
v___x_2710_ = lean_int_neg(v___x_2709_);
lean_dec(v___x_2709_);
v___x_2711_ = l_Int_toNat(v___x_2710_);
lean_dec(v___x_2710_);
v___x_2712_ = l_Lean_instToExprInt32_mkNat(v___x_2711_);
v___x_2713_ = l_Lean_mkApp3(v___x_2706_, v___x_2707_, v___x_2708_, v___x_2712_);
v___y_2316_ = v___x_2713_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = lean_int32_to_int(v___x_2703_);
v___x_2715_ = l_Int_toNat(v___x_2714_);
lean_dec(v___x_2714_);
v___x_2716_ = l_Lean_instToExprInt32_mkNat(v___x_2715_);
v___y_2316_ = v___x_2716_;
goto v___jp_2315_;
}
}
}
}
}
else
{
lean_object* v_w_2718_; lean_object* v_bv_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_var_2214_);
v_w_2718_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2719_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2721_ = v_value_2215_;
v_isShared_2722_ = v_isSharedCheck_2749_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_bv_2719_);
lean_inc(v_w_2718_);
lean_dec(v_value_2215_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2749_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = lean_unsigned_to_nat(64u);
v___x_2724_ = lean_nat_dec_eq(v_w_2718_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
lean_dec(v_bv_2719_);
lean_dec_ref(v_arg_2308_);
lean_del_object(v___x_2304_);
v___x_2725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117);
v___x_2726_ = l_Nat_reprFast(v_w_2718_);
v___x_2727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
v___x_2728_ = l_Lean_MessageData_ofFormat(v___x_2727_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 7);
lean_ctor_set(v___x_2721_, 1, v___x_2728_);
lean_ctor_set(v___x_2721_, 0, v___x_2725_);
v___x_2730_ = v___x_2721_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2732_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2733_;
}
}
else
{
uint64_t v___x_2735_; uint64_t v___x_2736_; uint8_t v___x_2737_; 
lean_del_object(v___x_2721_);
lean_dec(v_w_2718_);
v___x_2735_ = lean_uint64_of_nat_mk(v_bv_2719_);
v___x_2736_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118);
v___x_2737_ = lean_int64_dec_le(v___x_2736_, v___x_2735_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120);
v___x_2740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122);
v___x_2741_ = lean_int64_to_int_sint(v___x_2735_);
v___x_2742_ = lean_int_neg(v___x_2741_);
lean_dec(v___x_2741_);
v___x_2743_ = l_Int_toNat(v___x_2742_);
lean_dec(v___x_2742_);
v___x_2744_ = l_Lean_instToExprInt64_mkNat(v___x_2743_);
v___x_2745_ = l_Lean_mkApp3(v___x_2738_, v___x_2739_, v___x_2740_, v___x_2744_);
v___y_2310_ = v___x_2745_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_int64_to_int_sint(v___x_2735_);
v___x_2747_ = l_Int_toNat(v___x_2746_);
lean_dec(v___x_2746_);
v___x_2748_ = l_Lean_instToExprInt64_mkNat(v___x_2747_);
v___y_2310_ = v___x_2748_;
goto v___jp_2309_;
}
}
}
}
v___jp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_arg_2308_);
lean_ctor_set(v___x_2311_, 1, v___y_2310_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2311_);
v___x_2313_ = v___x_2304_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_arg_2308_);
lean_ctor_set(v___x_2317_, 1, v___y_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_arg_2308_);
lean_ctor_set(v___x_2321_, 1, v___y_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
v___jp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_arg_2308_);
lean_ctor_set(v___x_2325_, 1, v___y_2324_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
v___jp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_inc_ref(v___y_2328_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_arg_2308_);
lean_ctor_set(v___x_2329_, 1, v___y_2328_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_value_2215_);
lean_dec_ref(v_var_2214_);
v_a_2751_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2301_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2301_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
v___jp_2240_:
{
if (lean_obj_tag(v_var_2214_) == 5)
{
lean_object* v_fn_2247_; 
v_fn_2247_ = lean_ctor_get(v_var_2214_, 0);
if (lean_obj_tag(v_fn_2247_) == 4)
{
lean_object* v_declName_2248_; 
v_declName_2248_ = lean_ctor_get(v_fn_2247_, 0);
if (lean_obj_tag(v_declName_2248_) == 1)
{
lean_object* v_arg_2249_; lean_object* v_us_2250_; lean_object* v_pre_2251_; lean_object* v_str_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_arg_2249_ = lean_ctor_get(v_var_2214_, 1);
v_us_2250_ = lean_ctor_get(v_fn_2247_, 1);
v_pre_2251_ = lean_ctor_get(v_declName_2248_, 0);
v_str_2252_ = lean_ctor_get(v_declName_2248_, 1);
v___x_2253_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix;
v___x_2254_ = lean_string_dec_eq(v_str_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v_w_2255_; lean_object* v_bv_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2268_; 
v_w_2255_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2256_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2258_ = v_value_2215_;
v_isShared_2259_ = v_isSharedCheck_2268_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_bv_2256_);
lean_inc(v_w_2255_);
lean_dec(v_value_2215_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2268_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2261_ = l_Lean_mkNatLit(v_w_2255_);
v___x_2262_ = l_Lean_mkNatLit(v_bv_2256_);
v___x_2263_ = l_Lean_mkAppB(v___x_2260_, v___x_2261_, v___x_2262_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___x_2263_);
lean_ctor_set(v___x_2258_, 0, v_var_2214_);
v___x_2265_ = v___x_2258_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_var_2214_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
}
}
else
{
lean_object* v___x_2269_; 
lean_inc(v_pre_2251_);
lean_inc(v_us_2250_);
lean_inc_ref(v_arg_2249_);
lean_dec_ref_known(v_var_2214_, 2);
v___x_2269_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_pre_2251_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2292_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2292_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2292_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
if (lean_obj_tag(v_a_2270_) == 5)
{
lean_object* v_val_2274_; lean_object* v_ctors_2275_; lean_object* v_bv_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2288_; 
v_val_2274_ = lean_ctor_get(v_a_2270_, 0);
lean_inc_ref(v_val_2274_);
lean_dec_ref_known(v_a_2270_, 1);
v_ctors_2275_ = lean_ctor_get(v_val_2274_, 4);
lean_inc(v_ctors_2275_);
lean_dec_ref(v_val_2274_);
v_bv_2276_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v_value_2215_, 0);
lean_dec(v_unused_2289_);
v___x_2278_ = v_value_2215_;
v_isShared_2279_ = v_isSharedCheck_2288_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_bv_2276_);
lean_dec(v_value_2215_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2288_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2280_ = l_List_get_x21Internal___redArg(v___x_2239_, v_ctors_2275_, v_bv_2276_);
lean_dec(v_ctors_2275_);
v___x_2281_ = l_Lean_mkConst(v___x_2280_, v_us_2250_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 1, v___x_2281_);
lean_ctor_set(v___x_2278_, 0, v_arg_2249_);
v___x_2283_ = v___x_2278_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_arg_2249_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2285_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2283_);
v___x_2285_ = v___x_2272_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_del_object(v___x_2272_);
lean_dec(v_a_2270_);
lean_dec(v_us_2250_);
lean_dec_ref(v_arg_2249_);
lean_dec_ref(v_value_2215_);
v___x_2290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6);
v___x_2291_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v___x_2290_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2291_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_us_2250_);
lean_dec_ref(v_arg_2249_);
lean_dec_ref(v_value_2215_);
v_a_2293_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2269_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2269_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
else
{
goto v___jp_2223_;
}
}
else
{
goto v___jp_2223_;
}
}
else
{
goto v___jp_2223_;
}
}
}
else
{
lean_object* v_w_2759_; lean_object* v_bv_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2772_; 
v_w_2759_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2760_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2762_ = v_value_2215_;
v_isShared_2763_ = v_isSharedCheck_2772_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_bv_2760_);
lean_inc(v_w_2759_);
lean_dec(v_value_2215_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2772_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2765_ = l_Lean_mkNatLit(v_w_2759_);
v___x_2766_ = l_Lean_mkNatLit(v_bv_2760_);
v___x_2767_ = l_Lean_mkAppB(v___x_2764_, v___x_2765_, v___x_2766_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v___x_2767_);
lean_ctor_set(v___x_2762_, 0, v_var_2214_);
v___x_2769_ = v___x_2762_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_var_2214_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
return v___x_2770_;
}
}
}
v___jp_2223_:
{
lean_object* v_w_2224_; lean_object* v_bv_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2237_; 
v_w_2224_ = lean_ctor_get(v_value_2215_, 0);
v_bv_2225_ = lean_ctor_get(v_value_2215_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_value_2215_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2227_ = v_value_2215_;
v_isShared_2228_ = v_isSharedCheck_2237_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_bv_2225_);
lean_inc(v_w_2224_);
lean_dec(v_value_2215_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2237_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2230_ = l_Lean_mkNatLit(v_w_2224_);
v___x_2231_ = l_Lean_mkNatLit(v_bv_2225_);
v___x_2232_ = l_Lean_mkAppB(v___x_2229_, v___x_2230_, v___x_2231_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2232_);
lean_ctor_set(v___x_2227_, 0, v_var_2214_);
v___x_2234_ = v___x_2227_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_var_2214_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object* v_var_2773_, lean_object* v_value_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_2773_, v_value_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_object* v_00_u03b1_2783_, lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_2784_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_msg_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(v_00_u03b1_2793_, v_msg_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object* v_00_u03b1_2803_, lean_object* v_constName_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2813_, lean_object* v_constName_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(v_00_u03b1_2813_, v_constName_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2823_, lean_object* v_ref_2824_, lean_object* v_constName_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2824_, v_constName_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2834_, lean_object* v_ref_2835_, lean_object* v_constName_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(v_00_u03b1_2834_, v_ref_2835_, v_constName_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v_ref_2835_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_2845_, lean_object* v_ref_2846_, lean_object* v_msg_2847_, lean_object* v_declHint_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2846_, v_msg_2847_, v_declHint_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_ref_2858_, lean_object* v_msg_2859_, lean_object* v_declHint_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_2857_, v_ref_2858_, v_msg_2859_, v_declHint_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v_ref_2858_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_2869_, lean_object* v_declHint_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_2869_, v_declHint_2870_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2879_, lean_object* v_declHint_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_2879_, v_declHint_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2889_, lean_object* v_ref_2890_, lean_object* v_msg_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_2890_, v_msg_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2900_, lean_object* v_ref_2901_, lean_object* v_msg_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_2900_, v_ref_2901_, v_msg_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v_ref_2901_);
return v_res_2910_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object* v_a_2911_, lean_object* v_x_2912_){
_start:
{
if (lean_obj_tag(v_x_2912_) == 0)
{
uint8_t v___x_2913_; 
v___x_2913_ = 0;
return v___x_2913_;
}
else
{
lean_object* v_key_2914_; lean_object* v_tail_2915_; uint8_t v___x_2916_; 
v_key_2914_ = lean_ctor_get(v_x_2912_, 0);
v_tail_2915_ = lean_ctor_get(v_x_2912_, 2);
v___x_2916_ = lean_expr_eqv(v_key_2914_, v_a_2911_);
if (v___x_2916_ == 0)
{
v_x_2912_ = v_tail_2915_;
goto _start;
}
else
{
return v___x_2916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object* v_a_2918_, lean_object* v_x_2919_){
_start:
{
uint8_t v_res_2920_; lean_object* v_r_2921_; 
v_res_2920_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_2918_, v_x_2919_);
lean_dec(v_x_2919_);
lean_dec_ref(v_a_2918_);
v_r_2921_ = lean_box(v_res_2920_);
return v_r_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
if (lean_obj_tag(v_x_2923_) == 0)
{
return v_x_2922_;
}
else
{
lean_object* v_key_2924_; lean_object* v_value_2925_; lean_object* v_tail_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2949_; 
v_key_2924_ = lean_ctor_get(v_x_2923_, 0);
v_value_2925_ = lean_ctor_get(v_x_2923_, 1);
v_tail_2926_ = lean_ctor_get(v_x_2923_, 2);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_x_2923_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2928_ = v_x_2923_;
v_isShared_2929_ = v_isSharedCheck_2949_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_tail_2926_);
lean_inc(v_value_2925_);
lean_inc(v_key_2924_);
lean_dec(v_x_2923_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2949_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; uint64_t v___x_2931_; uint64_t v___x_2932_; uint64_t v___x_2933_; uint64_t v_fold_2934_; uint64_t v___x_2935_; uint64_t v___x_2936_; uint64_t v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; size_t v___x_2940_; size_t v___x_2941_; size_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2930_ = lean_array_get_size(v_x_2922_);
v___x_2931_ = l_Lean_Expr_hash(v_key_2924_);
v___x_2932_ = 32ULL;
v___x_2933_ = lean_uint64_shift_right(v___x_2931_, v___x_2932_);
v_fold_2934_ = lean_uint64_xor(v___x_2931_, v___x_2933_);
v___x_2935_ = 16ULL;
v___x_2936_ = lean_uint64_shift_right(v_fold_2934_, v___x_2935_);
v___x_2937_ = lean_uint64_xor(v_fold_2934_, v___x_2936_);
v___x_2938_ = lean_uint64_to_usize(v___x_2937_);
v___x_2939_ = lean_usize_of_nat(v___x_2930_);
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_sub(v___x_2939_, v___x_2940_);
v___x_2942_ = lean_usize_land(v___x_2938_, v___x_2941_);
v___x_2943_ = lean_array_uget_borrowed(v_x_2922_, v___x_2942_);
lean_inc(v___x_2943_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 2, v___x_2943_);
v___x_2945_ = v___x_2928_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_key_2924_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_value_2925_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_array_uset(v_x_2922_, v___x_2942_, v___x_2945_);
v_x_2922_ = v___x_2946_;
v_x_2923_ = v_tail_2926_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2950_, lean_object* v_source_2951_, lean_object* v_target_2952_){
_start:
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = lean_array_get_size(v_source_2951_);
v___x_2954_ = lean_nat_dec_lt(v_i_2950_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec_ref(v_source_2951_);
lean_dec(v_i_2950_);
return v_target_2952_;
}
else
{
lean_object* v_es_2955_; lean_object* v___x_2956_; lean_object* v_source_2957_; lean_object* v_target_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_es_2955_ = lean_array_fget(v_source_2951_, v_i_2950_);
v___x_2956_ = lean_box(0);
v_source_2957_ = lean_array_fset(v_source_2951_, v_i_2950_, v___x_2956_);
v_target_2958_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2952_, v_es_2955_);
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_add(v_i_2950_, v___x_2959_);
lean_dec(v_i_2950_);
v_i_2950_ = v___x_2960_;
v_source_2951_ = v_source_2957_;
v_target_2952_ = v_target_2958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(lean_object* v_data_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v_nbuckets_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2963_ = lean_array_get_size(v_data_2962_);
v___x_2964_ = lean_unsigned_to_nat(2u);
v_nbuckets_2965_ = lean_nat_mul(v___x_2963_, v___x_2964_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_mk_array(v_nbuckets_2965_, v___x_2967_);
v___x_2969_ = lean_array_propagate_mark(v_data_2962_, v___x_2968_);
v___x_2970_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(v___x_2966_, v_data_2962_, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object* v_m_2971_, lean_object* v_a_2972_, lean_object* v_b_2973_){
_start:
{
lean_object* v_size_2974_; lean_object* v_buckets_2975_; lean_object* v___x_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; uint64_t v___x_2979_; uint64_t v_fold_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; lean_object* v_bkt_2989_; uint8_t v___x_2990_; 
v_size_2974_ = lean_ctor_get(v_m_2971_, 0);
v_buckets_2975_ = lean_ctor_get(v_m_2971_, 1);
v___x_2976_ = lean_array_get_size(v_buckets_2975_);
v___x_2977_ = l_Lean_Expr_hash(v_a_2972_);
v___x_2978_ = 32ULL;
v___x_2979_ = lean_uint64_shift_right(v___x_2977_, v___x_2978_);
v_fold_2980_ = lean_uint64_xor(v___x_2977_, v___x_2979_);
v___x_2981_ = 16ULL;
v___x_2982_ = lean_uint64_shift_right(v_fold_2980_, v___x_2981_);
v___x_2983_ = lean_uint64_xor(v_fold_2980_, v___x_2982_);
v___x_2984_ = lean_uint64_to_usize(v___x_2983_);
v___x_2985_ = lean_usize_of_nat(v___x_2976_);
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = lean_usize_sub(v___x_2985_, v___x_2986_);
v___x_2988_ = lean_usize_land(v___x_2984_, v___x_2987_);
v_bkt_2989_ = lean_array_uget_borrowed(v_buckets_2975_, v___x_2988_);
v___x_2990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_2972_, v_bkt_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3011_; 
lean_inc_ref(v_buckets_2975_);
lean_inc(v_size_2974_);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_m_2971_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; lean_object* v_unused_3013_; 
v_unused_3012_ = lean_ctor_get(v_m_2971_, 1);
lean_dec(v_unused_3012_);
v_unused_3013_ = lean_ctor_get(v_m_2971_, 0);
lean_dec(v_unused_3013_);
v___x_2992_ = v_m_2971_;
v_isShared_2993_ = v_isSharedCheck_3011_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v_m_2971_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3011_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v_size_x27_2995_; lean_object* v___x_2996_; lean_object* v_buckets_x27_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_2994_ = lean_unsigned_to_nat(1u);
v_size_x27_2995_ = lean_nat_add(v_size_2974_, v___x_2994_);
lean_dec(v_size_2974_);
lean_inc(v_bkt_2989_);
v___x_2996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2996_, 0, v_a_2972_);
lean_ctor_set(v___x_2996_, 1, v_b_2973_);
lean_ctor_set(v___x_2996_, 2, v_bkt_2989_);
v_buckets_x27_2997_ = lean_array_uset(v_buckets_2975_, v___x_2988_, v___x_2996_);
v___x_2998_ = lean_unsigned_to_nat(4u);
v___x_2999_ = lean_nat_mul(v_size_x27_2995_, v___x_2998_);
v___x_3000_ = lean_unsigned_to_nat(3u);
v___x_3001_ = lean_nat_div(v___x_2999_, v___x_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_array_get_size(v_buckets_x27_2997_);
v___x_3003_ = lean_nat_dec_le(v___x_3001_, v___x_3002_);
lean_dec(v___x_3001_);
if (v___x_3003_ == 0)
{
lean_object* v_val_3004_; lean_object* v___x_3006_; 
v_val_3004_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(v_buckets_x27_2997_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v_val_3004_);
lean_ctor_set(v___x_2992_, 0, v_size_x27_2995_);
v___x_3006_ = v___x_2992_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_size_x27_2995_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_val_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
else
{
lean_object* v___x_3009_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v_buckets_x27_2997_);
lean_ctor_set(v___x_2992_, 0, v_size_x27_2995_);
v___x_3009_ = v___x_2992_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_size_x27_2995_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_buckets_x27_2997_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
else
{
lean_dec(v_b_2973_);
lean_dec_ref(v_a_2972_);
return v_m_2971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object* v_as_3014_, size_t v_sz_3015_, size_t v_i_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_a_3026_; uint8_t v___x_3030_; 
v___x_3030_ = lean_usize_dec_lt(v_i_3016_, v_sz_3015_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_b_3017_);
return v___x_3031_;
}
else
{
lean_object* v_a_3032_; lean_object* v_fst_3033_; lean_object* v_snd_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_a_3032_ = lean_array_uget_borrowed(v_as_3014_, v_i_3016_);
v_fst_3033_ = lean_ctor_get(v_a_3032_, 0);
v_snd_3034_ = lean_ctor_get(v_a_3032_, 1);
v___x_3035_ = lean_box(0);
lean_inc(v_snd_3034_);
lean_inc(v_fst_3033_);
v___x_3036_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_3033_, v_snd_3034_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v_fst_3038_; lean_object* v___x_3039_; lean_object* v_uninterpretedSymbols_3040_; lean_object* v_unusedRelevantHypotheses_3041_; lean_object* v_derivedEquations_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3066_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v___x_3036_, 1);
v_fst_3038_ = lean_ctor_get(v_a_3037_, 0);
lean_inc(v_fst_3038_);
v___x_3039_ = lean_st_ref_take(v___y_3019_);
v_uninterpretedSymbols_3040_ = lean_ctor_get(v___x_3039_, 0);
v_unusedRelevantHypotheses_3041_ = lean_ctor_get(v___x_3039_, 1);
v_derivedEquations_3042_ = lean_ctor_get(v___x_3039_, 2);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3044_ = v___x_3039_;
v_isShared_3045_ = v_isSharedCheck_3066_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_derivedEquations_3042_);
lean_inc(v_unusedRelevantHypotheses_3041_);
lean_inc(v_uninterpretedSymbols_3040_);
lean_dec(v___x_3039_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3066_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = lean_array_push(v_derivedEquations_3042_, v_a_3037_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 2, v___x_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_uninterpretedSymbols_3040_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_unusedRelevantHypotheses_3041_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_st_ref_put(v___y_3019_, v___x_3048_);
if (lean_obj_tag(v_fst_3038_) == 1)
{
lean_object* v_fvarId_3050_; lean_object* v___x_3051_; 
v_fvarId_3050_ = lean_ctor_get(v_fst_3038_, 0);
lean_inc(v_fvarId_3050_);
lean_dec_ref_known(v_fst_3038_, 1);
v___x_3051_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvarId_3050_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v_fvarId_3050_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref_known(v___x_3051_, 1);
v_a_3026_ = v___x_3035_;
goto v___jp_3025_;
}
else
{
return v___x_3051_;
}
}
else
{
lean_object* v___x_3052_; lean_object* v_uninterpretedSymbols_3053_; lean_object* v_unusedRelevantHypotheses_3054_; lean_object* v_derivedEquations_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3064_; 
v___x_3052_ = lean_st_ref_take(v___y_3019_);
v_uninterpretedSymbols_3053_ = lean_ctor_get(v___x_3052_, 0);
v_unusedRelevantHypotheses_3054_ = lean_ctor_get(v___x_3052_, 1);
v_derivedEquations_3055_ = lean_ctor_get(v___x_3052_, 2);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3057_ = v___x_3052_;
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_derivedEquations_3055_);
lean_inc(v_unusedRelevantHypotheses_3054_);
lean_inc(v_uninterpretedSymbols_3053_);
lean_dec(v___x_3052_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3064_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3059_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_uninterpretedSymbols_3053_, v_fst_3038_, v___x_3035_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_unusedRelevantHypotheses_3054_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_derivedEquations_3055_);
v___x_3061_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_st_ref_put(v___y_3019_, v___x_3061_);
v_a_3026_ = v___x_3035_;
goto v___jp_3025_;
}
}
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v_a_3067_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3036_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3036_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
v___jp_3025_:
{
size_t v___x_3027_; size_t v___x_3028_; 
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_add(v_i_3016_, v___x_3027_);
v_i_3016_ = v___x_3028_;
v_b_3017_ = v_a_3026_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___boxed(lean_object* v_as_3075_, lean_object* v_sz_3076_, lean_object* v_i_3077_, lean_object* v_b_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
size_t v_sz_boxed_3086_; size_t v_i_boxed_3087_; lean_object* v_res_3088_; 
v_sz_boxed_3086_ = lean_unbox_usize(v_sz_3076_);
lean_dec(v_sz_3076_);
v_i_boxed_3087_ = lean_unbox_usize(v_i_3077_);
lean_dec(v_i_3077_);
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_as_3075_, v_sz_boxed_3086_, v_i_boxed_3087_, v_b_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec_ref(v_as_3075_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_equations_3096_; lean_object* v___x_3097_; size_t v_sz_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v_equations_3096_ = lean_ctor_get(v_a_3089_, 2);
v___x_3097_ = lean_box(0);
v_sz_3098_ = lean_array_size(v_equations_3096_);
v___x_3099_ = ((size_t)0ULL);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_equations_3096_, v_sz_3098_, v___x_3099_, v___x_3097_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v___x_3100_, 0);
lean_dec(v_unused_3108_);
v___x_3102_ = v___x_3100_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_dec(v___x_3100_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3097_);
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3097_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object* v_00_u03b2_3117_, lean_object* v_m_3118_, lean_object* v_a_3119_, lean_object* v_b_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3118_, v_a_3119_, v_b_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object* v_00_u03b2_3122_, lean_object* v_a_3123_, lean_object* v_x_3124_){
_start:
{
uint8_t v___x_3125_; 
v___x_3125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3123_, v_x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3126_, lean_object* v_a_3127_, lean_object* v_x_3128_){
_start:
{
uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_res_3129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_3126_, v_a_3127_, v_x_3128_);
lean_dec(v_x_3128_);
lean_dec_ref(v_a_3127_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1(lean_object* v_00_u03b2_3131_, lean_object* v_data_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(v_data_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3134_, lean_object* v_i_3135_, lean_object* v_source_3136_, lean_object* v_target_3137_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(v_i_3135_, v_source_3136_, v_target_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(v_x_3140_, v_x_3141_);
return v___x_3142_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__0));
v___x_3145_ = l_Lean_stringToMessageData(v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg(lean_object* v_as_x27_3146_, lean_object* v_b_3147_){
_start:
{
if (lean_obj_tag(v_as_x27_3146_) == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_b_3147_);
return v___x_3148_;
}
else
{
lean_object* v_head_3149_; lean_object* v_tail_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_head_3149_ = lean_ctor_get(v_as_x27_3146_, 0);
v_tail_3150_ = lean_ctor_get(v_as_x27_3146_, 1);
v___x_3151_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1);
lean_inc(v_head_3149_);
v___x_3152_ = l_Lean_MessageData_ofExpr(v_head_3149_);
v___x_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_b_3147_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v_as_x27_3146_ = v_tail_3150_;
v_b_3147_ = v___x_3154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3156_, lean_object* v_b_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg(v_as_x27_3156_, v_b_3157_);
lean_dec(v_as_x27_3156_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object* v_x_3159_, lean_object* v_x_3160_){
_start:
{
if (lean_obj_tag(v_x_3160_) == 0)
{
lean_inc(v_x_3159_);
return v_x_3159_;
}
else
{
lean_object* v_key_3161_; lean_object* v_tail_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_key_3161_ = lean_ctor_get(v_x_3160_, 0);
v_tail_3162_ = lean_ctor_get(v_x_3160_, 2);
v___x_3163_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_x_3159_, v_tail_3162_);
lean_inc(v_key_3161_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_key_3161_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object* v_x_3165_, lean_object* v_x_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_x_3165_, v_x_3166_);
lean_dec(v_x_3166_);
lean_dec(v_x_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(lean_object* v_as_3168_, size_t v_i_3169_, size_t v_stop_3170_, lean_object* v_b_3171_){
_start:
{
uint8_t v___x_3172_; 
v___x_3172_ = lean_usize_dec_eq(v_i_3169_, v_stop_3170_);
if (v___x_3172_ == 0)
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3173_ = ((size_t)1ULL);
v___x_3174_ = lean_usize_sub(v_i_3169_, v___x_3173_);
v___x_3175_ = lean_array_uget_borrowed(v_as_3168_, v___x_3174_);
v___x_3176_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_b_3171_, v___x_3175_);
lean_dec(v_b_3171_);
v_i_3169_ = v___x_3174_;
v_b_3171_ = v___x_3176_;
goto _start;
}
else
{
return v_b_3171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2___boxed(lean_object* v_as_3178_, lean_object* v_i_3179_, lean_object* v_stop_3180_, lean_object* v_b_3181_){
_start:
{
size_t v_i_boxed_3182_; size_t v_stop_boxed_3183_; lean_object* v_res_3184_; 
v_i_boxed_3182_ = lean_unbox_usize(v_i_3179_);
lean_dec(v_i_3179_);
v_stop_boxed_3183_ = lean_unbox_usize(v_stop_3180_);
lean_dec(v_stop_3180_);
v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(v_as_3178_, v_i_boxed_3182_, v_stop_boxed_3183_, v_b_3181_);
lean_dec_ref(v_as_3178_);
return v_res_3184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object* v_d_3188_){
_start:
{
lean_object* v___y_3190_; lean_object* v_uninterpretedSymbols_3193_; lean_object* v_size_3194_; lean_object* v_buckets_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_uninterpretedSymbols_3193_ = lean_ctor_get(v_d_3188_, 0);
v_size_3194_ = lean_ctor_get(v_uninterpretedSymbols_3193_, 0);
v_buckets_3195_ = lean_ctor_get(v_uninterpretedSymbols_3193_, 1);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_nat_dec_eq(v_size_3194_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_array_get_size(v_buckets_3195_);
v___x_3200_ = lean_nat_dec_lt(v___x_3196_, v___x_3199_);
if (v___x_3200_ == 0)
{
v___y_3190_ = v___x_3198_;
goto v___jp_3189_;
}
else
{
size_t v___x_3201_; size_t v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_usize_of_nat(v___x_3199_);
v___x_3202_ = ((size_t)0ULL);
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(v_buckets_3195_, v___x_3201_, v___x_3202_, v___x_3198_);
v___y_3190_ = v___x_3203_;
goto v___jp_3189_;
}
}
else
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_box(0);
return v___x_3204_;
}
v___jp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
v___x_3192_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg(v___y_3190_, v___x_3191_);
lean_dec(v___y_3190_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object* v_d_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_3205_);
lean_dec_ref(v_d_3205_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object* v_as_3207_, lean_object* v_as_x27_3208_, lean_object* v_b_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg(v_as_x27_3208_, v_b_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object* v_as_3212_, lean_object* v_as_x27_3213_, lean_object* v_b_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_as_3212_, v_as_x27_3213_, v_b_3214_, v_a_3215_);
lean_dec(v_as_x27_3213_);
lean_dec(v_as_3212_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3218_) == 0)
{
lean_inc(v_x_3217_);
return v_x_3217_;
}
else
{
lean_object* v_key_3219_; lean_object* v_tail_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_key_3219_ = lean_ctor_get(v_x_3218_, 0);
v_tail_3220_ = lean_ctor_get(v_x_3218_, 2);
v___x_3221_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3217_, v_tail_3220_);
lean_inc(v_key_3219_);
v___x_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3222_, 0, v_key_3219_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3223_, v_x_3224_);
lean_dec(v_x_3224_);
lean_dec(v_x_3223_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object* v_as_3226_, size_t v_i_3227_, size_t v_stop_3228_, lean_object* v_b_3229_){
_start:
{
uint8_t v___x_3230_; 
v___x_3230_ = lean_usize_dec_eq(v_i_3227_, v_stop_3228_);
if (v___x_3230_ == 0)
{
size_t v___x_3231_; size_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3231_ = ((size_t)1ULL);
v___x_3232_ = lean_usize_sub(v_i_3227_, v___x_3231_);
v___x_3233_ = lean_array_uget_borrowed(v_as_3226_, v___x_3232_);
v___x_3234_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_b_3229_, v___x_3233_);
lean_dec(v_b_3229_);
v_i_3227_ = v___x_3232_;
v_b_3229_ = v___x_3234_;
goto _start;
}
else
{
return v_b_3229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object* v_as_3236_, lean_object* v_i_3237_, lean_object* v_stop_3238_, lean_object* v_b_3239_){
_start:
{
size_t v_i_boxed_3240_; size_t v_stop_boxed_3241_; lean_object* v_res_3242_; 
v_i_boxed_3240_ = lean_unbox_usize(v_i_3237_);
lean_dec(v_i_3237_);
v_stop_boxed_3241_ = lean_unbox_usize(v_stop_3238_);
lean_dec(v_stop_3238_);
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_3236_, v_i_boxed_3240_, v_stop_boxed_3241_, v_b_3239_);
lean_dec_ref(v_as_3236_);
return v_res_3242_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0));
v___x_3245_ = l_Lean_stringToMessageData(v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(lean_object* v_as_x27_3246_, lean_object* v_b_3247_){
_start:
{
if (lean_obj_tag(v_as_x27_3246_) == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_b_3247_);
return v___x_3248_;
}
else
{
lean_object* v_head_3249_; lean_object* v_tail_3250_; lean_object* v_type_3251_; lean_object* v_source_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_head_3249_ = lean_ctor_get(v_as_x27_3246_, 0);
v_tail_3250_ = lean_ctor_get(v_as_x27_3246_, 1);
v_type_3251_ = lean_ctor_get(v_head_3249_, 1);
v_source_3252_ = lean_ctor_get(v_head_3249_, 3);
v___x_3253_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___redArg___closed__1);
lean_inc_ref(v_type_3251_);
v___x_3254_ = l_Lean_MessageData_ofExpr(v_type_3251_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
lean_inc(v_source_3252_);
v___x_3258_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v_source_3252_);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v_b_3247_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v_as_x27_3246_ = v_tail_3250_;
v_b_3247_ = v___x_3260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3262_, lean_object* v_b_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3262_, v_b_3263_);
lean_dec(v_as_x27_3262_);
return v_res_3264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0));
v___x_3267_ = l_Lean_stringToMessageData(v___x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object* v_d_3268_){
_start:
{
lean_object* v___y_3270_; lean_object* v_unusedRelevantHypotheses_3273_; lean_object* v_size_3274_; lean_object* v_buckets_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v_unusedRelevantHypotheses_3273_ = lean_ctor_get(v_d_3268_, 1);
v_size_3274_ = lean_ctor_get(v_unusedRelevantHypotheses_3273_, 0);
v_buckets_3275_ = lean_ctor_get(v_unusedRelevantHypotheses_3273_, 1);
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_nat_dec_eq(v_size_3274_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_array_get_size(v_buckets_3275_);
v___x_3280_ = lean_nat_dec_lt(v___x_3276_, v___x_3279_);
if (v___x_3280_ == 0)
{
v___y_3270_ = v___x_3278_;
goto v___jp_3269_;
}
else
{
size_t v___x_3281_; size_t v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_usize_of_nat(v___x_3279_);
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_buckets_3275_, v___x_3281_, v___x_3282_, v___x_3278_);
v___y_3270_ = v___x_3283_;
goto v___jp_3269_;
}
}
else
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_box(0);
return v___x_3284_;
}
v___jp_3269_:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
v___x_3272_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v___y_3270_, v___x_3271_);
lean_dec(v___y_3270_);
return v___x_3272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object* v_d_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_3285_);
lean_dec_ref(v_d_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object* v_as_3287_, lean_object* v_as_x27_3288_, lean_object* v_b_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3288_, v_b_3289_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object* v_as_3292_, lean_object* v_as_x27_3293_, lean_object* v_b_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_as_3292_, v_as_x27_3293_, v_b_3294_, v_a_3295_);
lean_dec(v_as_x27_3293_);
lean_dec(v_as_3292_);
return v_res_3296_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0));
v___x_3308_ = l_Lean_stringToMessageData(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object* v_as_3312_, size_t v_i_3313_, size_t v_stop_3314_, lean_object* v_b_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_usize_dec_eq(v_i_3313_, v_stop_3314_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; size_t v___x_3323_; size_t v___x_3324_; 
v___x_3317_ = lean_array_uget_borrowed(v_as_3312_, v_i_3313_);
v___x_3318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v_b_3315_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
lean_inc(v___x_3317_);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v___x_3317_);
v___x_3321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = ((size_t)1ULL);
v___x_3324_ = lean_usize_add(v_i_3313_, v___x_3323_);
v_i_3313_ = v___x_3324_;
v_b_3315_ = v___x_3322_;
goto _start;
}
else
{
return v_b_3315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object* v_as_3326_, lean_object* v_i_3327_, lean_object* v_stop_3328_, lean_object* v_b_3329_){
_start:
{
size_t v_i_boxed_3330_; size_t v_stop_boxed_3331_; lean_object* v_res_3332_; 
v_i_boxed_3330_ = lean_unbox_usize(v_i_3327_);
lean_dec(v_i_3327_);
v_stop_boxed_3331_ = lean_unbox_usize(v_stop_3328_);
lean_dec(v_stop_3328_);
v_res_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_3326_, v_i_boxed_3330_, v_stop_boxed_3331_, v_b_3329_);
lean_dec_ref(v_as_3326_);
return v_res_3332_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object* v_as_3336_, size_t v_i_3337_, size_t v_stop_3338_, lean_object* v_b_3339_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_eq(v_i_3337_, v_stop_3338_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3360_; 
v___x_3341_ = lean_array_uget(v_as_3336_, v_i_3337_);
v_fst_3342_ = lean_ctor_get(v___x_3341_, 0);
v_snd_3343_ = lean_ctor_get(v___x_3341_, 1);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3345_ = v___x_3341_;
v_isShared_3346_ = v_isSharedCheck_3360_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3343_);
lean_inc(v_fst_3342_);
lean_dec(v___x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3360_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3347_ = l_Lean_MessageData_ofExpr(v_fst_3342_);
v___x_3348_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 7);
lean_ctor_set(v___x_3345_, 1, v___x_3348_);
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3350_ = v___x_3345_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; size_t v___x_3356_; size_t v___x_3357_; 
v___x_3351_ = l_Lean_MessageData_ofExpr(v_snd_3343_);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_b_3339_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = ((size_t)1ULL);
v___x_3357_ = lean_usize_add(v_i_3337_, v___x_3356_);
v_i_3337_ = v___x_3357_;
v_b_3339_ = v___x_3355_;
goto _start;
}
}
}
else
{
return v_b_3339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object* v_as_3361_, lean_object* v_i_3362_, lean_object* v_stop_3363_, lean_object* v_b_3364_){
_start:
{
size_t v_i_boxed_3365_; size_t v_stop_boxed_3366_; lean_object* v_res_3367_; 
v_i_boxed_3365_ = lean_unbox_usize(v_i_3362_);
lean_dec(v_i_3362_);
v_stop_boxed_3366_ = lean_unbox_usize(v_stop_3363_);
lean_dec(v_stop_3363_);
v_res_3367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_3361_, v_i_boxed_3365_, v_stop_boxed_3366_, v_b_3364_);
lean_dec_ref(v_as_3361_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object* v_a_3368_, lean_object* v_x_3369_, lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 0)
{
lean_dec_ref(v_a_3368_);
return v_x_3369_;
}
else
{
lean_object* v_head_3371_; lean_object* v_tail_3372_; lean_object* v___x_3373_; 
v_head_3371_ = lean_ctor_get(v_x_3370_, 0);
lean_inc(v_head_3371_);
v_tail_3372_ = lean_ctor_get(v_x_3370_, 1);
lean_inc(v_tail_3372_);
lean_dec_ref_known(v_x_3370_, 2);
lean_inc_ref(v_a_3368_);
v___x_3373_ = lean_apply_1(v_head_3371_, v_a_3368_);
if (lean_obj_tag(v___x_3373_) == 1)
{
lean_object* v_val_3374_; lean_object* v___x_3375_; 
v_val_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v___x_3375_ = lean_array_push(v_x_3369_, v_val_3374_);
v_x_3369_ = v___x_3375_;
v_x_3370_ = v_tail_3372_;
goto _start;
}
else
{
lean_dec(v___x_3373_);
v_x_3370_ = v_tail_3372_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4);
v___x_3387_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___x_3386_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8));
v___x_3394_ = l_Lean_stringToMessageData(v___x_3393_);
return v___x_3394_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9);
v___x_3396_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v___x_3395_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object* v_counterExample_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed), 7, 0);
v___x_3405_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_3404_, v_counterExample_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3457_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3457_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3457_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_err_3411_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v___x_3436_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0));
v___x_3437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers));
lean_inc(v_a_3406_);
v___x_3438_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3406_, v___x_3436_, v___x_3437_);
v___x_3439_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3440_ = lean_array_get_size(v___x_3438_);
v___x_3441_ = lean_nat_dec_eq(v___x_3440_, v___x_3435_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___y_3444_; uint8_t v___x_3448_; 
v___x_3442_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5);
v___x_3448_ = lean_nat_dec_lt(v___x_3435_, v___x_3440_);
if (v___x_3448_ == 0)
{
lean_dec_ref(v___x_3438_);
v___y_3444_ = v___x_3439_;
goto v___jp_3443_;
}
else
{
uint8_t v___x_3449_; 
v___x_3449_ = lean_nat_dec_le(v___x_3440_, v___x_3440_);
if (v___x_3449_ == 0)
{
if (v___x_3448_ == 0)
{
lean_dec_ref(v___x_3438_);
v___y_3444_ = v___x_3439_;
goto v___jp_3443_;
}
else
{
size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = lean_usize_of_nat(v___x_3440_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3438_, v___x_3450_, v___x_3451_, v___x_3439_);
lean_dec_ref(v___x_3438_);
v___y_3444_ = v___x_3452_;
goto v___jp_3443_;
}
}
else
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = lean_usize_of_nat(v___x_3440_);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3438_, v___x_3453_, v___x_3454_, v___x_3439_);
lean_dec_ref(v___x_3438_);
v___y_3444_ = v___x_3455_;
goto v___jp_3443_;
}
}
v___jp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3442_);
lean_ctor_set(v___x_3445_, 1, v___y_3444_);
v___x_3446_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v_err_3411_ = v___x_3447_;
goto v___jp_3410_;
}
}
else
{
lean_object* v___x_3456_; 
lean_dec_ref(v___x_3438_);
v___x_3456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10);
v_err_3411_ = v___x_3456_;
goto v___jp_3410_;
}
v___jp_3410_:
{
lean_object* v_derivedEquations_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_derivedEquations_3412_ = lean_ctor_get(v_a_3406_, 2);
lean_inc_ref(v_derivedEquations_3412_);
lean_dec(v_a_3406_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_array_get_size(v_derivedEquations_3412_);
v___x_3415_ = lean_nat_dec_lt(v___x_3413_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3417_; 
lean_dec_ref(v_derivedEquations_3412_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_err_3411_);
v___x_3417_ = v___x_3408_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_err_3411_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
else
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_nat_dec_le(v___x_3414_, v___x_3414_);
if (v___x_3419_ == 0)
{
if (v___x_3415_ == 0)
{
lean_object* v___x_3421_; 
lean_dec_ref(v_derivedEquations_3412_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_err_3411_);
v___x_3421_ = v___x_3408_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_err_3411_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
else
{
size_t v___x_3423_; size_t v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3423_ = ((size_t)0ULL);
v___x_3424_ = lean_usize_of_nat(v___x_3414_);
v___x_3425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3412_, v___x_3423_, v___x_3424_, v_err_3411_);
lean_dec_ref(v_derivedEquations_3412_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3425_);
v___x_3427_ = v___x_3408_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
else
{
size_t v___x_3429_; size_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = lean_usize_of_nat(v___x_3414_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3412_, v___x_3429_, v___x_3430_, v_err_3411_);
lean_dec_ref(v_derivedEquations_3412_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3431_);
v___x_3433_ = v___x_3408_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
v_a_3458_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3405_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3405_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object* v_counterExample_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
return v_res_3472_;
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

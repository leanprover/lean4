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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for USize was not 32 bit but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " bit"};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for USize was not 64 bit but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for ISize was not 32 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for ISize was not 64 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Value for UInt8 was not 8 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for UInt16 was not 16 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for UInt32 was not 32 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for UInt64 was not 64 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Value for Int8 was not 8 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for Int16 was not 16 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for Int32 was not 32 bit but "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for Int64 was not 64 bit but "};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "It abstracted the following unsupported expressions as opaque variables: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "The following potentially relevant hypotheses could not be used: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object*);
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
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_nbuckets_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = lean_array_get_size(v_data_420_);
v___x_422_ = lean_unsigned_to_nat(2u);
v_nbuckets_423_ = lean_nat_mul(v___x_421_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_box(0);
v___x_426_ = lean_mk_array(v_nbuckets_423_, v___x_425_);
v___x_427_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(v___x_424_, v_data_420_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(lean_object* v_m_428_, lean_object* v_a_429_, lean_object* v_b_430_){
_start:
{
lean_object* v_size_431_; lean_object* v_buckets_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_475_; 
v_size_431_ = lean_ctor_get(v_m_428_, 0);
v_buckets_432_ = lean_ctor_get(v_m_428_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_m_428_);
if (v_isSharedCheck_475_ == 0)
{
v___x_434_ = v_m_428_;
v_isShared_435_ = v_isSharedCheck_475_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_buckets_432_);
lean_inc(v_size_431_);
lean_dec(v_m_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_475_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v_fold_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v_bkt_449_; uint8_t v___x_450_; 
v___x_436_ = lean_array_get_size(v_buckets_432_);
v___x_437_ = lean_uint64_of_nat(v_a_429_);
v___x_438_ = 32ULL;
v___x_439_ = lean_uint64_shift_right(v___x_437_, v___x_438_);
v_fold_440_ = lean_uint64_xor(v___x_437_, v___x_439_);
v___x_441_ = 16ULL;
v___x_442_ = lean_uint64_shift_right(v_fold_440_, v___x_441_);
v___x_443_ = lean_uint64_xor(v_fold_440_, v___x_442_);
v___x_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = lean_usize_of_nat(v___x_436_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_sub(v___x_445_, v___x_446_);
v___x_448_ = lean_usize_land(v___x_444_, v___x_447_);
v_bkt_449_ = lean_array_uget_borrowed(v_buckets_432_, v___x_448_);
v___x_450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_429_, v_bkt_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v_size_x27_452_; lean_object* v___x_453_; lean_object* v_buckets_x27_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v_size_x27_452_ = lean_nat_add(v_size_431_, v___x_451_);
lean_dec(v_size_431_);
lean_inc(v_bkt_449_);
v___x_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_453_, 0, v_a_429_);
lean_ctor_set(v___x_453_, 1, v_b_430_);
lean_ctor_set(v___x_453_, 2, v_bkt_449_);
v_buckets_x27_454_ = lean_array_uset(v_buckets_432_, v___x_448_, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(4u);
v___x_456_ = lean_nat_mul(v_size_x27_452_, v___x_455_);
v___x_457_ = lean_unsigned_to_nat(3u);
v___x_458_ = lean_nat_div(v___x_456_, v___x_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_array_get_size(v_buckets_x27_454_);
v___x_460_ = lean_nat_dec_le(v___x_458_, v___x_459_);
lean_dec(v___x_458_);
if (v___x_460_ == 0)
{
lean_object* v_val_461_; lean_object* v___x_463_; 
v_val_461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(v_buckets_x27_454_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_val_461_);
lean_ctor_set(v___x_434_, 0, v_size_x27_452_);
v___x_463_ = v___x_434_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_size_x27_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_val_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_object* v___x_466_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_buckets_x27_454_);
lean_ctor_set(v___x_434_, 0, v_size_x27_452_);
v___x_466_ = v___x_434_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_size_x27_452_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_buckets_x27_454_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v___x_468_; lean_object* v_buckets_x27_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
lean_inc(v_bkt_449_);
v___x_468_ = lean_box(0);
v_buckets_x27_469_ = lean_array_uset(v_buckets_432_, v___x_448_, v___x_468_);
v___x_470_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_429_, v_b_430_, v_bkt_449_);
v___x_471_ = lean_array_uset(v_buckets_x27_469_, v___x_448_, v___x_470_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_471_);
v___x_473_ = v___x_434_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_size_431_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object* v_aigSize_476_, lean_object* v_assignment_477_, lean_object* v_as_478_, size_t v_sz_479_, size_t v_i_480_, lean_object* v_b_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_lt(v_i_480_, v_sz_479_);
if (v___x_482_ == 0)
{
return v_b_481_;
}
else
{
lean_object* v_a_483_; lean_object* v_fst_484_; lean_object* v_snd_485_; uint8_t v___y_487_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_a_483_ = lean_array_uget_borrowed(v_as_478_, v_i_480_);
v_fst_484_ = lean_ctor_get(v_a_483_, 0);
v_snd_485_ = lean_ctor_get(v_a_483_, 1);
v___x_498_ = lean_nat_add(v_snd_485_, v_aigSize_476_);
v___x_499_ = lean_array_get_size(v_assignment_477_);
v___x_500_ = lean_nat_dec_lt(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v___x_498_);
v___y_487_ = v___x_482_;
goto v___jp_486_;
}
else
{
lean_object* v___x_501_; lean_object* v_fst_502_; uint8_t v___x_503_; 
v___x_501_ = lean_array_fget_borrowed(v_assignment_477_, v___x_498_);
lean_dec(v___x_498_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
v___x_503_ = lean_unbox(v_fst_502_);
v___y_487_ = v___x_503_;
goto v___jp_486_;
}
v___jp_486_:
{
lean_object* v_var_488_; lean_object* v_idx_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; size_t v___x_495_; size_t v___x_496_; 
v_var_488_ = lean_ctor_get(v_fst_484_, 0);
v_idx_489_ = lean_ctor_get(v_fst_484_, 2);
v___x_490_ = lean_box(1);
v___x_491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_b_481_, v_var_488_, v___x_490_);
v___x_492_ = lean_box(v___y_487_);
lean_inc(v_idx_489_);
v___x_493_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_idx_489_, v___x_492_, v___x_491_);
lean_inc(v_var_488_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_b_481_, v_var_488_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_480_, v___x_495_);
v_i_480_ = v___x_496_;
v_b_481_ = v___x_494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object* v_aigSize_504_, lean_object* v_assignment_505_, lean_object* v_as_506_, lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_b_509_){
_start:
{
size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_sz_boxed_510_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_aigSize_504_, v_assignment_505_, v_as_506_, v_sz_boxed_510_, v_i_boxed_511_, v_b_509_);
lean_dec_ref(v_as_506_);
lean_dec_ref(v_assignment_505_);
lean_dec(v_aigSize_504_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
return v_x_513_;
}
else
{
lean_object* v_key_515_; lean_object* v_value_516_; lean_object* v_tail_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_key_515_ = lean_ctor_get(v_x_514_, 0);
v_value_516_ = lean_ctor_get(v_x_514_, 1);
v_tail_517_ = lean_ctor_get(v_x_514_, 2);
lean_inc(v_value_516_);
lean_inc(v_key_515_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_key_515_);
lean_ctor_set(v___x_518_, 1, v_value_516_);
v___x_519_ = lean_array_push(v_x_513_, v___x_518_);
v_x_513_ = v___x_519_;
v_x_514_ = v_tail_517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_x_521_, v_x_522_);
lean_dec(v_x_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object* v_as_524_, size_t v_i_525_, size_t v_stop_526_, lean_object* v_b_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_eq(v_i_525_, v_stop_526_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; size_t v___x_531_; size_t v___x_532_; 
v___x_529_ = lean_array_uget_borrowed(v_as_524_, v_i_525_);
v___x_530_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_b_527_, v___x_529_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_525_, v___x_531_);
v_i_525_ = v___x_532_;
v_b_527_ = v___x_530_;
goto _start;
}
else
{
return v_b_527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object* v_as_534_, lean_object* v_i_535_, lean_object* v_stop_536_, lean_object* v_b_537_){
_start:
{
size_t v_i_boxed_538_; size_t v_stop_boxed_539_; lean_object* v_res_540_; 
v_i_boxed_538_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_stop_boxed_539_ = lean_unbox_usize(v_stop_536_);
lean_dec(v_stop_536_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_as_534_, v_i_boxed_538_, v_stop_boxed_539_, v_b_537_);
lean_dec_ref(v_as_534_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
return v_x_541_;
}
else
{
lean_object* v_key_543_; lean_object* v_value_544_; lean_object* v_tail_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_key_543_ = lean_ctor_get(v_x_542_, 0);
v_value_544_ = lean_ctor_get(v_x_542_, 1);
v_tail_545_ = lean_ctor_get(v_x_542_, 2);
lean_inc(v_value_544_);
lean_inc(v_key_543_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_key_543_);
lean_ctor_set(v___x_546_, 1, v_value_544_);
v___x_547_ = lean_array_push(v_x_541_, v___x_546_);
v_x_541_ = v___x_547_;
v_x_542_ = v_tail_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___boxed(lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_x_549_, v_x_550_);
lean_dec(v_x_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(lean_object* v_as_552_, size_t v_i_553_, size_t v_stop_554_, lean_object* v_b_555_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_eq(v_i_553_, v_stop_554_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; 
v___x_557_ = lean_array_uget_borrowed(v_as_552_, v_i_553_);
v___x_558_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_b_555_, v___x_557_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_553_, v___x_559_);
v_i_553_ = v___x_560_;
v_b_555_ = v___x_558_;
goto _start;
}
else
{
return v_b_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13___boxed(lean_object* v_as_562_, lean_object* v_i_563_, lean_object* v_stop_564_, lean_object* v_b_565_){
_start:
{
size_t v_i_boxed_566_; size_t v_stop_boxed_567_; lean_object* v_res_568_; 
v_i_boxed_566_ = lean_unbox_usize(v_i_563_);
lean_dec(v_i_563_);
v_stop_boxed_567_ = lean_unbox_usize(v_stop_564_);
lean_dec(v_stop_564_);
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_as_562_, v_i_boxed_566_, v_stop_boxed_567_, v_b_565_);
lean_dec_ref(v_as_562_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(lean_object* v_as_569_, size_t v_i_570_, size_t v_stop_571_, lean_object* v_b_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_570_, v_stop_571_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; size_t v___x_577_; size_t v___x_578_; 
v___x_574_ = lean_array_uget_borrowed(v_as_569_, v_i_570_);
v___x_575_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_574_);
v___x_576_ = lean_nat_add(v_b_572_, v___x_575_);
lean_dec(v___x_575_);
lean_dec(v_b_572_);
v___x_577_ = ((size_t)1ULL);
v___x_578_ = lean_usize_add(v_i_570_, v___x_577_);
v_i_570_ = v___x_578_;
v_b_572_ = v___x_576_;
goto _start;
}
else
{
return v_b_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18___boxed(lean_object* v_as_580_, lean_object* v_i_581_, lean_object* v_stop_582_, lean_object* v_b_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_stop_boxed_585_; lean_object* v_res_586_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_581_);
lean_dec(v_i_581_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_582_);
lean_dec(v_stop_582_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_as_580_, v_i_boxed_584_, v_stop_boxed_585_, v_b_583_);
lean_dec_ref(v_as_580_);
return v_res_586_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = 0;
v___x_588_ = l_Lean_instInhabitedExpr;
v___x_589_ = lean_box(v___x_587_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(lean_object* v_msg_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_panic_fn_borrowed(v___x_594_, v_msg_591_);
lean_dec_ref_known(v___x_594_, 2);
return v___x_595_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_599_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2));
v___x_600_ = lean_unsigned_to_nat(11u);
v___x_601_ = lean_unsigned_to_nat(163u);
v___x_602_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1));
v___x_603_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0));
v___x_604_ = l_mkPanicMessageWithDecl(v___x_603_, v___x_602_, v___x_601_, v___x_600_, v___x_599_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object* v_a_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3);
v___x_608_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_key_609_; lean_object* v_value_610_; lean_object* v_tail_611_; uint8_t v___x_612_; 
v_key_609_ = lean_ctor_get(v_x_606_, 0);
v_value_610_ = lean_ctor_get(v_x_606_, 1);
v_tail_611_ = lean_ctor_get(v_x_606_, 2);
v___x_612_ = lean_nat_dec_eq(v_key_609_, v_a_605_);
if (v___x_612_ == 0)
{
v_x_606_ = v_tail_611_;
goto _start;
}
else
{
lean_inc(v_value_610_);
return v_value_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object* v_a_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_a_614_, v_x_615_);
lean_dec(v_x_615_);
lean_dec(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_buckets_619_; lean_object* v___x_620_; uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; uint64_t v_fold_624_; uint64_t v___x_625_; uint64_t v___x_626_; uint64_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_buckets_619_ = lean_ctor_get(v_m_617_, 1);
v___x_620_ = lean_array_get_size(v_buckets_619_);
v___x_621_ = lean_uint64_of_nat(v_a_618_);
v___x_622_ = 32ULL;
v___x_623_ = lean_uint64_shift_right(v___x_621_, v___x_622_);
v_fold_624_ = lean_uint64_xor(v___x_621_, v___x_623_);
v___x_625_ = 16ULL;
v___x_626_ = lean_uint64_shift_right(v_fold_624_, v___x_625_);
v___x_627_ = lean_uint64_xor(v_fold_624_, v___x_626_);
v___x_628_ = lean_uint64_to_usize(v___x_627_);
v___x_629_ = lean_usize_of_nat(v___x_620_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_sub(v___x_629_, v___x_630_);
v___x_632_ = lean_usize_land(v___x_628_, v___x_631_);
v___x_633_ = lean_array_uget_borrowed(v_buckets_619_, v___x_632_);
v___x_634_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_a_618_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object* v_m_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_m_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_m_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(lean_object* v_atomsAssignment_638_, lean_object* v_acc_639_, lean_object* v_a_640_){
_start:
{
if (lean_obj_tag(v_a_640_) == 0)
{
return v_acc_639_;
}
else
{
lean_object* v_key_641_; lean_object* v_value_642_; lean_object* v_tail_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_key_641_ = lean_ctor_get(v_a_640_, 0);
v_value_642_ = lean_ctor_get(v_a_640_, 1);
v_tail_643_ = lean_ctor_get(v_a_640_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_640_);
if (v_isSharedCheck_657_ == 0)
{
v___x_645_ = v_a_640_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_tail_643_);
lean_inc(v_value_642_);
lean_inc(v_key_641_);
lean_dec(v_a_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_var_647_; lean_object* v___x_648_; lean_object* v_snd_649_; lean_object* v_snd_650_; uint8_t v___x_651_; 
v_var_647_ = lean_ctor_get(v_key_641_, 0);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_638_, v_var_647_);
v_snd_649_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_snd_649_);
lean_dec_ref(v___x_648_);
v_snd_650_ = lean_ctor_get(v_snd_649_, 1);
lean_inc(v_snd_650_);
lean_dec(v_snd_649_);
v___x_651_ = lean_unbox(v_snd_650_);
lean_dec(v_snd_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 2, v_acc_639_);
v___x_653_ = v___x_645_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_key_641_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_value_642_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_acc_639_);
v___x_653_ = v_reuseFailAlloc_655_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v_acc_639_ = v___x_653_;
v_a_640_ = v_tail_643_;
goto _start;
}
}
else
{
lean_del_object(v___x_645_);
lean_dec(v_value_642_);
lean_dec(v_key_641_);
v_a_640_ = v_tail_643_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16___boxed(lean_object* v_atomsAssignment_658_, lean_object* v_acc_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(v_atomsAssignment_658_, v_acc_659_, v_a_660_);
lean_dec_ref(v_atomsAssignment_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(lean_object* v_atomsAssignment_662_, size_t v_sz_663_, size_t v_i_664_, lean_object* v_bs_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_lt(v_i_664_, v_sz_663_);
if (v___x_666_ == 0)
{
return v_bs_665_;
}
else
{
lean_object* v_v_667_; lean_object* v___x_668_; lean_object* v_bs_x27_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v_v_667_ = lean_array_uget(v_bs_665_, v_i_664_);
v___x_668_ = lean_unsigned_to_nat(0u);
v_bs_x27_669_ = lean_array_uset(v_bs_665_, v_i_664_, v___x_668_);
v___x_670_ = lean_box(0);
v___x_671_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(v_atomsAssignment_662_, v___x_670_, v_v_667_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_664_, v___x_672_);
v___x_674_ = lean_array_uset(v_bs_x27_669_, v_i_664_, v___x_671_);
v_i_664_ = v___x_673_;
v_bs_665_ = v___x_674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17___boxed(lean_object* v_atomsAssignment_676_, lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_bs_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_atomsAssignment_676_, v_sz_boxed_680_, v_i_boxed_681_, v_bs_679_);
lean_dec_ref(v_atomsAssignment_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object* v_atomsAssignment_683_, lean_object* v_m_684_){
_start:
{
lean_object* v_buckets_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_712_; 
v_buckets_685_ = lean_ctor_get(v_m_684_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_m_684_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v_m_684_, 0);
lean_dec(v_unused_713_);
v___x_687_ = v_m_684_;
v_isShared_688_ = v_isSharedCheck_712_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_buckets_685_);
lean_dec(v_m_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_712_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
size_t v_sz_689_; size_t v___x_690_; lean_object* v_newBuckets_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_sz_689_ = lean_array_size(v_buckets_685_);
v___x_690_ = ((size_t)0ULL);
v_newBuckets_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_atomsAssignment_683_, v_sz_689_, v___x_690_, v_buckets_685_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_array_get_size(v_newBuckets_691_);
v___x_694_ = lean_nat_dec_lt(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_696_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_newBuckets_691_);
lean_ctor_set(v___x_687_, 0, v___x_692_);
v___x_696_ = v___x_687_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_newBuckets_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_le(v___x_693_, v___x_693_);
if (v___x_698_ == 0)
{
if (v___x_694_ == 0)
{
lean_object* v___x_700_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_newBuckets_691_);
lean_ctor_set(v___x_687_, 0, v___x_692_);
v___x_700_ = v___x_687_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_newBuckets_691_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
size_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_usize_of_nat(v___x_693_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_newBuckets_691_, v___x_690_, v___x_702_, v___x_692_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_newBuckets_691_);
lean_ctor_set(v___x_687_, 0, v___x_703_);
v___x_705_ = v___x_687_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_newBuckets_691_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = lean_usize_of_nat(v___x_693_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_newBuckets_691_, v___x_690_, v___x_707_, v___x_692_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_newBuckets_691_);
lean_ctor_set(v___x_687_, 0, v___x_708_);
v___x_710_ = v___x_687_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_newBuckets_691_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object* v_atomsAssignment_714_, lean_object* v_m_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_atomsAssignment_714_, v_m_715_);
lean_dec_ref(v_atomsAssignment_714_);
return v_res_716_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_720_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2));
v___x_721_ = lean_unsigned_to_nat(6u);
v___x_722_ = lean_unsigned_to_nat(69u);
v___x_723_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1));
v___x_724_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0));
v___x_725_ = l_mkPanicMessageWithDecl(v___x_724_, v___x_723_, v___x_722_, v___x_721_, v___x_720_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object* v_as_x27_726_, lean_object* v_b_727_){
_start:
{
if (lean_obj_tag(v_as_x27_726_) == 0)
{
return v_b_727_;
}
else
{
lean_object* v_head_728_; lean_object* v_tail_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_755_; 
v_head_728_ = lean_ctor_get(v_as_x27_726_, 0);
v_tail_729_ = lean_ctor_get(v_as_x27_726_, 1);
v_fst_730_ = lean_ctor_get(v_head_728_, 0);
v_snd_731_ = lean_ctor_get(v_head_728_, 1);
v_fst_732_ = lean_ctor_get(v_b_727_, 0);
v_snd_733_ = lean_ctor_get(v_b_727_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_b_727_);
if (v_isSharedCheck_755_ == 0)
{
v___x_735_ = v_b_727_;
v_isShared_736_ = v_isSharedCheck_755_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v_b_727_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_755_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_value_738_; uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_eq(v_fst_730_, v_snd_733_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_735_);
lean_dec(v_snd_733_);
lean_dec(v_fst_732_);
v___x_746_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3);
v___x_747_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(v___x_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
return v_a_748_;
}
else
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_747_, 1);
v_as_x27_726_ = v_tail_729_;
v_b_727_ = v_a_749_;
goto _start;
}
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_unbox(v_snd_731_);
if (v___x_751_ == 0)
{
v_value_738_ = v_fst_732_;
goto v___jp_737_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_shiftl(v___x_752_, v_snd_733_);
v___x_754_ = lean_nat_lor(v_fst_732_, v___x_753_);
lean_dec(v___x_753_);
lean_dec(v_fst_732_);
v_value_738_ = v___x_754_;
goto v___jp_737_;
}
}
v___jp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_snd_733_, v___x_739_);
lean_dec(v_snd_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_740_);
lean_ctor_set(v___x_735_, 0, v_value_738_);
v___x_742_ = v___x_735_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_value_738_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_744_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v_as_x27_726_ = v_tail_729_;
v_b_727_ = v___x_742_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___boxed(lean_object* v_as_x27_756_, lean_object* v_b_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_756_, v_b_757_);
lean_dec(v_as_x27_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object* v_init_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_k_761_; lean_object* v_v_762_; lean_object* v_l_763_; lean_object* v_r_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_k_761_ = lean_ctor_get(v_x_760_, 1);
v_v_762_ = lean_ctor_get(v_x_760_, 2);
v_l_763_ = lean_ctor_get(v_x_760_, 3);
v_r_764_ = lean_ctor_get(v_x_760_, 4);
v___x_765_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_759_, v_r_764_);
lean_inc(v_v_762_);
lean_inc(v_k_761_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_k_761_);
lean_ctor_set(v___x_766_, 1, v_v_762_);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
v_init_759_ = v___x_767_;
v_x_760_ = v_l_763_;
goto _start;
}
else
{
return v_init_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___boxed(lean_object* v_init_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_769_, v_x_770_);
lean_dec(v_x_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object* v_atomsAssignment_774_, lean_object* v_as_775_, size_t v_sz_776_, size_t v_i_777_, lean_object* v_b_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_lt(v_i_777_, v_sz_776_);
if (v___x_779_ == 0)
{
return v_b_778_;
}
else
{
lean_object* v_a_780_; lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_snd_785_; lean_object* v_fst_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_810_; 
v_a_780_ = lean_array_uget_borrowed(v_as_775_, v_i_777_);
v_fst_781_ = lean_ctor_get(v_a_780_, 0);
v_snd_782_ = lean_ctor_get(v_a_780_, 1);
v___x_783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0));
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_774_, v_fst_781_);
v_snd_785_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_snd_785_);
lean_dec_ref(v___x_784_);
v_fst_786_ = lean_ctor_get(v_snd_785_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_snd_785_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_snd_785_, 1);
lean_dec(v_unused_811_);
v___x_788_ = v_snd_785_;
v_isShared_789_ = v_isSharedCheck_810_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_fst_786_);
lean_dec(v_snd_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_810_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_fst_793_; lean_object* v_snd_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_809_; 
v___x_790_ = lean_box(0);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v___x_790_, v_snd_782_);
v___x_792_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v___x_791_, v___x_783_);
lean_dec(v___x_791_);
v_fst_793_ = lean_ctor_get(v___x_792_, 0);
v_snd_794_ = lean_ctor_get(v___x_792_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_809_ == 0)
{
v___x_796_ = v___x_792_;
v_isShared_797_ = v_isSharedCheck_809_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snd_794_);
lean_inc(v_fst_793_);
lean_dec(v___x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_809_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_BitVec_ofNat(v_snd_794_, v_fst_793_);
lean_dec(v_fst_793_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_798_);
lean_ctor_set(v___x_788_, 0, v_snd_794_);
v___x_800_ = v___x_788_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_snd_794_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_808_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_800_);
lean_ctor_set(v___x_796_, 0, v_fst_786_);
v___x_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_fst_786_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_807_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; 
v___x_803_ = lean_array_push(v_b_778_, v___x_802_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_777_, v___x_804_);
v_i_777_ = v___x_805_;
v_b_778_ = v___x_803_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object* v_atomsAssignment_812_, lean_object* v_as_813_, lean_object* v_sz_814_, lean_object* v_i_815_, lean_object* v_b_816_){
_start:
{
size_t v_sz_boxed_817_; size_t v_i_boxed_818_; lean_object* v_res_819_; 
v_sz_boxed_817_ = lean_unbox_usize(v_sz_814_);
lean_dec(v_sz_814_);
v_i_boxed_818_ = lean_unbox_usize(v_i_815_);
lean_dec(v_i_815_);
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_812_, v_as_813_, v_sz_boxed_817_, v_i_boxed_818_, v_b_816_);
lean_dec_ref(v_as_813_);
lean_dec_ref(v_atomsAssignment_812_);
return v_res_819_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_box(0);
v___x_821_ = lean_unsigned_to_nat(16u);
v___x_822_ = lean_mk_array(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_sparseMap_825_; 
v___x_823_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0);
v___x_824_ = lean_unsigned_to_nat(0u);
v_sparseMap_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_sparseMap_825_, 0, v___x_824_);
lean_ctor_set(v_sparseMap_825_, 1, v___x_823_);
return v_sparseMap_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object* v_var2Cnf_828_, lean_object* v_assignment_829_, lean_object* v_aigSize_830_, lean_object* v_atomsAssignment_831_){
_start:
{
lean_object* v___y_833_; size_t v___y_834_; lean_object* v___y_835_; lean_object* v___x_838_; lean_object* v_size_839_; lean_object* v_buckets_840_; lean_object* v___x_841_; lean_object* v_sparseMap_842_; lean_object* v___y_844_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_atomsAssignment_831_, v_var2Cnf_828_);
v_size_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_size_839_);
v_buckets_840_ = lean_ctor_get(v___x_838_, 1);
lean_inc_ref(v_buckets_840_);
lean_dec_ref(v___x_838_);
v___x_841_ = lean_unsigned_to_nat(0u);
v_sparseMap_842_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1);
v___x_859_ = lean_mk_empty_array_with_capacity(v_size_839_);
lean_dec(v_size_839_);
v___x_860_ = lean_array_get_size(v_buckets_840_);
v___x_861_ = lean_nat_dec_lt(v___x_841_, v___x_860_);
if (v___x_861_ == 0)
{
lean_dec_ref(v_buckets_840_);
v___y_844_ = v___x_859_;
goto v___jp_843_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = lean_nat_dec_le(v___x_860_, v___x_860_);
if (v___x_862_ == 0)
{
if (v___x_861_ == 0)
{
lean_dec_ref(v_buckets_840_);
v___y_844_ = v___x_859_;
goto v___jp_843_;
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_860_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_buckets_840_, v___x_863_, v___x_864_, v___x_859_);
lean_dec_ref(v_buckets_840_);
v___y_844_ = v___x_865_;
goto v___jp_843_;
}
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_860_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_buckets_840_, v___x_866_, v___x_867_, v___x_859_);
lean_dec_ref(v_buckets_840_);
v___y_844_ = v___x_868_;
goto v___jp_843_;
}
}
v___jp_832_:
{
size_t v_sz_836_; lean_object* v___x_837_; 
v_sz_836_ = lean_array_size(v___y_835_);
lean_inc_ref(v___y_833_);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_831_, v___y_835_, v_sz_836_, v___y_834_, v___y_833_);
lean_dec_ref(v___y_835_);
return v___x_837_;
}
v___jp_843_:
{
size_t v_sz_845_; size_t v___x_846_; lean_object* v___x_847_; lean_object* v_size_848_; lean_object* v_buckets_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_sz_845_ = lean_array_size(v___y_844_);
v___x_846_ = ((size_t)0ULL);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_aigSize_830_, v_assignment_829_, v___y_844_, v_sz_845_, v___x_846_, v_sparseMap_842_);
lean_dec_ref(v___y_844_);
v_size_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_size_848_);
v_buckets_849_ = lean_ctor_get(v___x_847_, 1);
lean_inc_ref(v_buckets_849_);
lean_dec_ref(v___x_847_);
v___x_850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2));
v___x_851_ = lean_mk_empty_array_with_capacity(v_size_848_);
lean_dec(v_size_848_);
v___x_852_ = lean_array_get_size(v_buckets_849_);
v___x_853_ = lean_nat_dec_lt(v___x_841_, v___x_852_);
if (v___x_853_ == 0)
{
lean_dec_ref(v_buckets_849_);
v___y_833_ = v___x_850_;
v___y_834_ = v___x_846_;
v___y_835_ = v___x_851_;
goto v___jp_832_;
}
else
{
uint8_t v___x_854_; 
v___x_854_ = lean_nat_dec_le(v___x_852_, v___x_852_);
if (v___x_854_ == 0)
{
if (v___x_853_ == 0)
{
lean_dec_ref(v_buckets_849_);
v___y_833_ = v___x_850_;
v___y_834_ = v___x_846_;
v___y_835_ = v___x_851_;
goto v___jp_832_;
}
else
{
size_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_usize_of_nat(v___x_852_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_buckets_849_, v___x_846_, v___x_855_, v___x_851_);
lean_dec_ref(v_buckets_849_);
v___y_833_ = v___x_850_;
v___y_834_ = v___x_846_;
v___y_835_ = v___x_856_;
goto v___jp_832_;
}
}
else
{
size_t v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_usize_of_nat(v___x_852_);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_buckets_849_, v___x_846_, v___x_857_, v___x_851_);
lean_dec_ref(v_buckets_849_);
v___y_833_ = v___x_850_;
v___y_834_ = v___x_846_;
v___y_835_ = v___x_858_;
goto v___jp_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object* v_var2Cnf_869_, lean_object* v_assignment_870_, lean_object* v_aigSize_871_, lean_object* v_atomsAssignment_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_var2Cnf_869_, v_assignment_870_, v_aigSize_871_, v_atomsAssignment_872_);
lean_dec_ref(v_atomsAssignment_872_);
lean_dec(v_aigSize_871_);
lean_dec_ref(v_assignment_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object* v_as_874_, lean_object* v_as_x27_875_, lean_object* v_b_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_875_, v_b_876_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___boxed(lean_object* v_as_879_, lean_object* v_as_x27_880_, lean_object* v_b_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(v_as_879_, v_as_x27_880_, v_b_881_, v_a_882_);
lean_dec(v_as_x27_880_);
lean_dec(v_as_879_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object* v_00_u03b2_884_, lean_object* v_m_885_, lean_object* v_a_886_, lean_object* v_fallback_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_885_, v_a_886_, v_fallback_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object* v_00_u03b2_889_, lean_object* v_m_890_, lean_object* v_a_891_, lean_object* v_fallback_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_00_u03b2_889_, v_m_890_, v_a_891_, v_fallback_892_);
lean_dec(v_fallback_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_m_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object* v_00_u03b2_894_, lean_object* v_k_895_, lean_object* v_v_896_, lean_object* v_t_897_, lean_object* v_hl_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_895_, v_v_896_, v_t_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object* v_00_u03b2_900_, lean_object* v_m_901_, lean_object* v_a_902_, lean_object* v_b_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_m_901_, v_a_902_, v_b_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(lean_object* v_00_u03b2_905_, lean_object* v_a_906_, lean_object* v_fallback_907_, lean_object* v_x_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_906_, v_fallback_907_, v_x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___boxed(lean_object* v_00_u03b2_910_, lean_object* v_a_911_, lean_object* v_fallback_912_, lean_object* v_x_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(v_00_u03b2_910_, v_a_911_, v_fallback_912_, v_x_913_);
lean_dec(v_x_913_);
lean_dec(v_fallback_912_);
lean_dec(v_a_911_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(lean_object* v_00_u03b2_915_, lean_object* v_a_916_, lean_object* v_x_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_916_, v_x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___boxed(lean_object* v_00_u03b2_919_, lean_object* v_a_920_, lean_object* v_x_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(v_00_u03b2_919_, v_a_920_, v_x_921_);
lean_dec(v_x_921_);
lean_dec(v_a_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9(lean_object* v_00_u03b2_924_, lean_object* v_data_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(v_data_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10(lean_object* v_00_u03b2_927_, lean_object* v_a_928_, lean_object* v_b_929_, lean_object* v_x_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_928_, v_b_929_, v_x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_932_, lean_object* v_i_933_, lean_object* v_source_934_, lean_object* v_target_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(v_i_933_, v_source_934_, v_target_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(lean_object* v_mvarId_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_941_, v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_948_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_948_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(lean_object* v_mvarId_965_, lean_object* v_x_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_965_, v_x_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_object* v_00_u03b1_973_, lean_object* v_mvarId_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_974_, v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(lean_object* v_00_u03b1_982_, lean_object* v_mvarId_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(v_00_u03b1_982_, v_mvarId_983_, v_x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(lean_object* v___x_991_, lean_object* v_x_992_, lean_object* v_counterExample_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_st_mk_ref(v___x_991_);
lean_inc(v___x_999_);
v___x_1000_ = lean_apply_7(v_x_992_, v_counterExample_993_, v___x_999_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v___x_1000_, 0);
lean_dec(v_unused_1009_);
v___x_1002_ = v___x_1000_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v___x_1000_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_st_ref_get(v___x_999_);
lean_dec(v___x_999_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___x_999_);
v_a_1010_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1000_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1000_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(lean_object* v___x_1018_, lean_object* v_x_1019_, lean_object* v_counterExample_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_1018_, v_x_1019_, v_counterExample_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v_res_1026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_unsigned_to_nat(16u);
v___x_1029_ = lean_mk_array(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2));
v___x_1036_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1);
v___x_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
lean_ctor_set(v___x_1037_, 2, v___x_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(lean_object* v_x_1038_, lean_object* v_counterExample_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_goal_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; 
v_goal_1045_ = lean_ctor_get(v_counterExample_1039_, 0);
lean_inc(v_goal_1045_);
v___x_1046_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1047_, 0, v___x_1046_);
lean_closure_set(v___f_1047_, 1, v_x_1038_);
lean_closure_set(v___f_1047_, 2, v_counterExample_1039_);
v___x_1048_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_goal_1045_, v___f_1047_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(lean_object* v_x_1049_, lean_object* v_counterExample_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_1049_, v_counterExample_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(lean_object* v_a_1057_){
_start:
{
lean_object* v_unusedHypotheses_1059_; lean_object* v___x_1060_; 
v_unusedHypotheses_1059_ = lean_ctor_get(v_a_1057_, 1);
lean_inc_ref(v_unusedHypotheses_1059_);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_unusedHypotheses_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_1061_);
lean_dec_ref(v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_unusedHypotheses_1071_; lean_object* v___x_1072_; 
v_unusedHypotheses_1071_ = lean_ctor_get(v_a_1064_, 1);
lean_inc_ref(v_unusedHypotheses_1071_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_unusedHypotheses_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(lean_object* v_a_1081_){
_start:
{
lean_object* v_equations_1083_; lean_object* v___x_1084_; 
v_equations_1083_ = lean_ctor_get(v_a_1081_, 2);
lean_inc_ref(v_equations_1083_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_equations_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_1085_);
lean_dec_ref(v_a_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_equations_1095_; lean_object* v___x_1096_; 
v_equations_1095_ = lean_ctor_get(v_a_1088_, 2);
lean_inc_ref(v_equations_1095_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_equations_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(lean_object* v_e_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_uninterpretedSymbols_1111_; lean_object* v_unusedRelevantHypotheses_1112_; lean_object* v_derivedEquations_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1126_; 
v___x_1110_ = lean_st_ref_take(v_a_1108_);
v_uninterpretedSymbols_1111_ = lean_ctor_get(v___x_1110_, 0);
v_unusedRelevantHypotheses_1112_ = lean_ctor_get(v___x_1110_, 1);
v_derivedEquations_1113_ = lean_ctor_get(v___x_1110_, 2);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1115_ = v___x_1110_;
v_isShared_1116_ = v_isSharedCheck_1126_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_derivedEquations_1113_);
lean_inc(v_unusedRelevantHypotheses_1112_);
lean_inc(v_uninterpretedSymbols_1111_);
lean_dec(v___x_1110_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1126_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1117_, v___x_1118_, v_uninterpretedSymbols_1111_, v_e_1107_, v___x_1119_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1120_);
v___x_1122_ = v___x_1115_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_unusedRelevantHypotheses_1112_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_derivedEquations_1113_);
v___x_1122_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_st_ref_set(v_a_1108_, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1119_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object* v_e_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_1127_, v_a_1128_);
lean_dec(v_a_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(lean_object* v_e_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v_uninterpretedSymbols_1140_; lean_object* v_unusedRelevantHypotheses_1141_; lean_object* v_derivedEquations_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1155_; 
v___x_1139_ = lean_st_ref_take(v_a_1133_);
v_uninterpretedSymbols_1140_ = lean_ctor_get(v___x_1139_, 0);
v_unusedRelevantHypotheses_1141_ = lean_ctor_get(v___x_1139_, 1);
v_derivedEquations_1142_ = lean_ctor_get(v___x_1139_, 2);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1144_ = v___x_1139_;
v_isShared_1145_ = v_isSharedCheck_1155_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_derivedEquations_1142_);
lean_inc(v_unusedRelevantHypotheses_1141_);
lean_inc(v_uninterpretedSymbols_1140_);
lean_dec(v___x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1155_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1148_ = lean_box(0);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1146_, v___x_1147_, v_uninterpretedSymbols_1140_, v_e_1131_, v___x_1148_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1149_);
v___x_1151_ = v___x_1144_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_unusedRelevantHypotheses_1141_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_derivedEquations_1142_);
v___x_1151_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_st_ref_set(v_a_1133_, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1148_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(lean_object* v_e_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object* v_fvar_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v_uninterpretedSymbols_1171_; lean_object* v_unusedRelevantHypotheses_1172_; lean_object* v_derivedEquations_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1186_; 
v___x_1170_ = lean_st_ref_take(v_a_1168_);
v_uninterpretedSymbols_1171_ = lean_ctor_get(v___x_1170_, 0);
v_unusedRelevantHypotheses_1172_ = lean_ctor_get(v___x_1170_, 1);
v_derivedEquations_1173_ = lean_ctor_get(v___x_1170_, 2);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1175_ = v___x_1170_;
v_isShared_1176_ = v_isSharedCheck_1186_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_derivedEquations_1173_);
lean_inc(v_unusedRelevantHypotheses_1172_);
lean_inc(v_uninterpretedSymbols_1171_);
lean_dec(v___x_1170_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1186_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1179_ = lean_box(0);
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1177_, v___x_1178_, v_unusedRelevantHypotheses_1172_, v_fvar_1167_, v___x_1179_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1180_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_uninterpretedSymbols_1171_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_derivedEquations_1173_);
v___x_1182_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_st_ref_set(v_a_1168_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1179_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object* v_fvar_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_fvar_1187_, v_a_1188_);
lean_dec(v_a_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(lean_object* v_fvar_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v_uninterpretedSymbols_1200_; lean_object* v_unusedRelevantHypotheses_1201_; lean_object* v_derivedEquations_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1215_; 
v___x_1199_ = lean_st_ref_take(v_a_1193_);
v_uninterpretedSymbols_1200_ = lean_ctor_get(v___x_1199_, 0);
v_unusedRelevantHypotheses_1201_ = lean_ctor_get(v___x_1199_, 1);
v_derivedEquations_1202_ = lean_ctor_get(v___x_1199_, 2);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1204_ = v___x_1199_;
v_isShared_1205_ = v_isSharedCheck_1215_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_derivedEquations_1202_);
lean_inc(v_unusedRelevantHypotheses_1201_);
lean_inc(v_uninterpretedSymbols_1200_);
lean_dec(v___x_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1215_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1206_, v___x_1207_, v_unusedRelevantHypotheses_1201_, v_fvar_1191_, v___x_1208_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1209_);
v___x_1211_ = v___x_1204_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_uninterpretedSymbols_1200_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_derivedEquations_1202_);
v___x_1211_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_st_ref_set(v_a_1193_, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1208_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object* v_fvar_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_fvar_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(lean_object* v_var_1225_, lean_object* v_value_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v_uninterpretedSymbols_1230_; lean_object* v_unusedRelevantHypotheses_1231_; lean_object* v_derivedEquations_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1244_; 
v___x_1229_ = lean_st_ref_take(v_a_1227_);
v_uninterpretedSymbols_1230_ = lean_ctor_get(v___x_1229_, 0);
v_unusedRelevantHypotheses_1231_ = lean_ctor_get(v___x_1229_, 1);
v_derivedEquations_1232_ = lean_ctor_get(v___x_1229_, 2);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1234_ = v___x_1229_;
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_derivedEquations_1232_);
lean_inc(v_unusedRelevantHypotheses_1231_);
lean_inc(v_uninterpretedSymbols_1230_);
lean_dec(v___x_1229_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_var_1225_);
lean_ctor_set(v___x_1236_, 1, v_value_1226_);
v___x_1237_ = lean_array_push(v_derivedEquations_1232_, v___x_1236_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 2, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_uninterpretedSymbols_1230_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_unusedRelevantHypotheses_1231_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_st_ref_set(v_a_1227_, v___x_1239_);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object* v_var_1245_, lean_object* v_value_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_1245_, v_value_1246_, v_a_1247_);
lean_dec(v_a_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(lean_object* v_var_1250_, lean_object* v_value_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v_uninterpretedSymbols_1260_; lean_object* v_unusedRelevantHypotheses_1261_; lean_object* v_derivedEquations_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1274_; 
v___x_1259_ = lean_st_ref_take(v_a_1253_);
v_uninterpretedSymbols_1260_ = lean_ctor_get(v___x_1259_, 0);
v_unusedRelevantHypotheses_1261_ = lean_ctor_get(v___x_1259_, 1);
v_derivedEquations_1262_ = lean_ctor_get(v___x_1259_, 2);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1264_ = v___x_1259_;
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_derivedEquations_1262_);
lean_inc(v_unusedRelevantHypotheses_1261_);
lean_inc(v_uninterpretedSymbols_1260_);
lean_dec(v___x_1259_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_var_1250_);
lean_ctor_set(v___x_1266_, 1, v_value_1251_);
v___x_1267_ = lean_array_push(v_derivedEquations_1262_, v___x_1266_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 2, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_uninterpretedSymbols_1260_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_unusedRelevantHypotheses_1261_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_st_ref_set(v_a_1253_, v___x_1269_);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(lean_object* v_var_1275_, lean_object* v_value_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_1275_, v_value_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object* v_a_1285_, lean_object* v_x_1286_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = 0;
return v___x_1287_;
}
else
{
lean_object* v_key_1288_; lean_object* v_tail_1289_; uint8_t v___x_1290_; 
v_key_1288_ = lean_ctor_get(v_x_1286_, 0);
v_tail_1289_ = lean_ctor_get(v_x_1286_, 2);
v___x_1290_ = l_Lean_instBEqFVarId_beq(v_key_1288_, v_a_1285_);
if (v___x_1290_ == 0)
{
v_x_1286_ = v_tail_1289_;
goto _start;
}
else
{
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object* v_a_1292_, lean_object* v_x_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1292_, v_x_1293_);
lean_dec(v_x_1293_);
lean_dec(v_a_1292_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
return v_x_1296_;
}
else
{
lean_object* v_key_1298_; lean_object* v_value_1299_; lean_object* v_tail_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1323_; 
v_key_1298_ = lean_ctor_get(v_x_1297_, 0);
v_value_1299_ = lean_ctor_get(v_x_1297_, 1);
v_tail_1300_ = lean_ctor_get(v_x_1297_, 2);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1302_ = v_x_1297_;
v_isShared_1303_ = v_isSharedCheck_1323_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_tail_1300_);
lean_inc(v_value_1299_);
lean_inc(v_key_1298_);
lean_dec(v_x_1297_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1323_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; uint64_t v___x_1305_; uint64_t v___x_1306_; uint64_t v___x_1307_; uint64_t v_fold_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1304_ = lean_array_get_size(v_x_1296_);
v___x_1305_ = l_Lean_instHashableFVarId_hash(v_key_1298_);
v___x_1306_ = 32ULL;
v___x_1307_ = lean_uint64_shift_right(v___x_1305_, v___x_1306_);
v_fold_1308_ = lean_uint64_xor(v___x_1305_, v___x_1307_);
v___x_1309_ = 16ULL;
v___x_1310_ = lean_uint64_shift_right(v_fold_1308_, v___x_1309_);
v___x_1311_ = lean_uint64_xor(v_fold_1308_, v___x_1310_);
v___x_1312_ = lean_uint64_to_usize(v___x_1311_);
v___x_1313_ = lean_usize_of_nat(v___x_1304_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_sub(v___x_1313_, v___x_1314_);
v___x_1316_ = lean_usize_land(v___x_1312_, v___x_1315_);
v___x_1317_ = lean_array_uget_borrowed(v_x_1296_, v___x_1316_);
lean_inc(v___x_1317_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v___x_1317_);
v___x_1319_ = v___x_1302_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_key_1298_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_value_1299_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_array_uset(v_x_1296_, v___x_1316_, v___x_1319_);
v_x_1296_ = v___x_1320_;
v_x_1297_ = v_tail_1300_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1324_, lean_object* v_source_1325_, lean_object* v_target_1326_){
_start:
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_array_get_size(v_source_1325_);
v___x_1328_ = lean_nat_dec_lt(v_i_1324_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v_source_1325_);
lean_dec(v_i_1324_);
return v_target_1326_;
}
else
{
lean_object* v_es_1329_; lean_object* v___x_1330_; lean_object* v_source_1331_; lean_object* v_target_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_es_1329_ = lean_array_fget(v_source_1325_, v_i_1324_);
v___x_1330_ = lean_box(0);
v_source_1331_ = lean_array_fset(v_source_1325_, v_i_1324_, v___x_1330_);
v_target_1332_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_target_1326_, v_es_1329_);
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_nat_add(v_i_1324_, v___x_1333_);
lean_dec(v_i_1324_);
v_i_1324_ = v___x_1334_;
v_source_1325_ = v_source_1331_;
v_target_1326_ = v_target_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(lean_object* v_data_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_nbuckets_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1337_ = lean_array_get_size(v_data_1336_);
v___x_1338_ = lean_unsigned_to_nat(2u);
v_nbuckets_1339_ = lean_nat_mul(v___x_1337_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_mk_array(v_nbuckets_1339_, v___x_1341_);
v___x_1343_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v___x_1340_, v_data_1336_, v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object* v_m_1344_, lean_object* v_a_1345_, lean_object* v_b_1346_){
_start:
{
lean_object* v_size_1347_; lean_object* v_buckets_1348_; lean_object* v___x_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v_fold_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; lean_object* v_bkt_1362_; uint8_t v___x_1363_; 
v_size_1347_ = lean_ctor_get(v_m_1344_, 0);
v_buckets_1348_ = lean_ctor_get(v_m_1344_, 1);
v___x_1349_ = lean_array_get_size(v_buckets_1348_);
v___x_1350_ = l_Lean_instHashableFVarId_hash(v_a_1345_);
v___x_1351_ = 32ULL;
v___x_1352_ = lean_uint64_shift_right(v___x_1350_, v___x_1351_);
v_fold_1353_ = lean_uint64_xor(v___x_1350_, v___x_1352_);
v___x_1354_ = 16ULL;
v___x_1355_ = lean_uint64_shift_right(v_fold_1353_, v___x_1354_);
v___x_1356_ = lean_uint64_xor(v_fold_1353_, v___x_1355_);
v___x_1357_ = lean_uint64_to_usize(v___x_1356_);
v___x_1358_ = lean_usize_of_nat(v___x_1349_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_sub(v___x_1358_, v___x_1359_);
v___x_1361_ = lean_usize_land(v___x_1357_, v___x_1360_);
v_bkt_1362_ = lean_array_uget_borrowed(v_buckets_1348_, v___x_1361_);
v___x_1363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1345_, v_bkt_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1384_; 
lean_inc_ref(v_buckets_1348_);
lean_inc(v_size_1347_);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_m_1344_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; lean_object* v_unused_1386_; 
v_unused_1385_ = lean_ctor_get(v_m_1344_, 1);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_m_1344_, 0);
lean_dec(v_unused_1386_);
v___x_1365_ = v_m_1344_;
v_isShared_1366_ = v_isSharedCheck_1384_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v_m_1344_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1384_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v_size_x27_1368_; lean_object* v___x_1369_; lean_object* v_buckets_x27_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v_size_x27_1368_ = lean_nat_add(v_size_1347_, v___x_1367_);
lean_dec(v_size_1347_);
lean_inc(v_bkt_1362_);
v___x_1369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1345_);
lean_ctor_set(v___x_1369_, 1, v_b_1346_);
lean_ctor_set(v___x_1369_, 2, v_bkt_1362_);
v_buckets_x27_1370_ = lean_array_uset(v_buckets_1348_, v___x_1361_, v___x_1369_);
v___x_1371_ = lean_unsigned_to_nat(4u);
v___x_1372_ = lean_nat_mul(v_size_x27_1368_, v___x_1371_);
v___x_1373_ = lean_unsigned_to_nat(3u);
v___x_1374_ = lean_nat_div(v___x_1372_, v___x_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_array_get_size(v_buckets_x27_1370_);
v___x_1376_ = lean_nat_dec_le(v___x_1374_, v___x_1375_);
lean_dec(v___x_1374_);
if (v___x_1376_ == 0)
{
lean_object* v_val_1377_; lean_object* v___x_1379_; 
v_val_1377_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_buckets_x27_1370_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_val_1377_);
lean_ctor_set(v___x_1365_, 0, v_size_x27_1368_);
v___x_1379_ = v___x_1365_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_size_x27_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_val_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v___x_1382_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_buckets_x27_1370_);
lean_ctor_set(v___x_1365_, 0, v_size_x27_1368_);
v___x_1382_ = v___x_1365_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_size_x27_1368_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_buckets_x27_1370_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_dec(v_b_1346_);
lean_dec(v_a_1345_);
return v_m_1344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object* v_fvar_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
if (lean_obj_tag(v_a_1388_) == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_a_1389_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
else
{
lean_object* v_key_1397_; lean_object* v_tail_1398_; lean_object* v___x_1399_; 
v_key_1397_ = lean_ctor_get(v_a_1388_, 0);
lean_inc_n(v_key_1397_, 2);
v_tail_1398_ = lean_ctor_get(v_a_1388_, 2);
lean_inc(v_tail_1398_);
lean_dec_ref_known(v_a_1388_, 3);
v___x_1399_ = l_Lean_FVarId_getType___redArg(v_key_1397_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = lean_box(0);
v___x_1402_ = l_Lean_Expr_containsFVar(v_a_1400_, v_fvar_1387_);
lean_dec(v_a_1400_);
if (v___x_1402_ == 0)
{
lean_dec(v_key_1397_);
v_a_1388_ = v_tail_1398_;
v_a_1389_ = v___x_1401_;
goto _start;
}
else
{
lean_object* v___x_1404_; lean_object* v_uninterpretedSymbols_1405_; lean_object* v_unusedRelevantHypotheses_1406_; lean_object* v_derivedEquations_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1417_; 
v___x_1404_ = lean_st_ref_take(v___y_1390_);
v_uninterpretedSymbols_1405_ = lean_ctor_get(v___x_1404_, 0);
v_unusedRelevantHypotheses_1406_ = lean_ctor_get(v___x_1404_, 1);
v_derivedEquations_1407_ = lean_ctor_get(v___x_1404_, 2);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1409_ = v___x_1404_;
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_derivedEquations_1407_);
lean_inc(v_unusedRelevantHypotheses_1406_);
lean_inc(v_uninterpretedSymbols_1405_);
lean_dec(v___x_1404_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_unusedRelevantHypotheses_1406_, v_key_1397_, v___x_1401_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_uninterpretedSymbols_1405_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_derivedEquations_1407_);
v___x_1413_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_st_ref_set(v___y_1390_, v___x_1413_);
v_a_1388_ = v_tail_1398_;
v_a_1389_ = v___x_1401_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_tail_1398_);
lean_dec(v_key_1397_);
v_a_1418_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1399_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1399_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object* v_fvar_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1426_, v_a_1427_, v_a_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec(v_fvar_1426_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object* v_fvar_1435_, lean_object* v_as_1436_, size_t v_sz_1437_, size_t v_i_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_lt(v_i_1438_, v_sz_1437_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1439_);
return v___x_1448_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_array_uget_borrowed(v_as_1436_, v_i_1438_);
lean_inc(v_a_1449_);
v___x_1450_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1435_, v_a_1449_, v_b_1439_, v___y_1441_, v___y_1442_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1463_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1463_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1463_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
if (lean_obj_tag(v_a_1451_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v_a_1451_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v_a_1451_, 1);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v_a_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v_a_1459_; size_t v___x_1460_; size_t v___x_1461_; 
lean_del_object(v___x_1453_);
v_a_1459_ = lean_ctor_get(v_a_1451_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v_a_1451_, 1);
v___x_1460_ = ((size_t)1ULL);
v___x_1461_ = lean_usize_add(v_i_1438_, v___x_1460_);
v_i_1438_ = v___x_1461_;
v_b_1439_ = v_a_1459_;
goto _start;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1450_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1450_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object* v_fvar_1472_, lean_object* v_as_1473_, lean_object* v_sz_1474_, lean_object* v_i_1475_, lean_object* v_b_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1474_);
lean_dec(v_sz_1474_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1472_, v_as_1473_, v_sz_boxed_1484_, v_i_boxed_1485_, v_b_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec_ref(v_as_1473_);
lean_dec(v_fvar_1472_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object* v_fvar_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_unusedHypotheses_1495_; lean_object* v_buckets_1496_; lean_object* v___x_1497_; size_t v_sz_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v_unusedHypotheses_1495_ = lean_ctor_get(v_a_1488_, 1);
v_buckets_1496_ = lean_ctor_get(v_unusedHypotheses_1495_, 1);
v___x_1497_ = lean_box(0);
v_sz_1498_ = lean_array_size(v_buckets_1496_);
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1487_, v_buckets_1496_, v_sz_1498_, v___x_1499_, v___x_1497_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___x_1500_, 0);
lean_dec(v_unused_1508_);
v___x_1502_ = v___x_1500_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_dec(v___x_1500_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1497_);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1497_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object* v_fvar_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_fvar_1509_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object* v_00_u03b2_1518_, lean_object* v_m_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_1519_, v_a_1520_, v_b_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object* v_fvar_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1523_, v_a_1524_, v_a_1525_, v___y_1527_, v___y_1528_, v___y_1530_, v___y_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object* v_fvar_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_fvar_1534_, v_a_1535_, v_a_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_fvar_1534_);
return v_res_1544_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object* v_00_u03b2_1545_, lean_object* v_a_1546_, lean_object* v_x_1547_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1546_, v_x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1549_, lean_object* v_a_1550_, lean_object* v_x_1551_){
_start:
{
uint8_t v_res_1552_; lean_object* v_r_1553_; 
v_res_1552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(v_00_u03b2_1549_, v_a_1550_, v_x_1551_);
lean_dec(v_x_1551_);
lean_dec(v_a_1550_);
v_r_1553_ = lean_box(v_res_1552_);
return v_r_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1(lean_object* v_00_u03b2_1554_, lean_object* v_data_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_data_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1557_, lean_object* v_i_1558_, lean_object* v_source_1559_, lean_object* v_target_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v_i_1558_, v_source_1559_, v_target_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_x_1563_, v_x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_instMonadEIO(lean_box(0));
return v___x_1566_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = l_Lean_instInhabitedExpr;
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_toApplicative_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1646_; 
v___x_1581_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0);
v___x_1582_ = l_StateRefT_x27_instMonad___redArg(v___x_1581_);
v_toApplicative_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1582_, 1);
lean_dec(v_unused_1647_);
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1646_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_toApplicative_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1646_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_toFunctor_1587_; lean_object* v_toSeq_1588_; lean_object* v_toSeqLeft_1589_; lean_object* v_toSeqRight_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1644_; 
v_toFunctor_1587_ = lean_ctor_get(v_toApplicative_1583_, 0);
v_toSeq_1588_ = lean_ctor_get(v_toApplicative_1583_, 2);
v_toSeqLeft_1589_ = lean_ctor_get(v_toApplicative_1583_, 3);
v_toSeqRight_1590_ = lean_ctor_get(v_toApplicative_1583_, 4);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_toApplicative_1583_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v_toApplicative_1583_, 1);
lean_dec(v_unused_1645_);
v___x_1592_ = v_toApplicative_1583_;
v_isShared_1593_ = v_isSharedCheck_1644_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_toSeqRight_1590_);
lean_inc(v_toSeqLeft_1589_);
lean_inc(v_toSeq_1588_);
lean_inc(v_toFunctor_1587_);
lean_dec(v_toApplicative_1583_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1644_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___f_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; lean_object* v___x_1603_; 
v___f_1594_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1));
v___f_1595_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1587_);
v___f_1596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1596_, 0, v_toFunctor_1587_);
v___f_1597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1597_, 0, v_toFunctor_1587_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___f_1596_);
lean_ctor_set(v___x_1598_, 1, v___f_1597_);
v___f_1599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1599_, 0, v_toSeqRight_1590_);
v___f_1600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1600_, 0, v_toSeqLeft_1589_);
v___f_1601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1601_, 0, v_toSeq_1588_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 4, v___f_1599_);
lean_ctor_set(v___x_1592_, 3, v___f_1600_);
lean_ctor_set(v___x_1592_, 2, v___f_1601_);
lean_ctor_set(v___x_1592_, 1, v___f_1594_);
lean_ctor_set(v___x_1592_, 0, v___x_1598_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___f_1594_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v___f_1601_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v___f_1600_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___f_1599_);
v___x_1603_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1605_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___f_1595_);
lean_ctor_set(v___x_1585_, 0, v___x_1603_);
v___x_1605_ = v___x_1585_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___f_1595_);
v___x_1605_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v_toApplicative_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1640_; 
v___x_1606_ = l_StateRefT_x27_instMonad___redArg(v___x_1605_);
v_toApplicative_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v___x_1606_, 1);
lean_dec(v_unused_1641_);
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1640_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_toApplicative_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1640_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_toFunctor_1611_; lean_object* v_toSeq_1612_; lean_object* v_toSeqLeft_1613_; lean_object* v_toSeqRight_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1638_; 
v_toFunctor_1611_ = lean_ctor_get(v_toApplicative_1607_, 0);
v_toSeq_1612_ = lean_ctor_get(v_toApplicative_1607_, 2);
v_toSeqLeft_1613_ = lean_ctor_get(v_toApplicative_1607_, 3);
v_toSeqRight_1614_ = lean_ctor_get(v_toApplicative_1607_, 4);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_toApplicative_1607_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v_toApplicative_1607_, 1);
lean_dec(v_unused_1639_);
v___x_1616_ = v_toApplicative_1607_;
v_isShared_1617_ = v_isSharedCheck_1638_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_toSeqRight_1614_);
lean_inc(v_toSeqLeft_1613_);
lean_inc(v_toSeq_1612_);
lean_inc(v_toFunctor_1611_);
lean_dec(v_toApplicative_1607_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1638_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___f_1625_; lean_object* v___x_1627_; 
v___f_1618_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3));
v___f_1619_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1611_);
v___f_1620_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1620_, 0, v_toFunctor_1611_);
v___f_1621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1621_, 0, v_toFunctor_1611_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___f_1620_);
lean_ctor_set(v___x_1622_, 1, v___f_1621_);
v___f_1623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1623_, 0, v_toSeqRight_1614_);
v___f_1624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1624_, 0, v_toSeqLeft_1613_);
v___f_1625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1625_, 0, v_toSeq_1612_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v___f_1623_);
lean_ctor_set(v___x_1616_, 3, v___f_1624_);
lean_ctor_set(v___x_1616_, 2, v___f_1625_);
lean_ctor_set(v___x_1616_, 1, v___f_1618_);
lean_ctor_set(v___x_1616_, 0, v___x_1622_);
v___x_1627_ = v___x_1616_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___f_1618_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v___f_1625_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v___f_1624_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v___f_1623_);
v___x_1627_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v___f_1619_);
lean_ctor_set(v___x_1609_, 0, v___x_1627_);
v___x_1629_ = v___x_1609_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___f_1619_);
v___x_1629_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_41395__overap_1634_; lean_object* v___x_1635_; 
v___x_1630_ = l_StateRefT_x27_instMonad___redArg(v___x_1629_);
v___x_1631_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5);
v___x_1632_ = l_instInhabitedOfMonad___redArg(v___x_1630_, v___x_1631_);
v___f_1633_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1633_, 0, v___x_1632_);
v___x_41395__overap_1634_ = lean_panic_fn_borrowed(v___f_1633_, v_msg_1573_);
lean_dec_ref(v___f_1633_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
v___x_1635_ = lean_apply_7(v___x_41395__overap_1634_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, lean_box(0));
return v___x_1635_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(lean_object* v_msgData_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v_env_1664_; lean_object* v___x_1665_; lean_object* v_mctx_1666_; lean_object* v_lctx_1667_; lean_object* v_options_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1663_ = lean_st_ref_get(v___y_1661_);
v_env_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_env_1664_);
lean_dec(v___x_1663_);
v___x_1665_ = lean_st_ref_get(v___y_1659_);
v_mctx_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc_ref(v_mctx_1666_);
lean_dec(v___x_1665_);
v_lctx_1667_ = lean_ctor_get(v___y_1658_, 2);
v_options_1668_ = lean_ctor_get(v___y_1660_, 2);
lean_inc_ref(v_options_1668_);
lean_inc_ref(v_lctx_1667_);
v___x_1669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1669_, 0, v_env_1664_);
lean_ctor_set(v___x_1669_, 1, v_mctx_1666_);
lean_ctor_set(v___x_1669_, 2, v_lctx_1667_);
lean_ctor_set(v___x_1669_, 3, v_options_1668_);
v___x_1670_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_msgData_1657_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(lean_object* v_msgData_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(lean_object* v_msg_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_ref_1685_; lean_object* v___x_1686_; lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
v_ref_1685_ = lean_ctor_get(v___y_1682_, 5);
v___x_1686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msg_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_inc(v_ref_1685_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_ref_1685_);
lean_ctor_set(v___x_1691_, 1, v_a_1687_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 1);
lean_ctor_set(v___x_1689_, 0, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(lean_object* v_msg_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1703_, lean_object* v_msg_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_fileName_1712_; lean_object* v_fileMap_1713_; lean_object* v_options_1714_; lean_object* v_currRecDepth_1715_; lean_object* v_maxRecDepth_1716_; lean_object* v_ref_1717_; lean_object* v_currNamespace_1718_; lean_object* v_openDecls_1719_; lean_object* v_initHeartbeats_1720_; lean_object* v_maxHeartbeats_1721_; lean_object* v_quotContext_1722_; lean_object* v_currMacroScope_1723_; uint8_t v_diag_1724_; lean_object* v_cancelTk_x3f_1725_; uint8_t v_suppressElabErrors_1726_; lean_object* v_inheritedTraceOptions_1727_; lean_object* v_ref_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_fileName_1712_ = lean_ctor_get(v___y_1709_, 0);
v_fileMap_1713_ = lean_ctor_get(v___y_1709_, 1);
v_options_1714_ = lean_ctor_get(v___y_1709_, 2);
v_currRecDepth_1715_ = lean_ctor_get(v___y_1709_, 3);
v_maxRecDepth_1716_ = lean_ctor_get(v___y_1709_, 4);
v_ref_1717_ = lean_ctor_get(v___y_1709_, 5);
v_currNamespace_1718_ = lean_ctor_get(v___y_1709_, 6);
v_openDecls_1719_ = lean_ctor_get(v___y_1709_, 7);
v_initHeartbeats_1720_ = lean_ctor_get(v___y_1709_, 8);
v_maxHeartbeats_1721_ = lean_ctor_get(v___y_1709_, 9);
v_quotContext_1722_ = lean_ctor_get(v___y_1709_, 10);
v_currMacroScope_1723_ = lean_ctor_get(v___y_1709_, 11);
v_diag_1724_ = lean_ctor_get_uint8(v___y_1709_, sizeof(void*)*14);
v_cancelTk_x3f_1725_ = lean_ctor_get(v___y_1709_, 12);
v_suppressElabErrors_1726_ = lean_ctor_get_uint8(v___y_1709_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1727_ = lean_ctor_get(v___y_1709_, 13);
v_ref_1728_ = l_Lean_replaceRef(v_ref_1703_, v_ref_1717_);
lean_inc_ref(v_inheritedTraceOptions_1727_);
lean_inc(v_cancelTk_x3f_1725_);
lean_inc(v_currMacroScope_1723_);
lean_inc(v_quotContext_1722_);
lean_inc(v_maxHeartbeats_1721_);
lean_inc(v_initHeartbeats_1720_);
lean_inc(v_openDecls_1719_);
lean_inc(v_currNamespace_1718_);
lean_inc(v_maxRecDepth_1716_);
lean_inc(v_currRecDepth_1715_);
lean_inc_ref(v_options_1714_);
lean_inc_ref(v_fileMap_1713_);
lean_inc_ref(v_fileName_1712_);
v___x_1729_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1729_, 0, v_fileName_1712_);
lean_ctor_set(v___x_1729_, 1, v_fileMap_1713_);
lean_ctor_set(v___x_1729_, 2, v_options_1714_);
lean_ctor_set(v___x_1729_, 3, v_currRecDepth_1715_);
lean_ctor_set(v___x_1729_, 4, v_maxRecDepth_1716_);
lean_ctor_set(v___x_1729_, 5, v_ref_1728_);
lean_ctor_set(v___x_1729_, 6, v_currNamespace_1718_);
lean_ctor_set(v___x_1729_, 7, v_openDecls_1719_);
lean_ctor_set(v___x_1729_, 8, v_initHeartbeats_1720_);
lean_ctor_set(v___x_1729_, 9, v_maxHeartbeats_1721_);
lean_ctor_set(v___x_1729_, 10, v_quotContext_1722_);
lean_ctor_set(v___x_1729_, 11, v_currMacroScope_1723_);
lean_ctor_set(v___x_1729_, 12, v_cancelTk_x3f_1725_);
lean_ctor_set(v___x_1729_, 13, v_inheritedTraceOptions_1727_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*14, v_diag_1724_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*14 + 1, v_suppressElabErrors_1726_);
v___x_1730_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1704_, v___y_1707_, v___y_1708_, v___x_1729_, v___y_1710_);
lean_dec_ref_known(v___x_1729_, 14);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1731_, lean_object* v_msg_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1731_, v_msg_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v_ref_1731_);
return v_res_1740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
lean_ctor_set(v___x_1746_, 3, v___x_1745_);
lean_ctor_set(v___x_1746_, 4, v___x_1744_);
lean_ctor_set(v___x_1746_, 5, v___x_1744_);
lean_ctor_set(v___x_1746_, 6, v___x_1744_);
lean_ctor_set(v___x_1746_, 7, v___x_1744_);
lean_ctor_set(v___x_1746_, 8, v___x_1744_);
lean_ctor_set(v___x_1746_, 9, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(32u);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1750_ = ((size_t)5ULL);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_unsigned_to_nat(32u);
v___x_1753_ = lean_mk_empty_array_with_capacity(v___x_1752_);
v___x_1754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1755_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___x_1753_);
lean_ctor_set(v___x_1755_, 2, v___x_1751_);
lean_ctor_set(v___x_1755_, 3, v___x_1751_);
lean_ctor_set_usize(v___x_1755_, 4, v___x_1750_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = lean_box(1);
v___x_1757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_1758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
lean_ctor_set(v___x_1759_, 2, v___x_1756_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1765_ = l_Lean_stringToMessageData(v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1768_ = l_Lean_stringToMessageData(v___x_1767_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_1777_ = l_Lean_stringToMessageData(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_1780_ = l_Lean_stringToMessageData(v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1781_, lean_object* v_declHint_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v_env_1786_; uint8_t v___x_1787_; 
v___x_1785_ = lean_st_ref_get(v___y_1783_);
v_env_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc_ref(v_env_1786_);
lean_dec(v___x_1785_);
v___x_1787_ = l_Lean_Name_isAnonymous(v_declHint_1782_);
if (v___x_1787_ == 0)
{
uint8_t v_isExporting_1788_; 
v_isExporting_1788_ = lean_ctor_get_uint8(v_env_1786_, sizeof(void*)*8);
if (v_isExporting_1788_ == 0)
{
lean_object* v___x_1789_; 
lean_dec_ref(v_env_1786_);
lean_dec(v_declHint_1782_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_msg_1781_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
lean_inc_ref(v_env_1786_);
v___x_1790_ = l_Lean_Environment_setExporting(v_env_1786_, v___x_1787_);
lean_inc(v_declHint_1782_);
lean_inc_ref(v___x_1790_);
v___x_1791_ = l_Lean_Environment_contains(v___x_1790_, v_declHint_1782_, v_isExporting_1788_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1786_);
lean_dec(v_declHint_1782_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_msg_1781_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_c_1798_; lean_object* v___x_1799_; 
v___x_1793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_1794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1795_ = l_Lean_Options_empty;
v___x_1796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1790_);
lean_ctor_set(v___x_1796_, 1, v___x_1793_);
lean_ctor_set(v___x_1796_, 2, v___x_1794_);
lean_ctor_set(v___x_1796_, 3, v___x_1795_);
lean_inc(v_declHint_1782_);
v___x_1797_ = l_Lean_MessageData_ofConstName(v_declHint_1782_, v___x_1787_);
v_c_1798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1798_, 0, v___x_1796_);
lean_ctor_set(v_c_1798_, 1, v___x_1797_);
v___x_1799_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1786_, v_declHint_1782_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec_ref(v_env_1786_);
lean_dec(v_declHint_1782_);
v___x_1800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_c_1798_);
v___x_1802_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_MessageData_note(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_msg_1781_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v_val_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1842_; 
v_val_1807_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1809_ = v___x_1799_;
v_isShared_1810_ = v_isSharedCheck_1842_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_val_1807_);
lean_dec(v___x_1799_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1842_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_mod_1814_; uint8_t v___x_1815_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = l_Lean_Environment_header(v_env_1786_);
lean_dec_ref(v_env_1786_);
v___x_1813_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1812_);
v_mod_1814_ = lean_array_get(v___x_1811_, v___x_1813_, v_val_1807_);
lean_dec(v_val_1807_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l_Lean_isPrivateName(v_declHint_1782_);
lean_dec(v_declHint_1782_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v_c_1798_);
v___x_1818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = l_Lean_MessageData_ofName(v_mod_1814_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_MessageData_note(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_msg_1781_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1825_);
v___x_1827_ = v___x_1809_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_c_1798_);
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = l_Lean_MessageData_ofName(v_mod_1814_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_MessageData_note(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_msg_1781_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1838_);
v___x_1840_ = v___x_1809_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1843_; 
lean_dec_ref(v_env_1786_);
lean_dec(v_declHint_1782_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_msg_1781_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1844_, lean_object* v_declHint_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1844_, v_declHint_1845_, v___y_1846_);
lean_dec(v___y_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_1849_, lean_object* v_declHint_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
v___x_1858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1849_, v_declHint_1850_, v___y_1856_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = l_Lean_unknownIdentifierMessageTag;
v___x_1864_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_1869_, lean_object* v_declHint_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1869_, v_declHint_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_1879_, lean_object* v_msg_1880_, lean_object* v_declHint_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v_a_1890_; lean_object* v___x_1891_; 
v___x_1889_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1880_, v_declHint_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
v___x_1891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1879_, v_a_1890_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1892_, lean_object* v_msg_1893_, lean_object* v_declHint_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1892_, v_msg_1893_, v_declHint_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v_ref_1892_);
return v_res_1902_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1905_ = l_Lean_stringToMessageData(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1908_ = l_Lean_stringToMessageData(v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1909_, lean_object* v_constName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1918_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1919_ = 0;
lean_inc(v_constName_1910_);
v___x_1920_ = l_Lean_MessageData_ofConstName(v_constName_1910_, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1918_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1909_, v___x_1923_, v_constName_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1925_, lean_object* v_constName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1925_, v_constName_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v_ref_1925_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object* v_constName_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_ref_1943_; lean_object* v___x_1944_; 
v_ref_1943_ = lean_ctor_get(v___y_1940_, 5);
v___x_1944_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1943_, v_constName_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(lean_object* v_constName_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v_env_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1962_ = lean_st_ref_get(v___y_1960_);
v_env_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc_ref(v_env_1963_);
lean_dec(v___x_1962_);
v___x_1964_ = 0;
lean_inc(v_constName_1954_);
v___x_1965_ = l_Lean_Environment_find_x3f(v_env_1963_, v_constName_1954_, v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1966_;
}
else
{
lean_object* v_val_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_constName_1954_);
v_val_1967_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1965_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_val_1967_);
lean_dec(v___x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 0);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_val_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object* v_constName_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1983_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2));
v___x_1991_ = l_Lean_Expr_const___override(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5));
v___x_1995_ = lean_unsigned_to_nat(61u);
v___x_1996_ = lean_unsigned_to_nat(221u);
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4));
v___x_1998_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0));
v___x_1999_ = l_mkPanicMessageWithDecl(v___x_1998_, v___x_1997_, v___x_1996_, v___x_1995_, v___x_1994_);
return v___x_1999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = l_Lean_Level_ofNat(v___x_2063_);
return v___x_2064_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(0);
v___x_2066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
v___x_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39));
v___x_2070_ = l_Lean_Expr_const___override(v___x_2069_, v___x_2068_);
return v___x_2070_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43));
v___x_2075_ = l_Lean_mkConst(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46));
v___x_2082_ = l_Lean_Expr_const___override(v___x_2081_, v___x_2080_);
return v___x_2082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48));
v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
return v___x_2085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
static size_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52(void){
_start:
{
lean_object* v___x_2089_; size_t v___x_2090_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_isize_of_nat(v___x_2089_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55));
v___x_2098_ = l_Lean_Expr_const___override(v___x_2097_, v___x_2096_);
return v___x_2098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57));
v___x_2103_ = l_Lean_Expr_const___override(v___x_2102_, v___x_2101_);
return v___x_2103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_box(0);
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60));
v___x_2110_ = l_Lean_Expr_const___override(v___x_2109_, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66));
v___x_2121_ = l_Lean_mkConst(v___x_2120_, v___x_2119_);
return v___x_2121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = lean_box(0);
v___x_2127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69));
v___x_2128_ = l_Lean_mkConst(v___x_2127_, v___x_2126_);
return v___x_2128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73));
v___x_2136_ = l_Lean_mkConst(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75));
v___x_2142_ = l_Lean_Expr_const___override(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79));
v___x_2150_ = l_Lean_mkConst(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81));
v___x_2156_ = l_Lean_Expr_const___override(v___x_2155_, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85));
v___x_2164_ = l_Lean_mkConst(v___x_2163_, v___x_2162_);
return v___x_2164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_box(0);
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87));
v___x_2170_ = l_Lean_Expr_const___override(v___x_2169_, v___x_2168_);
return v___x_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_box(0);
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91));
v___x_2178_ = l_Lean_mkConst(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93));
v___x_2184_ = l_Lean_Expr_const___override(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97(void){
_start:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_int8_of_nat(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98));
v___x_2194_ = l_Lean_Expr_const___override(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100));
v___x_2200_ = l_Lean_Expr_const___override(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static uint16_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104(void){
_start:
{
lean_object* v___x_2204_; uint16_t v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_int16_of_nat(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105));
v___x_2210_ = l_Lean_Expr_const___override(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107));
v___x_2216_ = l_Lean_Expr_const___override(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static uint32_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111(void){
_start:
{
lean_object* v___x_2220_; uint32_t v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_int32_of_nat(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112));
v___x_2226_ = l_Lean_Expr_const___override(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114));
v___x_2232_ = l_Lean_Expr_const___override(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118(void){
_start:
{
lean_object* v___x_2236_; uint64_t v___x_2237_; 
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = lean_int64_of_nat(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_box(0);
v___x_2241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119));
v___x_2242_ = l_Lean_Expr_const___override(v___x_2241_, v___x_2240_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121));
v___x_2248_ = l_Lean_Expr_const___override(v___x_2247_, v___x_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object* v_var_2249_, lean_object* v_value_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = l_Lean_Expr_isFVar(v_var_2249_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_inc_ref(v_var_2249_);
v___x_2274_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_2249_, v_a_2254_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2785_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2785_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2785_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = l_Lean_Expr_cleanupAnnotations(v_a_2275_);
v___x_2344_ = l_Lean_Expr_isApp(v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec_ref(v___x_2343_);
v___y_2280_ = v_a_2251_;
v___y_2281_ = v_a_2252_;
v___y_2282_ = v_a_2253_;
v___y_2283_ = v_a_2254_;
v___y_2284_ = v_a_2255_;
v___y_2285_ = v_a_2256_;
goto v___jp_2279_;
}
else
{
lean_object* v_arg_2345_; lean_object* v___y_2347_; lean_object* v___y_2351_; lean_object* v___y_2355_; lean_object* v___y_2359_; lean_object* v___y_2363_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v_arg_2345_ = lean_ctor_get(v___x_2343_, 1);
lean_inc_ref(v_arg_2345_);
v___x_2366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2343_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9));
v___x_2368_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11));
v___x_2370_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13));
v___x_2372_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15));
v___x_2374_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17));
v___x_2376_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19));
v___x_2378_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21));
v___x_2380_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23));
v___x_2382_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25));
v___x_2384_ = l_Lean_Expr_isConstOf(v___x_2366_, v___x_2383_);
if (v___x_2384_ == 0)
{
uint8_t v___x_2385_; 
lean_dec_ref(v_arg_2345_);
v___x_2385_ = l_Lean_Expr_isApp(v___x_2366_);
if (v___x_2385_ == 0)
{
lean_dec_ref(v___x_2366_);
v___y_2280_ = v_a_2251_;
v___y_2281_ = v_a_2252_;
v___y_2282_ = v_a_2253_;
v___y_2283_ = v_a_2254_;
v___y_2284_ = v_a_2255_;
v___y_2285_ = v_a_2256_;
goto v___jp_2279_;
}
else
{
lean_object* v_arg_2386_; lean_object* v___y_2388_; lean_object* v___y_2392_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v_arg_2386_ = lean_ctor_get(v___x_2366_, 1);
lean_inc_ref(v_arg_2386_);
v___x_2395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2366_);
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28));
v___x_2397_ = l_Lean_Expr_isConstOf(v___x_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30));
v___x_2399_ = l_Lean_Expr_isConstOf(v___x_2395_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32));
v___x_2401_ = l_Lean_Expr_isConstOf(v___x_2395_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33));
v___x_2403_ = l_Lean_Expr_isConstOf(v___x_2395_, v___x_2402_);
lean_dec_ref(v___x_2395_);
if (v___x_2403_ == 0)
{
lean_dec_ref(v_arg_2386_);
v___y_2280_ = v_a_2251_;
v___y_2281_ = v_a_2252_;
v___y_2282_ = v_a_2253_;
v___y_2283_ = v_a_2254_;
v___y_2284_ = v_a_2255_;
v___y_2285_ = v_a_2256_;
goto v___jp_2279_;
}
else
{
lean_object* v_w_2404_; lean_object* v_bv_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2433_; 
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2404_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2405_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2407_ = v_value_2250_;
v_isShared_2408_ = v_isSharedCheck_2433_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_bv_2405_);
lean_inc(v_w_2404_);
lean_dec(v_value_2250_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2433_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = lean_unsigned_to_nat(32u);
v___x_2410_ = lean_nat_dec_eq(v_w_2404_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
lean_dec(v_bv_2405_);
lean_dec_ref(v_arg_2386_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35);
v___x_2412_ = l_Nat_reprFast(v_w_2404_);
v___x_2413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
v___x_2414_ = l_Lean_MessageData_ofFormat(v___x_2413_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set_tag(v___x_2407_, 7);
lean_ctor_set(v___x_2407_, 1, v___x_2414_);
lean_ctor_set(v___x_2407_, 0, v___x_2411_);
v___x_2416_ = v___x_2407_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2418_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2419_;
}
}
else
{
size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v_r_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec(v_w_2404_);
v___x_2421_ = lean_usize_of_nat(v_bv_2405_);
lean_dec(v_bv_2405_);
v___x_2422_ = lean_usize_to_nat(v___x_2421_);
v_r_2423_ = l_Lean_mkRawNatLit(v___x_2422_);
v___x_2424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2423_);
v___x_2427_ = l_Lean_Expr_app___override(v___x_2426_, v_r_2423_);
v___x_2428_ = l_Lean_mkApp3(v___x_2424_, v___x_2425_, v_r_2423_, v___x_2427_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 1, v___x_2428_);
lean_ctor_set(v___x_2407_, 0, v_arg_2386_);
v___x_2430_ = v___x_2407_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_arg_2386_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
}
}
}
else
{
lean_object* v_w_2434_; lean_object* v_bv_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v___x_2395_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2434_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2435_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2437_ = v_value_2250_;
v_isShared_2438_ = v_isSharedCheck_2463_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_bv_2435_);
lean_inc(v_w_2434_);
lean_dec(v_value_2250_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2463_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = lean_unsigned_to_nat(64u);
v___x_2440_ = lean_nat_dec_eq(v_w_2434_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec(v_bv_2435_);
lean_dec_ref(v_arg_2386_);
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49);
v___x_2442_ = l_Nat_reprFast(v_w_2434_);
v___x_2443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
v___x_2444_ = l_Lean_MessageData_ofFormat(v___x_2443_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 7);
lean_ctor_set(v___x_2437_, 1, v___x_2444_);
lean_ctor_set(v___x_2437_, 0, v___x_2441_);
v___x_2446_ = v___x_2437_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2448_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2449_;
}
}
else
{
size_t v___x_2451_; lean_object* v___x_2452_; lean_object* v_r_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
lean_dec(v_w_2434_);
v___x_2451_ = lean_usize_of_nat(v_bv_2435_);
lean_dec(v_bv_2435_);
v___x_2452_ = lean_usize_to_nat(v___x_2451_);
v_r_2453_ = l_Lean_mkRawNatLit(v___x_2452_);
v___x_2454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2453_);
v___x_2457_ = l_Lean_Expr_app___override(v___x_2456_, v_r_2453_);
v___x_2458_ = l_Lean_mkApp3(v___x_2454_, v___x_2455_, v_r_2453_, v___x_2457_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v___x_2458_);
lean_ctor_set(v___x_2437_, 0, v_arg_2386_);
v___x_2460_ = v___x_2437_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_arg_2386_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
}
}
}
}
else
{
lean_object* v_w_2464_; lean_object* v_bv_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v___x_2395_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2464_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2465_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2467_ = v_value_2250_;
v_isShared_2468_ = v_isSharedCheck_2496_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_bv_2465_);
lean_inc(v_w_2464_);
lean_dec(v_value_2250_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2496_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = lean_unsigned_to_nat(32u);
v___x_2470_ = lean_nat_dec_eq(v_w_2464_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_dec(v_bv_2465_);
lean_dec_ref(v_arg_2386_);
v___x_2471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51);
v___x_2472_ = l_Nat_reprFast(v_w_2464_);
v___x_2473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
v___x_2474_ = l_Lean_MessageData_ofFormat(v___x_2473_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 7);
lean_ctor_set(v___x_2467_, 1, v___x_2474_);
lean_ctor_set(v___x_2467_, 0, v___x_2471_);
v___x_2476_ = v___x_2467_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2478_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2479_;
}
}
else
{
lean_object* v___x_2481_; size_t v___x_2482_; size_t v___x_2483_; uint8_t v___x_2484_; 
lean_del_object(v___x_2467_);
v___x_2481_ = l_BitVec_toInt(v_w_2464_, v_bv_2465_);
lean_dec(v_w_2464_);
v___x_2482_ = lean_isize_of_int(v___x_2481_);
lean_dec(v___x_2481_);
v___x_2483_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2484_ = lean_isize_dec_le(v___x_2483_, v___x_2482_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2488_ = lean_isize_to_int(v___x_2482_);
v___x_2489_ = lean_int_neg(v___x_2488_);
lean_dec(v___x_2488_);
v___x_2490_ = l_Int_toNat(v___x_2489_);
lean_dec(v___x_2489_);
v___x_2491_ = l_Lean_instToExprISize_mkNat(v___x_2490_);
v___x_2492_ = l_Lean_mkApp3(v___x_2485_, v___x_2486_, v___x_2487_, v___x_2491_);
v___y_2392_ = v___x_2492_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_isize_to_int(v___x_2482_);
v___x_2494_ = l_Int_toNat(v___x_2493_);
lean_dec(v___x_2493_);
v___x_2495_ = l_Lean_instToExprISize_mkNat(v___x_2494_);
v___y_2392_ = v___x_2495_;
goto v___jp_2391_;
}
}
}
}
}
else
{
lean_object* v_w_2497_; lean_object* v_bv_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v___x_2395_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2497_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2498_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2500_ = v_value_2250_;
v_isShared_2501_ = v_isSharedCheck_2529_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_bv_2498_);
lean_inc(v_w_2497_);
lean_dec(v_value_2250_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2529_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = lean_unsigned_to_nat(64u);
v___x_2503_ = lean_nat_dec_eq(v_w_2497_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_dec(v_bv_2498_);
lean_dec_ref(v_arg_2386_);
v___x_2504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63);
v___x_2505_ = l_Nat_reprFast(v_w_2497_);
v___x_2506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
v___x_2507_ = l_Lean_MessageData_ofFormat(v___x_2506_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 7);
lean_ctor_set(v___x_2500_, 1, v___x_2507_);
lean_ctor_set(v___x_2500_, 0, v___x_2504_);
v___x_2509_ = v___x_2500_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2511_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2512_;
}
}
else
{
lean_object* v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; uint8_t v___x_2517_; 
lean_del_object(v___x_2500_);
v___x_2514_ = l_BitVec_toInt(v_w_2497_, v_bv_2498_);
lean_dec(v_w_2497_);
v___x_2515_ = lean_isize_of_int(v___x_2514_);
lean_dec(v___x_2514_);
v___x_2516_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2517_ = lean_isize_dec_le(v___x_2516_, v___x_2515_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2521_ = lean_isize_to_int(v___x_2515_);
v___x_2522_ = lean_int_neg(v___x_2521_);
lean_dec(v___x_2521_);
v___x_2523_ = l_Int_toNat(v___x_2522_);
lean_dec(v___x_2522_);
v___x_2524_ = l_Lean_instToExprISize_mkNat(v___x_2523_);
v___x_2525_ = l_Lean_mkApp3(v___x_2518_, v___x_2519_, v___x_2520_, v___x_2524_);
v___y_2388_ = v___x_2525_;
goto v___jp_2387_;
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_isize_to_int(v___x_2515_);
v___x_2527_ = l_Int_toNat(v___x_2526_);
lean_dec(v___x_2526_);
v___x_2528_ = l_Lean_instToExprISize_mkNat(v___x_2527_);
v___y_2388_ = v___x_2528_;
goto v___jp_2387_;
}
}
}
}
v___jp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_arg_2386_);
lean_ctor_set(v___x_2389_, 1, v___y_2388_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
v___jp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_arg_2386_);
lean_ctor_set(v___x_2393_, 1, v___y_2392_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
else
{
lean_object* v_w_2530_; lean_object* v_bv_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2530_ = lean_ctor_get(v_value_2250_, 0);
lean_inc(v_w_2530_);
v_bv_2531_ = lean_ctor_get(v_value_2250_, 1);
lean_inc(v_bv_2531_);
lean_dec_ref(v_value_2250_);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = l_BitVec_ofNat(v_w_2530_, v___x_2532_);
lean_dec(v_w_2530_);
v___x_2534_ = lean_nat_dec_eq(v_bv_2531_, v___x_2533_);
lean_dec(v___x_2533_);
lean_dec(v_bv_2531_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67);
v___y_2363_ = v___x_2535_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70);
v___y_2363_ = v___x_2536_;
goto v___jp_2362_;
}
}
}
else
{
lean_object* v_w_2537_; lean_object* v_bv_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2537_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2538_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2540_ = v_value_2250_;
v_isShared_2541_ = v_isSharedCheck_2566_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_bv_2538_);
lean_inc(v_w_2537_);
lean_dec(v_value_2250_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2566_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = lean_unsigned_to_nat(8u);
v___x_2543_ = lean_nat_dec_eq(v_w_2537_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_dec(v_bv_2538_);
lean_dec_ref(v_arg_2345_);
v___x_2544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72);
v___x_2545_ = l_Nat_reprFast(v_w_2537_);
v___x_2546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
v___x_2547_ = l_Lean_MessageData_ofFormat(v___x_2546_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 7);
lean_ctor_set(v___x_2540_, 1, v___x_2547_);
lean_ctor_set(v___x_2540_, 0, v___x_2544_);
v___x_2549_ = v___x_2540_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2551_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2552_;
}
}
else
{
uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v_r_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_dec(v_w_2537_);
v___x_2554_ = lean_uint8_of_nat_mk(v_bv_2538_);
v___x_2555_ = lean_uint8_to_nat(v___x_2554_);
v_r_2556_ = l_Lean_mkRawNatLit(v___x_2555_);
v___x_2557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74);
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76);
lean_inc_ref(v_r_2556_);
v___x_2560_ = l_Lean_Expr_app___override(v___x_2559_, v_r_2556_);
v___x_2561_ = l_Lean_mkApp3(v___x_2557_, v___x_2558_, v_r_2556_, v___x_2560_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 1, v___x_2561_);
lean_ctor_set(v___x_2540_, 0, v_arg_2345_);
v___x_2563_ = v___x_2540_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_arg_2345_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
return v___x_2564_;
}
}
}
}
}
else
{
lean_object* v_w_2567_; lean_object* v_bv_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2567_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2568_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2570_ = v_value_2250_;
v_isShared_2571_ = v_isSharedCheck_2596_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_bv_2568_);
lean_inc(v_w_2567_);
lean_dec(v_value_2250_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2596_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_unsigned_to_nat(16u);
v___x_2573_ = lean_nat_dec_eq(v_w_2567_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_bv_2568_);
lean_dec_ref(v_arg_2345_);
v___x_2574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78);
v___x_2575_ = l_Nat_reprFast(v_w_2567_);
v___x_2576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
v___x_2577_ = l_Lean_MessageData_ofFormat(v___x_2576_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 7);
lean_ctor_set(v___x_2570_, 1, v___x_2577_);
lean_ctor_set(v___x_2570_, 0, v___x_2574_);
v___x_2579_ = v___x_2570_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2581_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2582_;
}
}
else
{
uint16_t v___x_2584_; lean_object* v___x_2585_; lean_object* v_r_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_dec(v_w_2567_);
v___x_2584_ = lean_uint16_of_nat_mk(v_bv_2568_);
v___x_2585_ = lean_uint16_to_nat(v___x_2584_);
v_r_2586_ = l_Lean_mkRawNatLit(v___x_2585_);
v___x_2587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80);
v___x_2589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82);
lean_inc_ref(v_r_2586_);
v___x_2590_ = l_Lean_Expr_app___override(v___x_2589_, v_r_2586_);
v___x_2591_ = l_Lean_mkApp3(v___x_2587_, v___x_2588_, v_r_2586_, v___x_2590_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2591_);
lean_ctor_set(v___x_2570_, 0, v_arg_2345_);
v___x_2593_ = v___x_2570_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_arg_2345_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
}
}
}
else
{
lean_object* v_w_2597_; lean_object* v_bv_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2597_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2598_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2600_ = v_value_2250_;
v_isShared_2601_ = v_isSharedCheck_2626_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_bv_2598_);
lean_inc(v_w_2597_);
lean_dec(v_value_2250_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2626_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_unsigned_to_nat(32u);
v___x_2603_ = lean_nat_dec_eq(v_w_2597_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec(v_bv_2598_);
lean_dec_ref(v_arg_2345_);
v___x_2604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84);
v___x_2605_ = l_Nat_reprFast(v_w_2597_);
v___x_2606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
v___x_2607_ = l_Lean_MessageData_ofFormat(v___x_2606_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 7);
lean_ctor_set(v___x_2600_, 1, v___x_2607_);
lean_ctor_set(v___x_2600_, 0, v___x_2604_);
v___x_2609_ = v___x_2600_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2611_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2612_;
}
}
else
{
uint32_t v___x_2614_; lean_object* v___x_2615_; lean_object* v_r_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_dec(v_w_2597_);
v___x_2614_ = lean_uint32_of_nat_mk(v_bv_2598_);
v___x_2615_ = lean_uint32_to_nat(v___x_2614_);
v_r_2616_ = l_Lean_mkRawNatLit(v___x_2615_);
v___x_2617_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86);
v___x_2619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88);
lean_inc_ref(v_r_2616_);
v___x_2620_ = l_Lean_Expr_app___override(v___x_2619_, v_r_2616_);
v___x_2621_ = l_Lean_mkApp3(v___x_2617_, v___x_2618_, v_r_2616_, v___x_2620_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v___x_2621_);
lean_ctor_set(v___x_2600_, 0, v_arg_2345_);
v___x_2623_ = v___x_2600_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_arg_2345_);
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
else
{
lean_object* v_w_2627_; lean_object* v_bv_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2627_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2628_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2630_ = v_value_2250_;
v_isShared_2631_ = v_isSharedCheck_2656_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_bv_2628_);
lean_inc(v_w_2627_);
lean_dec(v_value_2250_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2656_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = lean_unsigned_to_nat(64u);
v___x_2633_ = lean_nat_dec_eq(v_w_2627_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec(v_bv_2628_);
lean_dec_ref(v_arg_2345_);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90);
v___x_2635_ = l_Nat_reprFast(v_w_2627_);
v___x_2636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
v___x_2637_ = l_Lean_MessageData_ofFormat(v___x_2636_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 7);
lean_ctor_set(v___x_2630_, 1, v___x_2637_);
lean_ctor_set(v___x_2630_, 0, v___x_2634_);
v___x_2639_ = v___x_2630_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2639_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2641_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2642_;
}
}
else
{
uint64_t v___x_2644_; lean_object* v___x_2645_; lean_object* v_r_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
lean_dec(v_w_2627_);
v___x_2644_ = lean_uint64_of_nat_mk(v_bv_2628_);
v___x_2645_ = lean_uint64_to_nat(v___x_2644_);
v_r_2646_ = l_Lean_mkRawNatLit(v___x_2645_);
v___x_2647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92);
v___x_2649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94);
lean_inc_ref(v_r_2646_);
v___x_2650_ = l_Lean_Expr_app___override(v___x_2649_, v_r_2646_);
v___x_2651_ = l_Lean_mkApp3(v___x_2647_, v___x_2648_, v_r_2646_, v___x_2650_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v___x_2651_);
lean_ctor_set(v___x_2630_, 0, v_arg_2345_);
v___x_2653_ = v___x_2630_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_arg_2345_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
}
}
}
else
{
lean_object* v_w_2657_; lean_object* v_bv_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2657_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2658_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2660_ = v_value_2250_;
v_isShared_2661_ = v_isSharedCheck_2688_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_bv_2658_);
lean_inc(v_w_2657_);
lean_dec(v_value_2250_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2688_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(8u);
v___x_2663_ = lean_nat_dec_eq(v_w_2657_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_dec(v_bv_2658_);
lean_dec_ref(v_arg_2345_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96);
v___x_2665_ = l_Nat_reprFast(v_w_2657_);
v___x_2666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
v___x_2667_ = l_Lean_MessageData_ofFormat(v___x_2666_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set_tag(v___x_2660_, 7);
lean_ctor_set(v___x_2660_, 1, v___x_2667_);
lean_ctor_set(v___x_2660_, 0, v___x_2664_);
v___x_2669_ = v___x_2660_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2671_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2672_;
}
}
else
{
uint8_t v___x_2674_; uint8_t v___x_2675_; uint8_t v___x_2676_; 
lean_del_object(v___x_2660_);
lean_dec(v_w_2657_);
v___x_2674_ = lean_uint8_of_nat_mk(v_bv_2658_);
v___x_2675_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97);
v___x_2676_ = lean_int8_dec_le(v___x_2675_, v___x_2674_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99);
v___x_2679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101);
v___x_2680_ = lean_int8_to_int(v___x_2674_);
v___x_2681_ = lean_int_neg(v___x_2680_);
v___x_2682_ = l_Int_toNat(v___x_2681_);
lean_dec(v___x_2681_);
v___x_2683_ = l_Lean_instToExprInt8_mkNat(v___x_2682_);
v___x_2684_ = l_Lean_mkApp3(v___x_2677_, v___x_2678_, v___x_2679_, v___x_2683_);
v___y_2359_ = v___x_2684_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_int8_to_int(v___x_2674_);
v___x_2686_ = l_Int_toNat(v___x_2685_);
v___x_2687_ = l_Lean_instToExprInt8_mkNat(v___x_2686_);
v___y_2359_ = v___x_2687_;
goto v___jp_2358_;
}
}
}
}
}
else
{
lean_object* v_w_2689_; lean_object* v_bv_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2689_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2690_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2692_ = v_value_2250_;
v_isShared_2693_ = v_isSharedCheck_2720_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_bv_2690_);
lean_inc(v_w_2689_);
lean_dec(v_value_2250_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2720_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = lean_unsigned_to_nat(16u);
v___x_2695_ = lean_nat_dec_eq(v_w_2689_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_bv_2690_);
lean_dec_ref(v_arg_2345_);
v___x_2696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103);
v___x_2697_ = l_Nat_reprFast(v_w_2689_);
v___x_2698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
v___x_2699_ = l_Lean_MessageData_ofFormat(v___x_2698_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 7);
lean_ctor_set(v___x_2692_, 1, v___x_2699_);
lean_ctor_set(v___x_2692_, 0, v___x_2696_);
v___x_2701_ = v___x_2692_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2703_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2704_;
}
}
else
{
uint16_t v___x_2706_; uint16_t v___x_2707_; uint8_t v___x_2708_; 
lean_del_object(v___x_2692_);
lean_dec(v_w_2689_);
v___x_2706_ = lean_uint16_of_nat_mk(v_bv_2690_);
v___x_2707_ = lean_uint16_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104);
v___x_2708_ = lean_int16_dec_le(v___x_2707_, v___x_2706_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106);
v___x_2711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108);
v___x_2712_ = lean_int16_to_int(v___x_2706_);
v___x_2713_ = lean_int_neg(v___x_2712_);
v___x_2714_ = l_Int_toNat(v___x_2713_);
lean_dec(v___x_2713_);
v___x_2715_ = l_Lean_instToExprInt16_mkNat(v___x_2714_);
v___x_2716_ = l_Lean_mkApp3(v___x_2709_, v___x_2710_, v___x_2711_, v___x_2715_);
v___y_2355_ = v___x_2716_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_int16_to_int(v___x_2706_);
v___x_2718_ = l_Int_toNat(v___x_2717_);
v___x_2719_ = l_Lean_instToExprInt16_mkNat(v___x_2718_);
v___y_2355_ = v___x_2719_;
goto v___jp_2354_;
}
}
}
}
}
else
{
lean_object* v_w_2721_; lean_object* v_bv_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2721_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2722_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2724_ = v_value_2250_;
v_isShared_2725_ = v_isSharedCheck_2752_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_bv_2722_);
lean_inc(v_w_2721_);
lean_dec(v_value_2250_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2752_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = lean_unsigned_to_nat(32u);
v___x_2727_ = lean_nat_dec_eq(v_w_2721_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v_bv_2722_);
lean_dec_ref(v_arg_2345_);
v___x_2728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110);
v___x_2729_ = l_Nat_reprFast(v_w_2721_);
v___x_2730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
v___x_2731_ = l_Lean_MessageData_ofFormat(v___x_2730_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 7);
lean_ctor_set(v___x_2724_, 1, v___x_2731_);
lean_ctor_set(v___x_2724_, 0, v___x_2728_);
v___x_2733_ = v___x_2724_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2735_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2736_;
}
}
else
{
uint32_t v___x_2738_; uint32_t v___x_2739_; uint8_t v___x_2740_; 
lean_del_object(v___x_2724_);
lean_dec(v_w_2721_);
v___x_2738_ = lean_uint32_of_nat_mk(v_bv_2722_);
v___x_2739_ = lean_uint32_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111);
v___x_2740_ = lean_int32_dec_le(v___x_2739_, v___x_2738_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113);
v___x_2743_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115);
v___x_2744_ = lean_int32_to_int(v___x_2738_);
v___x_2745_ = lean_int_neg(v___x_2744_);
lean_dec(v___x_2744_);
v___x_2746_ = l_Int_toNat(v___x_2745_);
lean_dec(v___x_2745_);
v___x_2747_ = l_Lean_instToExprInt32_mkNat(v___x_2746_);
v___x_2748_ = l_Lean_mkApp3(v___x_2741_, v___x_2742_, v___x_2743_, v___x_2747_);
v___y_2351_ = v___x_2748_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_int32_to_int(v___x_2738_);
v___x_2750_ = l_Int_toNat(v___x_2749_);
lean_dec(v___x_2749_);
v___x_2751_ = l_Lean_instToExprInt32_mkNat(v___x_2750_);
v___y_2351_ = v___x_2751_;
goto v___jp_2350_;
}
}
}
}
}
else
{
lean_object* v_w_2753_; lean_object* v_bv_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_var_2249_);
v_w_2753_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2754_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2756_ = v_value_2250_;
v_isShared_2757_ = v_isSharedCheck_2784_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_bv_2754_);
lean_inc(v_w_2753_);
lean_dec(v_value_2250_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2784_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2758_ = lean_unsigned_to_nat(64u);
v___x_2759_ = lean_nat_dec_eq(v_w_2753_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
lean_dec(v_bv_2754_);
lean_dec_ref(v_arg_2345_);
v___x_2760_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117);
v___x_2761_ = l_Nat_reprFast(v_w_2753_);
v___x_2762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
v___x_2763_ = l_Lean_MessageData_ofFormat(v___x_2762_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 7);
lean_ctor_set(v___x_2756_, 1, v___x_2763_);
lean_ctor_set(v___x_2756_, 0, v___x_2760_);
v___x_2765_ = v___x_2756_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2767_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2768_;
}
}
else
{
uint64_t v___x_2770_; uint64_t v___x_2771_; uint8_t v___x_2772_; 
lean_del_object(v___x_2756_);
lean_dec(v_w_2753_);
v___x_2770_ = lean_uint64_of_nat_mk(v_bv_2754_);
v___x_2771_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118);
v___x_2772_ = lean_int64_dec_le(v___x_2771_, v___x_2770_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120);
v___x_2775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122);
v___x_2776_ = lean_int64_to_int_sint(v___x_2770_);
v___x_2777_ = lean_int_neg(v___x_2776_);
lean_dec(v___x_2776_);
v___x_2778_ = l_Int_toNat(v___x_2777_);
lean_dec(v___x_2777_);
v___x_2779_ = l_Lean_instToExprInt64_mkNat(v___x_2778_);
v___x_2780_ = l_Lean_mkApp3(v___x_2773_, v___x_2774_, v___x_2775_, v___x_2779_);
v___y_2347_ = v___x_2780_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_int64_to_int_sint(v___x_2770_);
v___x_2782_ = l_Int_toNat(v___x_2781_);
lean_dec(v___x_2781_);
v___x_2783_ = l_Lean_instToExprInt64_mkNat(v___x_2782_);
v___y_2347_ = v___x_2783_;
goto v___jp_2346_;
}
}
}
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_arg_2345_);
lean_ctor_set(v___x_2348_, 1, v___y_2347_);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
v___jp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_arg_2345_);
lean_ctor_set(v___x_2352_, 1, v___y_2351_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v_arg_2345_);
lean_ctor_set(v___x_2356_, 1, v___y_2355_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
v___jp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_arg_2345_);
lean_ctor_set(v___x_2360_, 1, v___y_2359_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
v___jp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_inc_ref(v___y_2363_);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_arg_2345_);
lean_ctor_set(v___x_2364_, 1, v___y_2363_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
v___jp_2279_:
{
if (lean_obj_tag(v_var_2249_) == 5)
{
lean_object* v_fn_2286_; 
v_fn_2286_ = lean_ctor_get(v_var_2249_, 0);
if (lean_obj_tag(v_fn_2286_) == 4)
{
lean_object* v_declName_2287_; 
v_declName_2287_ = lean_ctor_get(v_fn_2286_, 0);
if (lean_obj_tag(v_declName_2287_) == 1)
{
lean_object* v_arg_2288_; lean_object* v_us_2289_; lean_object* v_pre_2290_; lean_object* v_str_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
v_arg_2288_ = lean_ctor_get(v_var_2249_, 1);
v_us_2289_ = lean_ctor_get(v_fn_2286_, 1);
v_pre_2290_ = lean_ctor_get(v_declName_2287_, 0);
v_str_2291_ = lean_ctor_get(v_declName_2287_, 1);
v___x_2292_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix;
v___x_2293_ = lean_string_dec_eq(v_str_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v_w_2294_; lean_object* v_bv_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v_w_2294_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2295_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v_value_2250_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_bv_2295_);
lean_inc(v_w_2294_);
lean_dec(v_value_2250_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2300_ = l_Lean_mkNatLit(v_w_2294_);
v___x_2301_ = l_Lean_mkNatLit(v_bv_2295_);
v___x_2302_ = l_Lean_mkAppB(v___x_2299_, v___x_2300_, v___x_2301_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2302_);
lean_ctor_set(v___x_2297_, 0, v_var_2249_);
v___x_2304_ = v___x_2297_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_var_2249_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2304_);
v___x_2306_ = v___x_2277_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v___x_2310_; 
lean_inc(v_pre_2290_);
lean_inc(v_us_2289_);
lean_inc_ref(v_arg_2288_);
lean_dec_ref_known(v_var_2249_, 2);
lean_del_object(v___x_2277_);
v___x_2310_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_pre_2290_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2334_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2334_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2334_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
if (lean_obj_tag(v_a_2311_) == 5)
{
lean_object* v_val_2315_; lean_object* v_ctors_2316_; lean_object* v_bv_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2330_; 
v_val_2315_ = lean_ctor_get(v_a_2311_, 0);
lean_inc_ref(v_val_2315_);
lean_dec_ref_known(v_a_2311_, 1);
v_ctors_2316_ = lean_ctor_get(v_val_2315_, 4);
lean_inc(v_ctors_2316_);
lean_dec_ref(v_val_2315_);
v_bv_2317_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v_value_2250_, 0);
lean_dec(v_unused_2331_);
v___x_2319_ = v_value_2250_;
v_isShared_2320_ = v_isSharedCheck_2330_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_bv_2317_);
lean_dec(v_value_2250_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2330_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = l_List_get_x21Internal___redArg(v___x_2321_, v_ctors_2316_, v_bv_2317_);
lean_dec(v_ctors_2316_);
v___x_2323_ = l_Lean_mkConst(v___x_2322_, v_us_2289_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v___x_2323_);
lean_ctor_set(v___x_2319_, 0, v_arg_2288_);
v___x_2325_ = v___x_2319_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_arg_2288_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2325_);
v___x_2327_ = v___x_2313_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_del_object(v___x_2313_);
lean_dec(v_a_2311_);
lean_dec(v_us_2289_);
lean_dec_ref(v_arg_2288_);
lean_dec_ref(v_value_2250_);
v___x_2332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6);
v___x_2333_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v___x_2332_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2333_;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_us_2289_);
lean_dec_ref(v_arg_2288_);
lean_dec_ref(v_value_2250_);
v_a_2335_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2310_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2310_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
else
{
lean_del_object(v___x_2277_);
goto v___jp_2258_;
}
}
else
{
lean_del_object(v___x_2277_);
goto v___jp_2258_;
}
}
else
{
lean_del_object(v___x_2277_);
goto v___jp_2258_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v_value_2250_);
lean_dec_ref(v_var_2249_);
v_a_2786_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2274_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2274_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_w_2794_; lean_object* v_bv_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2807_; 
v_w_2794_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2795_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2797_ = v_value_2250_;
v_isShared_2798_ = v_isSharedCheck_2807_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_bv_2795_);
lean_inc(v_w_2794_);
lean_dec(v_value_2250_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2807_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2800_ = l_Lean_mkNatLit(v_w_2794_);
v___x_2801_ = l_Lean_mkNatLit(v_bv_2795_);
v___x_2802_ = l_Lean_mkAppB(v___x_2799_, v___x_2800_, v___x_2801_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v___x_2802_);
lean_ctor_set(v___x_2797_, 0, v_var_2249_);
v___x_2804_ = v___x_2797_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_var_2249_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
v___jp_2258_:
{
lean_object* v_w_2259_; lean_object* v_bv_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2272_; 
v_w_2259_ = lean_ctor_get(v_value_2250_, 0);
v_bv_2260_ = lean_ctor_get(v_value_2250_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_value_2250_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2262_ = v_value_2250_;
v_isShared_2263_ = v_isSharedCheck_2272_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_bv_2260_);
lean_inc(v_w_2259_);
lean_dec(v_value_2250_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2272_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2265_ = l_Lean_mkNatLit(v_w_2259_);
v___x_2266_ = l_Lean_mkNatLit(v_bv_2260_);
v___x_2267_ = l_Lean_mkAppB(v___x_2264_, v___x_2265_, v___x_2266_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 1, v___x_2267_);
lean_ctor_set(v___x_2262_, 0, v_var_2249_);
v___x_2269_ = v___x_2262_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_var_2249_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object* v_var_2808_, lean_object* v_value_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_2808_, v_value_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_object* v_00_u03b1_2818_, lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_2819_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_msg_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(v_00_u03b1_2828_, v_msg_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object* v_00_u03b1_2838_, lean_object* v_constName_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2848_, lean_object* v_constName_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(v_00_u03b1_2848_, v_constName_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2858_, lean_object* v_ref_2859_, lean_object* v_constName_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2859_, v_constName_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2869_, lean_object* v_ref_2870_, lean_object* v_constName_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(v_00_u03b1_2869_, v_ref_2870_, v_constName_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_ref_2870_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_2880_, lean_object* v_ref_2881_, lean_object* v_msg_2882_, lean_object* v_declHint_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2881_, v_msg_2882_, v_declHint_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2892_, lean_object* v_ref_2893_, lean_object* v_msg_2894_, lean_object* v_declHint_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_2892_, v_ref_2893_, v_msg_2894_, v_declHint_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v_ref_2893_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_2904_, lean_object* v_declHint_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_2904_, v_declHint_2905_, v___y_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2914_, lean_object* v_declHint_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_2914_, v_declHint_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2924_, lean_object* v_ref_2925_, lean_object* v_msg_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_2925_, v_msg_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2935_, lean_object* v_ref_2936_, lean_object* v_msg_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_2935_, v_ref_2936_, v_msg_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_ref_2936_);
return v_res_2945_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object* v_a_2946_, lean_object* v_x_2947_){
_start:
{
if (lean_obj_tag(v_x_2947_) == 0)
{
uint8_t v___x_2948_; 
v___x_2948_ = 0;
return v___x_2948_;
}
else
{
lean_object* v_key_2949_; lean_object* v_tail_2950_; uint8_t v___x_2951_; 
v_key_2949_ = lean_ctor_get(v_x_2947_, 0);
v_tail_2950_ = lean_ctor_get(v_x_2947_, 2);
v___x_2951_ = lean_expr_eqv(v_key_2949_, v_a_2946_);
if (v___x_2951_ == 0)
{
v_x_2947_ = v_tail_2950_;
goto _start;
}
else
{
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object* v_a_2953_, lean_object* v_x_2954_){
_start:
{
uint8_t v_res_2955_; lean_object* v_r_2956_; 
v_res_2955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_2953_, v_x_2954_);
lean_dec(v_x_2954_);
lean_dec_ref(v_a_2953_);
v_r_2956_ = lean_box(v_res_2955_);
return v_r_2956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
if (lean_obj_tag(v_x_2958_) == 0)
{
return v_x_2957_;
}
else
{
lean_object* v_key_2959_; lean_object* v_value_2960_; lean_object* v_tail_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2984_; 
v_key_2959_ = lean_ctor_get(v_x_2958_, 0);
v_value_2960_ = lean_ctor_get(v_x_2958_, 1);
v_tail_2961_ = lean_ctor_get(v_x_2958_, 2);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_x_2958_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2963_ = v_x_2958_;
v_isShared_2964_ = v_isSharedCheck_2984_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_tail_2961_);
lean_inc(v_value_2960_);
lean_inc(v_key_2959_);
lean_dec(v_x_2958_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2984_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; uint64_t v___x_2966_; uint64_t v___x_2967_; uint64_t v___x_2968_; uint64_t v_fold_2969_; uint64_t v___x_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2965_ = lean_array_get_size(v_x_2957_);
v___x_2966_ = l_Lean_Expr_hash(v_key_2959_);
v___x_2967_ = 32ULL;
v___x_2968_ = lean_uint64_shift_right(v___x_2966_, v___x_2967_);
v_fold_2969_ = lean_uint64_xor(v___x_2966_, v___x_2968_);
v___x_2970_ = 16ULL;
v___x_2971_ = lean_uint64_shift_right(v_fold_2969_, v___x_2970_);
v___x_2972_ = lean_uint64_xor(v_fold_2969_, v___x_2971_);
v___x_2973_ = lean_uint64_to_usize(v___x_2972_);
v___x_2974_ = lean_usize_of_nat(v___x_2965_);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_sub(v___x_2974_, v___x_2975_);
v___x_2977_ = lean_usize_land(v___x_2973_, v___x_2976_);
v___x_2978_ = lean_array_uget_borrowed(v_x_2957_, v___x_2977_);
lean_inc(v___x_2978_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 2, v___x_2978_);
v___x_2980_ = v___x_2963_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_key_2959_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_value_2960_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_array_uset(v_x_2957_, v___x_2977_, v___x_2980_);
v_x_2957_ = v___x_2981_;
v_x_2958_ = v_tail_2961_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2985_, lean_object* v_source_2986_, lean_object* v_target_2987_){
_start:
{
lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = lean_array_get_size(v_source_2986_);
v___x_2989_ = lean_nat_dec_lt(v_i_2985_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_dec_ref(v_source_2986_);
lean_dec(v_i_2985_);
return v_target_2987_;
}
else
{
lean_object* v_es_2990_; lean_object* v___x_2991_; lean_object* v_source_2992_; lean_object* v_target_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_es_2990_ = lean_array_fget(v_source_2986_, v_i_2985_);
v___x_2991_ = lean_box(0);
v_source_2992_ = lean_array_fset(v_source_2986_, v_i_2985_, v___x_2991_);
v_target_2993_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2987_, v_es_2990_);
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_nat_add(v_i_2985_, v___x_2994_);
lean_dec(v_i_2985_);
v_i_2985_ = v___x_2995_;
v_source_2986_ = v_source_2992_;
v_target_2987_ = v_target_2993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(lean_object* v_data_2997_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_nbuckets_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2998_ = lean_array_get_size(v_data_2997_);
v___x_2999_ = lean_unsigned_to_nat(2u);
v_nbuckets_3000_ = lean_nat_mul(v___x_2998_, v___x_2999_);
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_mk_array(v_nbuckets_3000_, v___x_3002_);
v___x_3004_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(v___x_3001_, v_data_2997_, v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object* v_m_3005_, lean_object* v_a_3006_, lean_object* v_b_3007_){
_start:
{
lean_object* v_size_3008_; lean_object* v_buckets_3009_; lean_object* v___x_3010_; uint64_t v___x_3011_; uint64_t v___x_3012_; uint64_t v___x_3013_; uint64_t v_fold_3014_; uint64_t v___x_3015_; uint64_t v___x_3016_; uint64_t v___x_3017_; size_t v___x_3018_; size_t v___x_3019_; size_t v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; lean_object* v_bkt_3023_; uint8_t v___x_3024_; 
v_size_3008_ = lean_ctor_get(v_m_3005_, 0);
v_buckets_3009_ = lean_ctor_get(v_m_3005_, 1);
v___x_3010_ = lean_array_get_size(v_buckets_3009_);
v___x_3011_ = l_Lean_Expr_hash(v_a_3006_);
v___x_3012_ = 32ULL;
v___x_3013_ = lean_uint64_shift_right(v___x_3011_, v___x_3012_);
v_fold_3014_ = lean_uint64_xor(v___x_3011_, v___x_3013_);
v___x_3015_ = 16ULL;
v___x_3016_ = lean_uint64_shift_right(v_fold_3014_, v___x_3015_);
v___x_3017_ = lean_uint64_xor(v_fold_3014_, v___x_3016_);
v___x_3018_ = lean_uint64_to_usize(v___x_3017_);
v___x_3019_ = lean_usize_of_nat(v___x_3010_);
v___x_3020_ = ((size_t)1ULL);
v___x_3021_ = lean_usize_sub(v___x_3019_, v___x_3020_);
v___x_3022_ = lean_usize_land(v___x_3018_, v___x_3021_);
v_bkt_3023_ = lean_array_uget_borrowed(v_buckets_3009_, v___x_3022_);
v___x_3024_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3006_, v_bkt_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3045_; 
lean_inc_ref(v_buckets_3009_);
lean_inc(v_size_3008_);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_m_3005_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; lean_object* v_unused_3047_; 
v_unused_3046_ = lean_ctor_get(v_m_3005_, 1);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_m_3005_, 0);
lean_dec(v_unused_3047_);
v___x_3026_ = v_m_3005_;
v_isShared_3027_ = v_isSharedCheck_3045_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v_m_3005_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3045_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v_size_x27_3029_; lean_object* v___x_3030_; lean_object* v_buckets_x27_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3028_ = lean_unsigned_to_nat(1u);
v_size_x27_3029_ = lean_nat_add(v_size_3008_, v___x_3028_);
lean_dec(v_size_3008_);
lean_inc(v_bkt_3023_);
v___x_3030_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3030_, 0, v_a_3006_);
lean_ctor_set(v___x_3030_, 1, v_b_3007_);
lean_ctor_set(v___x_3030_, 2, v_bkt_3023_);
v_buckets_x27_3031_ = lean_array_uset(v_buckets_3009_, v___x_3022_, v___x_3030_);
v___x_3032_ = lean_unsigned_to_nat(4u);
v___x_3033_ = lean_nat_mul(v_size_x27_3029_, v___x_3032_);
v___x_3034_ = lean_unsigned_to_nat(3u);
v___x_3035_ = lean_nat_div(v___x_3033_, v___x_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_array_get_size(v_buckets_x27_3031_);
v___x_3037_ = lean_nat_dec_le(v___x_3035_, v___x_3036_);
lean_dec(v___x_3035_);
if (v___x_3037_ == 0)
{
lean_object* v_val_3038_; lean_object* v___x_3040_; 
v_val_3038_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(v_buckets_x27_3031_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v_val_3038_);
lean_ctor_set(v___x_3026_, 0, v_size_x27_3029_);
v___x_3040_ = v___x_3026_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_size_x27_3029_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_val_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
else
{
lean_object* v___x_3043_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v_buckets_x27_3031_);
lean_ctor_set(v___x_3026_, 0, v_size_x27_3029_);
v___x_3043_ = v___x_3026_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_size_x27_3029_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_buckets_x27_3031_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_dec(v_b_3007_);
lean_dec_ref(v_a_3006_);
return v_m_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object* v_as_3048_, size_t v_sz_3049_, size_t v_i_3050_, lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_a_3060_; uint8_t v___x_3064_; 
v___x_3064_ = lean_usize_dec_lt(v_i_3050_, v_sz_3049_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_b_3051_);
return v___x_3065_;
}
else
{
lean_object* v_a_3066_; lean_object* v_fst_3067_; lean_object* v_snd_3068_; lean_object* v___x_3069_; 
v_a_3066_ = lean_array_uget_borrowed(v_as_3048_, v_i_3050_);
v_fst_3067_ = lean_ctor_get(v_a_3066_, 0);
v_snd_3068_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_snd_3068_);
lean_inc(v_fst_3067_);
v___x_3069_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_3067_, v_snd_3068_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v_fst_3071_; lean_object* v___x_3072_; lean_object* v_uninterpretedSymbols_3073_; lean_object* v_unusedRelevantHypotheses_3074_; lean_object* v_derivedEquations_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3100_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3069_, 1);
v_fst_3071_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_fst_3071_);
v___x_3072_ = lean_st_ref_take(v___y_3053_);
v_uninterpretedSymbols_3073_ = lean_ctor_get(v___x_3072_, 0);
v_unusedRelevantHypotheses_3074_ = lean_ctor_get(v___x_3072_, 1);
v_derivedEquations_3075_ = lean_ctor_get(v___x_3072_, 2);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3077_ = v___x_3072_;
v_isShared_3078_ = v_isSharedCheck_3100_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_derivedEquations_3075_);
lean_inc(v_unusedRelevantHypotheses_3074_);
lean_inc(v_uninterpretedSymbols_3073_);
lean_dec(v___x_3072_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3100_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = lean_array_push(v_derivedEquations_3075_, v_a_3070_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 2, v___x_3079_);
v___x_3081_ = v___x_3077_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_uninterpretedSymbols_3073_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_unusedRelevantHypotheses_3074_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_st_ref_set(v___y_3053_, v___x_3081_);
v___x_3083_ = lean_box(0);
if (lean_obj_tag(v_fst_3071_) == 1)
{
lean_object* v_fvarId_3084_; lean_object* v___x_3085_; 
v_fvarId_3084_ = lean_ctor_get(v_fst_3071_, 0);
lean_inc(v_fvarId_3084_);
lean_dec_ref_known(v_fst_3071_, 1);
v___x_3085_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvarId_3084_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v_fvarId_3084_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_dec_ref_known(v___x_3085_, 1);
v_a_3060_ = v___x_3083_;
goto v___jp_3059_;
}
else
{
return v___x_3085_;
}
}
else
{
lean_object* v___x_3086_; lean_object* v_uninterpretedSymbols_3087_; lean_object* v_unusedRelevantHypotheses_3088_; lean_object* v_derivedEquations_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3098_; 
v___x_3086_ = lean_st_ref_take(v___y_3053_);
v_uninterpretedSymbols_3087_ = lean_ctor_get(v___x_3086_, 0);
v_unusedRelevantHypotheses_3088_ = lean_ctor_get(v___x_3086_, 1);
v_derivedEquations_3089_ = lean_ctor_get(v___x_3086_, 2);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3091_ = v___x_3086_;
v_isShared_3092_ = v_isSharedCheck_3098_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_derivedEquations_3089_);
lean_inc(v_unusedRelevantHypotheses_3088_);
lean_inc(v_uninterpretedSymbols_3087_);
lean_dec(v___x_3086_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3098_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_uninterpretedSymbols_3087_, v_fst_3071_, v___x_3083_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_unusedRelevantHypotheses_3088_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_derivedEquations_3089_);
v___x_3095_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_st_ref_set(v___y_3053_, v___x_3095_);
v_a_3060_ = v___x_3083_;
goto v___jp_3059_;
}
}
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3069_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3069_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
v___jp_3059_:
{
size_t v___x_3061_; size_t v___x_3062_; 
v___x_3061_ = ((size_t)1ULL);
v___x_3062_ = lean_usize_add(v_i_3050_, v___x_3061_);
v_i_3050_ = v___x_3062_;
v_b_3051_ = v_a_3060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___boxed(lean_object* v_as_3109_, lean_object* v_sz_3110_, lean_object* v_i_3111_, lean_object* v_b_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
size_t v_sz_boxed_3120_; size_t v_i_boxed_3121_; lean_object* v_res_3122_; 
v_sz_boxed_3120_ = lean_unbox_usize(v_sz_3110_);
lean_dec(v_sz_3110_);
v_i_boxed_3121_ = lean_unbox_usize(v_i_3111_);
lean_dec(v_i_3111_);
v_res_3122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_as_3109_, v_sz_boxed_3120_, v_i_boxed_3121_, v_b_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec_ref(v_as_3109_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_equations_3130_; lean_object* v___x_3131_; size_t v_sz_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
v_equations_3130_ = lean_ctor_get(v_a_3123_, 2);
v___x_3131_ = lean_box(0);
v_sz_3132_ = lean_array_size(v_equations_3130_);
v___x_3133_ = ((size_t)0ULL);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_equations_3130_, v_sz_3132_, v___x_3133_, v___x_3131_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3142_);
v___x_3136_ = v___x_3134_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_dec(v___x_3134_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3131_);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3131_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
return v___x_3134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object* v_00_u03b2_3151_, lean_object* v_m_3152_, lean_object* v_a_3153_, lean_object* v_b_3154_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3152_, v_a_3153_, v_b_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object* v_00_u03b2_3156_, lean_object* v_a_3157_, lean_object* v_x_3158_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3157_, v_x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3160_, lean_object* v_a_3161_, lean_object* v_x_3162_){
_start:
{
uint8_t v_res_3163_; lean_object* v_r_3164_; 
v_res_3163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_3160_, v_a_3161_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec_ref(v_a_3161_);
v_r_3164_ = lean_box(v_res_3163_);
return v_r_3164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1(lean_object* v_00_u03b2_3165_, lean_object* v_data_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(v_data_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3168_, lean_object* v_i_3169_, lean_object* v_source_3170_, lean_object* v_target_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(v_i_3169_, v_source_3170_, v_target_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3173_, lean_object* v_x_3174_, lean_object* v_x_3175_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(v_x_3174_, v_x_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object* v_x_3177_, lean_object* v_x_3178_){
_start:
{
if (lean_obj_tag(v_x_3178_) == 0)
{
lean_inc(v_x_3177_);
return v_x_3177_;
}
else
{
lean_object* v_key_3179_; lean_object* v_tail_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_key_3179_ = lean_ctor_get(v_x_3178_, 0);
v_tail_3180_ = lean_ctor_get(v_x_3178_, 2);
v___x_3181_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_x_3177_, v_tail_3180_);
lean_inc(v_key_3179_);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_key_3179_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object* v_x_3183_, lean_object* v_x_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_x_3183_, v_x_3184_);
lean_dec(v_x_3184_);
lean_dec(v_x_3183_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(lean_object* v_as_3186_, size_t v_i_3187_, size_t v_stop_3188_, lean_object* v_b_3189_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_usize_dec_eq(v_i_3187_, v_stop_3188_);
if (v___x_3190_ == 0)
{
size_t v___x_3191_; size_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3191_ = ((size_t)1ULL);
v___x_3192_ = lean_usize_sub(v_i_3187_, v___x_3191_);
v___x_3193_ = lean_array_uget_borrowed(v_as_3186_, v___x_3192_);
v___x_3194_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_b_3189_, v___x_3193_);
lean_dec(v_b_3189_);
v_i_3187_ = v___x_3192_;
v_b_3189_ = v___x_3194_;
goto _start;
}
else
{
return v_b_3189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2___boxed(lean_object* v_as_3196_, lean_object* v_i_3197_, lean_object* v_stop_3198_, lean_object* v_b_3199_){
_start:
{
size_t v_i_boxed_3200_; size_t v_stop_boxed_3201_; lean_object* v_res_3202_; 
v_i_boxed_3200_ = lean_unbox_usize(v_i_3197_);
lean_dec(v_i_3197_);
v_stop_boxed_3201_ = lean_unbox_usize(v_stop_3198_);
lean_dec(v_stop_3198_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(v_as_3196_, v_i_boxed_3200_, v_stop_boxed_3201_, v_b_3199_);
lean_dec_ref(v_as_3196_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
if (lean_obj_tag(v_a_3203_) == 0)
{
lean_object* v___x_3205_; 
v___x_3205_ = l_List_reverse___redArg(v_a_3204_);
return v___x_3205_;
}
else
{
lean_object* v_head_3206_; lean_object* v_tail_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3216_; 
v_head_3206_ = lean_ctor_get(v_a_3203_, 0);
v_tail_3207_ = lean_ctor_get(v_a_3203_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_a_3203_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3209_ = v_a_3203_;
v_isShared_3210_ = v_isSharedCheck_3216_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_tail_3207_);
lean_inc(v_head_3206_);
lean_dec(v_a_3203_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3216_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = l_Lean_MessageData_ofExpr(v_head_3206_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 1, v_a_3204_);
lean_ctor_set(v___x_3209_, 0, v___x_3211_);
v___x_3213_ = v___x_3209_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_a_3204_);
v___x_3213_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
v_a_3203_ = v_tail_3207_;
v_a_3204_ = v___x_3213_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0));
v___x_3219_ = l_Lean_stringToMessageData(v___x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object* v_d_3220_){
_start:
{
lean_object* v___y_3222_; lean_object* v_uninterpretedSymbols_3229_; lean_object* v_size_3230_; lean_object* v_buckets_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v_uninterpretedSymbols_3229_ = lean_ctor_get(v_d_3220_, 0);
v_size_3230_ = lean_ctor_get(v_uninterpretedSymbols_3229_, 0);
v_buckets_3231_ = lean_ctor_get(v_uninterpretedSymbols_3229_, 1);
v___x_3232_ = lean_unsigned_to_nat(0u);
v___x_3233_ = lean_nat_dec_eq(v_size_3230_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3234_ = lean_box(0);
v___x_3235_ = lean_array_get_size(v_buckets_3231_);
v___x_3236_ = lean_nat_dec_lt(v___x_3232_, v___x_3235_);
if (v___x_3236_ == 0)
{
v___y_3222_ = v___x_3234_;
goto v___jp_3221_;
}
else
{
size_t v___x_3237_; size_t v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_usize_of_nat(v___x_3235_);
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(v_buckets_3231_, v___x_3237_, v___x_3238_, v___x_3234_);
v___y_3222_ = v___x_3239_;
goto v___jp_3221_;
}
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_box(0);
return v___x_3240_;
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
v___x_3224_ = lean_box(0);
v___x_3225_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v___y_3222_, v___x_3224_);
v___x_3226_ = l_Lean_MessageData_ofList(v___x_3225_);
v___x_3227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3223_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object* v_d_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_3241_);
lean_dec_ref(v_d_3241_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
if (lean_obj_tag(v_a_3243_) == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = l_List_reverse___redArg(v_a_3244_);
return v___x_3245_;
}
else
{
lean_object* v_head_3246_; lean_object* v_tail_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3256_; 
v_head_3246_ = lean_ctor_get(v_a_3243_, 0);
v_tail_3247_ = lean_ctor_get(v_a_3243_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_a_3243_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3249_ = v_a_3243_;
v_isShared_3250_ = v_isSharedCheck_3256_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_tail_3247_);
lean_inc(v_head_3246_);
lean_dec(v_a_3243_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3256_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = l_Lean_mkFVar(v_head_3246_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v_a_3244_);
lean_ctor_set(v___x_3249_, 0, v___x_3251_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_a_3244_);
v___x_3253_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
v_a_3243_ = v_tail_3247_;
v_a_3244_ = v___x_3253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object* v_x_3257_, lean_object* v_x_3258_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 0)
{
lean_inc(v_x_3257_);
return v_x_3257_;
}
else
{
lean_object* v_key_3259_; lean_object* v_tail_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_key_3259_ = lean_ctor_get(v_x_3258_, 0);
v_tail_3260_ = lean_ctor_get(v_x_3258_, 2);
v___x_3261_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3257_, v_tail_3260_);
lean_inc(v_key_3259_);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v_key_3259_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* v_x_3263_, lean_object* v_x_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3263_, v_x_3264_);
lean_dec(v_x_3264_);
lean_dec(v_x_3263_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object* v_as_3266_, size_t v_i_3267_, size_t v_stop_3268_, lean_object* v_b_3269_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_eq(v_i_3267_, v_stop_3268_);
if (v___x_3270_ == 0)
{
size_t v___x_3271_; size_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3271_ = ((size_t)1ULL);
v___x_3272_ = lean_usize_sub(v_i_3267_, v___x_3271_);
v___x_3273_ = lean_array_uget_borrowed(v_as_3266_, v___x_3272_);
v___x_3274_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_b_3269_, v___x_3273_);
lean_dec(v_b_3269_);
v_i_3267_ = v___x_3272_;
v_b_3269_ = v___x_3274_;
goto _start;
}
else
{
return v_b_3269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object* v_as_3276_, lean_object* v_i_3277_, lean_object* v_stop_3278_, lean_object* v_b_3279_){
_start:
{
size_t v_i_boxed_3280_; size_t v_stop_boxed_3281_; lean_object* v_res_3282_; 
v_i_boxed_3280_ = lean_unbox_usize(v_i_3277_);
lean_dec(v_i_3277_);
v_stop_boxed_3281_ = lean_unbox_usize(v_stop_3278_);
lean_dec(v_stop_3278_);
v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_3276_, v_i_boxed_3280_, v_stop_boxed_3281_, v_b_3279_);
lean_dec_ref(v_as_3276_);
return v_res_3282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0));
v___x_3285_ = l_Lean_stringToMessageData(v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object* v_d_3286_){
_start:
{
lean_object* v___y_3288_; lean_object* v_unusedRelevantHypotheses_3296_; lean_object* v_size_3297_; lean_object* v_buckets_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v_unusedRelevantHypotheses_3296_ = lean_ctor_get(v_d_3286_, 1);
v_size_3297_ = lean_ctor_get(v_unusedRelevantHypotheses_3296_, 0);
v_buckets_3298_ = lean_ctor_get(v_unusedRelevantHypotheses_3296_, 1);
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = lean_nat_dec_eq(v_size_3297_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_array_get_size(v_buckets_3298_);
v___x_3303_ = lean_nat_dec_lt(v___x_3299_, v___x_3302_);
if (v___x_3303_ == 0)
{
v___y_3288_ = v___x_3301_;
goto v___jp_3287_;
}
else
{
size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_usize_of_nat(v___x_3302_);
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_buckets_3298_, v___x_3304_, v___x_3305_, v___x_3301_);
v___y_3288_ = v___x_3306_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_box(0);
return v___x_3307_;
}
v___jp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v___y_3288_, v___x_3289_);
v___x_3291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
v___x_3292_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v___x_3290_, v___x_3289_);
v___x_3293_ = l_Lean_MessageData_ofList(v___x_3292_);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3291_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object* v_d_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_3308_);
lean_dec_ref(v_d_3308_);
return v_res_3309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0));
v___x_3321_ = l_Lean_stringToMessageData(v___x_3320_);
return v___x_3321_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2));
v___x_3324_ = l_Lean_stringToMessageData(v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object* v_as_3325_, size_t v_i_3326_, size_t v_stop_3327_, lean_object* v_b_3328_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_eq(v_i_3326_, v_stop_3327_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; size_t v___x_3336_; size_t v___x_3337_; 
v___x_3330_ = lean_array_uget_borrowed(v_as_3325_, v_i_3326_);
v___x_3331_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_b_3328_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
lean_inc(v___x_3330_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___x_3330_);
v___x_3334_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = ((size_t)1ULL);
v___x_3337_ = lean_usize_add(v_i_3326_, v___x_3336_);
v_i_3326_ = v___x_3337_;
v_b_3328_ = v___x_3335_;
goto _start;
}
else
{
return v_b_3328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object* v_as_3339_, lean_object* v_i_3340_, lean_object* v_stop_3341_, lean_object* v_b_3342_){
_start:
{
size_t v_i_boxed_3343_; size_t v_stop_boxed_3344_; lean_object* v_res_3345_; 
v_i_boxed_3343_ = lean_unbox_usize(v_i_3340_);
lean_dec(v_i_3340_);
v_stop_boxed_3344_ = lean_unbox_usize(v_stop_3341_);
lean_dec(v_stop_3341_);
v_res_3345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_3339_, v_i_boxed_3343_, v_stop_boxed_3344_, v_b_3342_);
lean_dec_ref(v_as_3339_);
return v_res_3345_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0));
v___x_3348_ = l_Lean_stringToMessageData(v___x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object* v_as_3349_, size_t v_i_3350_, size_t v_stop_3351_, lean_object* v_b_3352_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_eq(v_i_3350_, v_stop_3351_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3373_; 
v___x_3354_ = lean_array_uget(v_as_3349_, v_i_3350_);
v_fst_3355_ = lean_ctor_get(v___x_3354_, 0);
v_snd_3356_ = lean_ctor_get(v___x_3354_, 1);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3358_ = v___x_3354_;
v_isShared_3359_ = v_isSharedCheck_3373_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_inc(v_fst_3355_);
lean_dec(v___x_3354_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3373_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3360_ = l_Lean_MessageData_ofExpr(v_fst_3355_);
v___x_3361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
if (v_isShared_3359_ == 0)
{
lean_ctor_set_tag(v___x_3358_, 7);
lean_ctor_set(v___x_3358_, 1, v___x_3361_);
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3363_ = v___x_3358_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; size_t v___x_3369_; size_t v___x_3370_; 
v___x_3364_ = l_Lean_MessageData_ofExpr(v_snd_3356_);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_b_3352_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = ((size_t)1ULL);
v___x_3370_ = lean_usize_add(v_i_3350_, v___x_3369_);
v_i_3350_ = v___x_3370_;
v_b_3352_ = v___x_3368_;
goto _start;
}
}
}
else
{
return v_b_3352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object* v_as_3374_, lean_object* v_i_3375_, lean_object* v_stop_3376_, lean_object* v_b_3377_){
_start:
{
size_t v_i_boxed_3378_; size_t v_stop_boxed_3379_; lean_object* v_res_3380_; 
v_i_boxed_3378_ = lean_unbox_usize(v_i_3375_);
lean_dec(v_i_3375_);
v_stop_boxed_3379_ = lean_unbox_usize(v_stop_3376_);
lean_dec(v_stop_3376_);
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_3374_, v_i_boxed_3378_, v_stop_boxed_3379_, v_b_3377_);
lean_dec_ref(v_as_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object* v_a_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_){
_start:
{
if (lean_obj_tag(v_x_3383_) == 0)
{
lean_dec_ref(v_a_3381_);
return v_x_3382_;
}
else
{
lean_object* v_head_3384_; lean_object* v_tail_3385_; lean_object* v___x_3386_; 
v_head_3384_ = lean_ctor_get(v_x_3383_, 0);
lean_inc(v_head_3384_);
v_tail_3385_ = lean_ctor_get(v_x_3383_, 1);
lean_inc(v_tail_3385_);
lean_dec_ref_known(v_x_3383_, 2);
lean_inc_ref(v_a_3381_);
v___x_3386_ = lean_apply_1(v_head_3384_, v_a_3381_);
if (lean_obj_tag(v___x_3386_) == 1)
{
lean_object* v_val_3387_; lean_object* v___x_3388_; 
v_val_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_val_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = lean_array_push(v_x_3382_, v_val_3387_);
v_x_3382_ = v___x_3388_;
v_x_3383_ = v_tail_3385_;
goto _start;
}
else
{
lean_dec(v___x_3386_);
v_x_3383_ = v_tail_3385_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3399_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4);
v___x_3400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
return v___x_3401_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9);
v___x_3409_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v___x_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object* v_counterExample_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed), 7, 0);
v___x_3418_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_3417_, v_counterExample_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3470_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3470_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3470_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_err_3424_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0));
v___x_3450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers));
lean_inc(v_a_3419_);
v___x_3451_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3419_, v___x_3449_, v___x_3450_);
v___x_3452_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2);
v___x_3453_ = lean_array_get_size(v___x_3451_);
v___x_3454_ = lean_nat_dec_eq(v___x_3453_, v___x_3448_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___y_3457_; uint8_t v___x_3461_; 
v___x_3455_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5);
v___x_3461_ = lean_nat_dec_lt(v___x_3448_, v___x_3453_);
if (v___x_3461_ == 0)
{
lean_dec_ref(v___x_3451_);
v___y_3457_ = v___x_3452_;
goto v___jp_3456_;
}
else
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_nat_dec_le(v___x_3453_, v___x_3453_);
if (v___x_3462_ == 0)
{
if (v___x_3461_ == 0)
{
lean_dec_ref(v___x_3451_);
v___y_3457_ = v___x_3452_;
goto v___jp_3456_;
}
else
{
size_t v___x_3463_; size_t v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = ((size_t)0ULL);
v___x_3464_ = lean_usize_of_nat(v___x_3453_);
v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3451_, v___x_3463_, v___x_3464_, v___x_3452_);
lean_dec_ref(v___x_3451_);
v___y_3457_ = v___x_3465_;
goto v___jp_3456_;
}
}
else
{
size_t v___x_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = ((size_t)0ULL);
v___x_3467_ = lean_usize_of_nat(v___x_3453_);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3451_, v___x_3466_, v___x_3467_, v___x_3452_);
lean_dec_ref(v___x_3451_);
v___y_3457_ = v___x_3468_;
goto v___jp_3456_;
}
}
v___jp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3455_);
lean_ctor_set(v___x_3458_, 1, v___y_3457_);
v___x_3459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v_err_3424_ = v___x_3460_;
goto v___jp_3423_;
}
}
else
{
lean_object* v___x_3469_; 
lean_dec_ref(v___x_3451_);
v___x_3469_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10);
v_err_3424_ = v___x_3469_;
goto v___jp_3423_;
}
v___jp_3423_:
{
lean_object* v_derivedEquations_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v_derivedEquations_3425_ = lean_ctor_get(v_a_3419_, 2);
lean_inc_ref(v_derivedEquations_3425_);
lean_dec(v_a_3419_);
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_array_get_size(v_derivedEquations_3425_);
v___x_3428_ = lean_nat_dec_lt(v___x_3426_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v_derivedEquations_3425_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v_err_3424_);
v___x_3430_ = v___x_3421_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_err_3424_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_nat_dec_le(v___x_3427_, v___x_3427_);
if (v___x_3432_ == 0)
{
if (v___x_3428_ == 0)
{
lean_object* v___x_3434_; 
lean_dec_ref(v_derivedEquations_3425_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v_err_3424_);
v___x_3434_ = v___x_3421_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_err_3424_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___x_3427_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3425_, v___x_3436_, v___x_3437_, v_err_3424_);
lean_dec_ref(v_derivedEquations_3425_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3438_);
v___x_3440_ = v___x_3421_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
size_t v___x_3442_; size_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3442_ = ((size_t)0ULL);
v___x_3443_ = lean_usize_of_nat(v___x_3427_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3425_, v___x_3442_, v___x_3443_, v_err_3424_);
lean_dec_ref(v_derivedEquations_3425_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3444_);
v___x_3446_ = v___x_3421_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
v_a_3471_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3418_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3418_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object* v_counterExample_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
return v_res_3485_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

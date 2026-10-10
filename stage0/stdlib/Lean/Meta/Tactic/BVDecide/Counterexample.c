// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Counterexample
// Imports: import Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.Basic
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecType_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Tactic.BVDecide.Counterexample"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Meta.Tactic.BVDecide.reconstructCounterExample"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: bitIdx == currentBit\n      "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\n  - "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "The prover used the following expressions as uninterpreted functions:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "It abstracted the following unsupported expressions as opaque variables:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__3_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers___closed__3_value;
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Consider the following assignment:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "The prover found a potentially spurious counterexample:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "The prover found a counterexample, consider the following assignment:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8;
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(lean_object* v_a_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
else
{
lean_object* v_key_28_; lean_object* v_tail_29_; uint8_t v___x_30_; 
v_key_28_ = lean_ctor_get(v_x_26_, 0);
v_tail_29_ = lean_ctor_get(v_x_26_, 2);
v___x_30_ = lean_nat_dec_eq(v_key_28_, v_a_25_);
if (v___x_30_ == 0)
{
v_x_26_ = v_tail_29_;
goto _start;
}
else
{
return v___x_30_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_25_ = stack[0].m_obj;
lean_object* v_x_26_ = stack[1].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_25_, v_x_26_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg___boxed(lean_object* v_a_33_, lean_object* v_x_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_33_, v_x_34_);
lean_dec(v_x_34_);
lean_dec(v_a_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(lean_object* v_m_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_buckets_39_; lean_object* v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v_fold_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; size_t v___x_48_; size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; size_t v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v_buckets_39_ = lean_ctor_get(v_m_37_, 1);
v___x_40_ = lean_array_get_size(v_buckets_39_);
v___x_41_ = lean_uint64_of_nat(v_a_38_);
v___x_42_ = 32ULL;
v___x_43_ = lean_uint64_shift_right(v___x_41_, v___x_42_);
v_fold_44_ = lean_uint64_xor(v___x_41_, v___x_43_);
v___x_45_ = 16ULL;
v___x_46_ = lean_uint64_shift_right(v_fold_44_, v___x_45_);
v___x_47_ = lean_uint64_xor(v_fold_44_, v___x_46_);
v___x_48_ = lean_uint64_to_usize(v___x_47_);
v___x_49_ = lean_usize_of_nat(v___x_40_);
v___x_50_ = ((size_t)1ULL);
v___x_51_ = lean_usize_sub(v___x_49_, v___x_50_);
v___x_52_ = lean_usize_land(v___x_48_, v___x_51_);
v___x_53_ = lean_array_uget_borrowed(v_buckets_39_, v___x_52_);
v___x_54_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_38_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_37_ = stack[0].m_obj;
lean_object* v_a_38_ = stack[1].m_obj;
uint8_t v_res_55_;
v_res_55_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v_m_37_, v_a_38_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg___boxed(lean_object* v_m_56_, lean_object* v_a_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v_m_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_m_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object* v___x_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
if (lean_obj_tag(v_a_61_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v_a_62_);
return v___x_63_;
}
else
{
lean_object* v_value_64_; lean_object* v_snd_65_; lean_object* v_key_66_; lean_object* v_tail_67_; lean_object* v_fst_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_91_; 
v_value_64_ = lean_ctor_get(v_a_61_, 1);
lean_inc(v_value_64_);
v_snd_65_ = lean_ctor_get(v_value_64_, 1);
lean_inc(v_snd_65_);
v_key_66_ = lean_ctor_get(v_a_61_, 0);
lean_inc(v_key_66_);
v_tail_67_ = lean_ctor_get(v_a_61_, 2);
lean_inc(v_tail_67_);
lean_dec_ref_known(v_a_61_, 3);
v_fst_68_ = lean_ctor_get(v_value_64_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_value_64_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v_value_64_, 1);
lean_dec(v_unused_92_);
v___x_70_ = v_value_64_;
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_fst_68_);
lean_dec(v_value_64_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_90_; 
v_fst_72_ = lean_ctor_get(v_snd_65_, 0);
v_snd_73_ = lean_ctor_get(v_snd_65_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_snd_65_);
if (v_isSharedCheck_90_ == 0)
{
v___x_75_ = v_snd_65_;
v_isShared_76_ = v_isSharedCheck_90_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_snd_73_);
lean_inc(v_fst_72_);
lean_dec(v_snd_65_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_90_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint8_t v___x_77_; 
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v___x_60_, v_key_66_);
lean_dec(v_key_66_);
if (v___x_77_ == 0)
{
lean_object* v_value_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v_value_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = l_BitVec_ofNat(v_fst_68_, v_value_78_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_fst_68_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_80_);
lean_ctor_set(v___x_75_, 0, v_snd_73_);
v___x_82_ = v___x_75_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_snd_73_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_88_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_84_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_82_);
lean_ctor_set(v___x_70_, 0, v_fst_72_);
v___x_84_ = v___x_70_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_fst_72_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_87_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; 
v___x_85_ = lean_array_push(v_a_62_, v___x_84_);
v_a_61_ = v_tail_67_;
v_a_62_ = v___x_85_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_75_);
lean_dec(v_snd_73_);
lean_dec(v_fst_72_);
lean_del_object(v___x_70_);
lean_dec(v_fst_68_);
v_a_61_ = v_tail_67_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object* v___x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v___x_93_, v_a_94_, v_a_95_);
lean_dec_ref(v___x_93_);
return v_res_96_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object* v___x_97_, lean_object* v_as_98_, size_t v_sz_99_, size_t v_i_100_, lean_object* v_b_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = lean_usize_dec_lt(v_i_100_, v_sz_99_);
if (v___x_102_ == 0)
{
return v_b_101_;
}
else
{
lean_object* v_a_103_; lean_object* v___x_104_; 
v_a_103_ = lean_array_uget_borrowed(v_as_98_, v_i_100_);
lean_inc(v_a_103_);
v___x_104_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v___x_97_, v_a_103_, v_b_101_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
return v_a_105_;
}
else
{
lean_object* v_a_106_; size_t v___x_107_; size_t v___x_108_; 
v_a_106_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_104_, 1);
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_add(v_i_100_, v___x_107_);
v_i_100_ = v___x_108_;
v_b_101_ = v_a_106_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_97_ = stack[0].m_obj;
lean_object* v_as_98_ = stack[1].m_obj;
size_t v_sz_99_ = stack[2].m_num;
size_t v_i_100_ = stack[3].m_num;
lean_object* v_b_101_ = stack[4].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v___x_97_, v_as_98_, v_sz_99_, v_i_100_, v_b_101_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object* v___x_111_, lean_object* v_as_112_, lean_object* v_sz_113_, lean_object* v_i_114_, lean_object* v_b_115_){
_start:
{
size_t v_sz_boxed_116_; size_t v_i_boxed_117_; lean_object* v_res_118_; 
v_sz_boxed_116_ = lean_unbox_usize(v_sz_113_);
lean_dec(v_sz_113_);
v_i_boxed_117_ = lean_unbox_usize(v_i_114_);
lean_dec(v_i_114_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v___x_111_, v_as_112_, v_sz_boxed_116_, v_i_boxed_117_, v_b_115_);
lean_dec_ref(v_as_112_);
lean_dec_ref(v___x_111_);
return v_res_118_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_122_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__2));
v___x_123_ = lean_unsigned_to_nat(6u);
v___x_124_ = lean_unsigned_to_nat(61u);
v___x_125_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__1));
v___x_126_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0));
v___x_127_ = l_mkPanicMessageWithDecl(v___x_126_, v___x_125_, v___x_124_, v___x_123_, v___x_122_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object* v_init_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v_k_130_; lean_object* v_v_131_; lean_object* v_l_132_; lean_object* v_r_133_; lean_object* v___x_134_; 
v_k_130_ = lean_ctor_get(v_x_129_, 1);
v_v_131_ = lean_ctor_get(v_x_129_, 2);
v_l_132_ = lean_ctor_get(v_x_129_, 3);
v_r_133_ = lean_ctor_get(v_x_129_, 4);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(v_init_128_, v_l_132_);
if (lean_obj_tag(v___x_134_) == 0)
{
return v___x_134_;
}
else
{
lean_object* v_a_135_; lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_158_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
v_fst_136_ = lean_ctor_get(v_a_135_, 0);
v_snd_137_ = lean_ctor_get(v_a_135_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_a_135_);
if (v_isSharedCheck_158_ == 0)
{
v___x_139_ = v_a_135_;
v_isShared_140_ = v_isSharedCheck_158_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_inc(v_fst_136_);
lean_dec(v_a_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_158_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v_value_142_; uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_k_130_, v_snd_137_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_del_object(v___x_139_);
lean_dec(v_snd_137_);
lean_dec(v_fst_136_);
v___x_150_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3);
v___x_151_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(v___x_150_);
if (lean_obj_tag(v___x_151_) == 0)
{
return v___x_151_;
}
else
{
lean_object* v_a_152_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_init_128_ = v_a_152_;
v_x_129_ = v_r_133_;
goto _start;
}
}
else
{
uint8_t v___x_154_; 
v___x_154_ = lean_unbox(v_v_131_);
if (v___x_154_ == 0)
{
v_value_142_ = v_fst_136_;
goto v___jp_141_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_shiftl(v___x_155_, v_snd_137_);
v___x_157_ = lean_nat_lor(v_fst_136_, v___x_156_);
lean_dec(v___x_156_);
lean_dec(v_fst_136_);
v_value_142_ = v___x_157_;
goto v___jp_141_;
}
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_snd_137_, v___x_143_);
lean_dec(v_snd_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_144_);
lean_ctor_set(v___x_139_, 0, v_value_142_);
v___x_146_ = v___x_139_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_value_142_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
v_init_128_ = v___x_146_;
v_x_129_ = v_r_133_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v_init_128_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___boxed(lean_object* v_init_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(v_init_160_, v_x_161_);
lean_dec(v_x_161_);
return v_res_162_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0(void){
_start:
{
uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = 0;
v___x_164_ = l_Lean_instInhabitedExpr;
v___x_165_ = lean_box(v___x_163_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10(lean_object* v_msg_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_panic_fn_borrowed(v___x_170_, v_msg_167_);
lean_dec_ref_known(v___x_170_, 2);
return v___x_171_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_175_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__2));
v___x_176_ = lean_unsigned_to_nat(11u);
v___x_177_ = lean_unsigned_to_nat(163u);
v___x_178_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__1));
v___x_179_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__0));
v___x_180_ = l_mkPanicMessageWithDecl(v___x_179_, v___x_178_, v___x_177_, v___x_176_, v___x_175_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(lean_object* v_a_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3);
v___x_184_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10(v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_key_185_; lean_object* v_value_186_; lean_object* v_tail_187_; uint8_t v___x_188_; 
v_key_185_ = lean_ctor_get(v_x_182_, 0);
v_value_186_ = lean_ctor_get(v_x_182_, 1);
v_tail_187_ = lean_ctor_get(v_x_182_, 2);
v___x_188_ = lean_nat_dec_eq(v_key_185_, v_a_181_);
if (v___x_188_ == 0)
{
v_x_182_ = v_tail_187_;
goto _start;
}
else
{
lean_inc(v_value_186_);
return v_value_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___boxed(lean_object* v_a_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(v_a_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec(v_a_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object* v_m_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_buckets_195_; lean_object* v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v_fold_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_buckets_195_ = lean_ctor_get(v_m_193_, 1);
v___x_196_ = lean_array_get_size(v_buckets_195_);
v___x_197_ = lean_uint64_of_nat(v_a_194_);
v___x_198_ = 32ULL;
v___x_199_ = lean_uint64_shift_right(v___x_197_, v___x_198_);
v_fold_200_ = lean_uint64_xor(v___x_197_, v___x_199_);
v___x_201_ = 16ULL;
v___x_202_ = lean_uint64_shift_right(v_fold_200_, v___x_201_);
v___x_203_ = lean_uint64_xor(v_fold_200_, v___x_202_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = lean_usize_of_nat(v___x_196_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_sub(v___x_205_, v___x_206_);
v___x_208_ = lean_usize_land(v___x_204_, v___x_207_);
v___x_209_ = lean_array_uget_borrowed(v_buckets_195_, v___x_208_);
v___x_210_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(v_a_194_, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object* v_m_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_m_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_m_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object* v_atomsAssignment_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
if (lean_obj_tag(v_a_217_) == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_a_218_);
return v___x_219_;
}
else
{
lean_object* v_key_220_; lean_object* v_value_221_; lean_object* v_tail_222_; lean_object* v___y_224_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_a_258_; 
v_key_220_ = lean_ctor_get(v_a_217_, 0);
v_value_221_ = lean_ctor_get(v_a_217_, 1);
v_tail_222_ = lean_ctor_get(v_a_217_, 2);
v___x_256_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___closed__0));
v___x_257_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(v___x_256_, v_value_221_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref(v___x_257_);
v___y_224_ = v_a_258_;
goto v___jp_223_;
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v_snd_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_254_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_atomsAssignment_216_, v_key_220_);
v_snd_226_ = lean_ctor_get(v___x_225_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v___x_225_, 0);
lean_dec(v_unused_255_);
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_254_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_snd_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_254_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_253_; 
v_fst_230_ = lean_ctor_get(v_snd_226_, 0);
v_snd_231_ = lean_ctor_get(v_snd_226_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_snd_226_);
if (v_isSharedCheck_253_ == 0)
{
v___x_233_ = v_snd_226_;
v_isShared_234_ = v_isSharedCheck_253_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_snd_231_);
lean_inc(v_fst_230_);
lean_dec(v_snd_226_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_253_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_252_; 
v_fst_235_ = lean_ctor_get(v___y_224_, 0);
v_snd_236_ = lean_ctor_get(v___y_224_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v___y_224_);
if (v_isSharedCheck_252_ == 0)
{
v___x_238_ = v___y_224_;
v_isShared_239_ = v_isSharedCheck_252_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_snd_236_);
lean_inc(v_fst_235_);
lean_dec(v___y_224_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_252_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = l_BitVec_ofNat(v_snd_236_, v_fst_235_);
lean_dec(v_fst_235_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_240_);
lean_ctor_set(v___x_228_, 0, v_snd_236_);
v___x_242_ = v___x_228_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_snd_236_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_251_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_242_);
lean_ctor_set(v___x_238_, 0, v_snd_231_);
v___x_244_ = v___x_238_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_snd_231_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_250_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_244_);
v___x_246_ = v___x_233_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_249_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
v___x_247_ = lean_array_push(v_a_218_, v___x_246_);
v_a_217_ = v_tail_222_;
v_a_218_ = v___x_247_;
goto _start;
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___boxed(lean_object* v_atomsAssignment_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(v_atomsAssignment_259_, v_a_260_, v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_atomsAssignment_259_);
return v_res_262_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object* v_atomsAssignment_263_, lean_object* v_as_264_, size_t v_sz_265_, size_t v_i_266_, lean_object* v_b_267_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_lt(v_i_266_, v_sz_265_);
if (v___x_268_ == 0)
{
return v_b_267_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_array_uget_borrowed(v_as_264_, v_i_266_);
v___x_270_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(v_atomsAssignment_263_, v_a_269_, v_b_267_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
return v_a_271_;
}
else
{
lean_object* v_a_272_; size_t v___x_273_; size_t v___x_274_; 
v_a_272_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_270_, 1);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_add(v_i_266_, v___x_273_);
v_i_266_ = v___x_274_;
v_b_267_ = v_a_272_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_atomsAssignment_263_ = stack[0].m_obj;
lean_object* v_as_264_ = stack[1].m_obj;
size_t v_sz_265_ = stack[2].m_num;
size_t v_i_266_ = stack[3].m_num;
lean_object* v_b_267_ = stack[4].m_obj;
lean_object* v_res_276_;
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_atomsAssignment_263_, v_as_264_, v_sz_265_, v_i_266_, v_b_267_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object* v_atomsAssignment_277_, lean_object* v_as_278_, lean_object* v_sz_279_, lean_object* v_i_280_, lean_object* v_b_281_){
_start:
{
size_t v_sz_boxed_282_; size_t v_i_boxed_283_; lean_object* v_res_284_; 
v_sz_boxed_282_ = lean_unbox_usize(v_sz_279_);
lean_dec(v_sz_279_);
v_i_boxed_283_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_atomsAssignment_277_, v_as_278_, v_sz_boxed_282_, v_i_boxed_283_, v_b_281_);
lean_dec_ref(v_as_278_);
lean_dec_ref(v_atomsAssignment_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(lean_object* v_k_285_, lean_object* v_v_286_, lean_object* v_t_287_){
_start:
{
if (lean_obj_tag(v_t_287_) == 0)
{
lean_object* v_size_288_; lean_object* v_k_289_; lean_object* v_v_290_; lean_object* v_l_291_; lean_object* v_r_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_573_; 
v_size_288_ = lean_ctor_get(v_t_287_, 0);
v_k_289_ = lean_ctor_get(v_t_287_, 1);
v_v_290_ = lean_ctor_get(v_t_287_, 2);
v_l_291_ = lean_ctor_get(v_t_287_, 3);
v_r_292_ = lean_ctor_get(v_t_287_, 4);
v_isSharedCheck_573_ = !lean_is_exclusive(v_t_287_);
if (v_isSharedCheck_573_ == 0)
{
v___x_294_ = v_t_287_;
v_isShared_295_ = v_isSharedCheck_573_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_r_292_);
lean_inc(v_l_291_);
lean_inc(v_v_290_);
lean_inc(v_k_289_);
lean_inc(v_size_288_);
lean_dec(v_t_287_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_573_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_lt(v_k_285_, v_k_289_);
if (v___x_296_ == 0)
{
uint8_t v___x_297_; 
v___x_297_ = lean_nat_dec_eq(v_k_285_, v_k_289_);
if (v___x_297_ == 0)
{
lean_object* v_impl_298_; lean_object* v___x_299_; 
lean_dec(v_size_288_);
v_impl_298_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_k_285_, v_v_286_, v_r_292_);
v___x_299_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_291_) == 0)
{
lean_object* v_size_300_; lean_object* v_size_301_; lean_object* v_k_302_; lean_object* v_v_303_; lean_object* v_l_304_; lean_object* v_r_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_size_300_ = lean_ctor_get(v_l_291_, 0);
v_size_301_ = lean_ctor_get(v_impl_298_, 0);
v_k_302_ = lean_ctor_get(v_impl_298_, 1);
v_v_303_ = lean_ctor_get(v_impl_298_, 2);
v_l_304_ = lean_ctor_get(v_impl_298_, 3);
lean_inc(v_l_304_);
v_r_305_ = lean_ctor_get(v_impl_298_, 4);
v___x_306_ = lean_unsigned_to_nat(3u);
v___x_307_ = lean_nat_mul(v___x_306_, v_size_300_);
v___x_308_ = lean_nat_dec_lt(v___x_307_, v_size_301_);
lean_dec(v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v_l_304_);
v___x_309_ = lean_nat_add(v___x_299_, v_size_300_);
v___x_310_ = lean_nat_add(v___x_309_, v_size_301_);
lean_dec(v___x_309_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v_impl_298_);
lean_ctor_set(v___x_294_, 0, v___x_310_);
v___x_312_ = v___x_294_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_l_291_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_impl_298_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_377_; 
lean_inc(v_r_305_);
lean_inc(v_v_303_);
lean_inc(v_k_302_);
lean_inc(v_size_301_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_impl_298_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_378_ = lean_ctor_get(v_impl_298_, 4);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_impl_298_, 3);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_impl_298_, 2);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_impl_298_, 1);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_impl_298_, 0);
lean_dec(v_unused_382_);
v___x_315_ = v_impl_298_;
v_isShared_316_ = v_isSharedCheck_377_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_impl_298_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_377_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_size_317_; lean_object* v_k_318_; lean_object* v_v_319_; lean_object* v_l_320_; lean_object* v_r_321_; lean_object* v_size_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_size_317_ = lean_ctor_get(v_l_304_, 0);
v_k_318_ = lean_ctor_get(v_l_304_, 1);
v_v_319_ = lean_ctor_get(v_l_304_, 2);
v_l_320_ = lean_ctor_get(v_l_304_, 3);
v_r_321_ = lean_ctor_get(v_l_304_, 4);
v_size_322_ = lean_ctor_get(v_r_305_, 0);
v___x_323_ = lean_unsigned_to_nat(2u);
v___x_324_ = lean_nat_mul(v___x_323_, v_size_322_);
v___x_325_ = lean_nat_dec_lt(v_size_317_, v___x_324_);
lean_dec(v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_353_; 
lean_inc(v_r_321_);
lean_inc(v_l_320_);
lean_inc(v_v_319_);
lean_inc(v_k_318_);
v_isSharedCheck_353_ = !lean_is_exclusive(v_l_304_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_354_ = lean_ctor_get(v_l_304_, 4);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_l_304_, 3);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_l_304_, 2);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_l_304_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_l_304_, 0);
lean_dec(v_unused_358_);
v___x_327_ = v_l_304_;
v_isShared_328_ = v_isSharedCheck_353_;
goto v_resetjp_326_;
}
else
{
lean_dec(v_l_304_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_353_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_343_; 
v___x_329_ = lean_nat_add(v___x_299_, v_size_300_);
v___x_330_ = lean_nat_add(v___x_329_, v_size_301_);
lean_dec(v_size_301_);
if (lean_obj_tag(v_l_320_) == 0)
{
lean_object* v_size_351_; 
v_size_351_ = lean_ctor_get(v_l_320_, 0);
lean_inc(v_size_351_);
v___y_343_ = v_size_351_;
goto v___jp_342_;
}
else
{
lean_object* v___x_352_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___y_343_ = v___x_352_;
goto v___jp_342_;
}
v___jp_331_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_nat_add(v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec(v___y_333_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 4, v_r_305_);
lean_ctor_set(v___x_327_, 3, v_r_321_);
lean_ctor_set(v___x_327_, 2, v_v_303_);
lean_ctor_set(v___x_327_, 1, v_k_302_);
lean_ctor_set(v___x_327_, 0, v___x_335_);
v___x_337_ = v___x_327_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_302_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_303_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_r_321_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_r_305_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 4, v___x_337_);
lean_ctor_set(v___x_315_, 3, v___y_332_);
lean_ctor_set(v___x_315_, 2, v_v_319_);
lean_ctor_set(v___x_315_, 1, v_k_318_);
lean_ctor_set(v___x_315_, 0, v___x_330_);
v___x_339_ = v___x_315_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_k_318_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_v_319_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v___y_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_nat_add(v___x_329_, v___y_343_);
lean_dec(v___y_343_);
lean_dec(v___x_329_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v_l_320_);
lean_ctor_set(v___x_294_, 0, v___x_344_);
v___x_346_ = v___x_294_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_l_291_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_l_320_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; 
v___x_347_ = lean_nat_add(v___x_299_, v_size_322_);
if (lean_obj_tag(v_r_321_) == 0)
{
lean_object* v_size_348_; 
v_size_348_ = lean_ctor_get(v_r_321_, 0);
lean_inc(v_size_348_);
v___y_332_ = v___x_346_;
v___y_333_ = v___x_347_;
v___y_334_ = v_size_348_;
goto v___jp_331_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___y_332_ = v___x_346_;
v___y_333_ = v___x_347_;
v___y_334_ = v___x_349_;
goto v___jp_331_;
}
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
lean_del_object(v___x_294_);
v___x_359_ = lean_nat_add(v___x_299_, v_size_300_);
v___x_360_ = lean_nat_add(v___x_359_, v_size_301_);
lean_dec(v_size_301_);
v___x_361_ = lean_nat_add(v___x_359_, v_size_317_);
lean_dec(v___x_359_);
lean_inc_ref(v_l_291_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 4, v_l_304_);
lean_ctor_set(v___x_315_, 3, v_l_291_);
lean_ctor_set(v___x_315_, 2, v_v_290_);
lean_ctor_set(v___x_315_, 1, v_k_289_);
lean_ctor_set(v___x_315_, 0, v___x_361_);
v___x_363_ = v___x_315_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_l_291_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_l_304_);
v___x_363_ = v_reuseFailAlloc_376_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_isSharedCheck_370_ = !lean_is_exclusive(v_l_291_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_371_ = lean_ctor_get(v_l_291_, 4);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_l_291_, 3);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_l_291_, 2);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_l_291_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_l_291_, 0);
lean_dec(v_unused_375_);
v___x_365_ = v_l_291_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_dec(v_l_291_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_r_305_);
lean_ctor_set(v___x_365_, 3, v___x_363_);
lean_ctor_set(v___x_365_, 2, v_v_303_);
lean_ctor_set(v___x_365_, 1, v_k_302_);
lean_ctor_set(v___x_365_, 0, v___x_360_);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_302_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_303_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_r_305_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_383_; 
v_l_383_ = lean_ctor_get(v_impl_298_, 3);
lean_inc(v_l_383_);
if (lean_obj_tag(v_l_383_) == 0)
{
lean_object* v_r_384_; lean_object* v_k_385_; lean_object* v_v_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_409_; 
v_r_384_ = lean_ctor_get(v_impl_298_, 4);
v_k_385_ = lean_ctor_get(v_impl_298_, 1);
v_v_386_ = lean_ctor_get(v_impl_298_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v_impl_298_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_impl_298_, 3);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_impl_298_, 0);
lean_dec(v_unused_411_);
v___x_388_ = v_impl_298_;
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_r_384_);
lean_inc(v_v_386_);
lean_inc(v_k_385_);
lean_dec(v_impl_298_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_k_390_; lean_object* v_v_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_405_; 
v_k_390_ = lean_ctor_get(v_l_383_, 1);
v_v_391_ = lean_ctor_get(v_l_383_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_l_383_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_406_ = lean_ctor_get(v_l_383_, 4);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_l_383_, 3);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_l_383_, 0);
lean_dec(v_unused_408_);
v___x_393_ = v_l_383_;
v_isShared_394_ = v_isSharedCheck_405_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_v_391_);
lean_inc(v_k_390_);
lean_dec(v_l_383_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_405_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_384_, 2);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 4, v_r_384_);
lean_ctor_set(v___x_393_, 3, v_r_384_);
lean_ctor_set(v___x_393_, 2, v_v_290_);
lean_ctor_set(v___x_393_, 1, v_k_289_);
lean_ctor_set(v___x_393_, 0, v___x_299_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_r_384_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_r_384_);
v___x_397_ = v_reuseFailAlloc_404_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_399_; 
lean_inc(v_r_384_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 3, v_r_384_);
lean_ctor_set(v___x_388_, 0, v___x_299_);
v___x_399_ = v___x_388_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_k_385_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_v_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_r_384_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_r_384_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v___x_399_);
lean_ctor_set(v___x_294_, 3, v___x_397_);
lean_ctor_set(v___x_294_, 2, v_v_391_);
lean_ctor_set(v___x_294_, 1, v_k_390_);
lean_ctor_set(v___x_294_, 0, v___x_395_);
v___x_401_ = v___x_294_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_390_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_v_391_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
else
{
lean_object* v_r_412_; 
v_r_412_ = lean_ctor_get(v_impl_298_, 4);
lean_inc(v_r_412_);
if (lean_obj_tag(v_r_412_) == 0)
{
lean_object* v_k_413_; lean_object* v_v_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
v_k_413_ = lean_ctor_get(v_impl_298_, 1);
v_v_414_ = lean_ctor_get(v_impl_298_, 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v_impl_298_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_426_ = lean_ctor_get(v_impl_298_, 4);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_impl_298_, 3);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_impl_298_, 0);
lean_dec(v_unused_428_);
v___x_416_ = v_impl_298_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_v_414_);
lean_inc(v_k_413_);
lean_dec(v_impl_298_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_unsigned_to_nat(3u);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 4, v_l_383_);
lean_ctor_set(v___x_416_, 2, v_v_290_);
lean_ctor_set(v___x_416_, 1, v_k_289_);
lean_ctor_set(v___x_416_, 0, v___x_299_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_l_383_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_l_383_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v_r_412_);
lean_ctor_set(v___x_294_, 3, v___x_420_);
lean_ctor_set(v___x_294_, 2, v_v_414_);
lean_ctor_set(v___x_294_, 1, v_k_413_);
lean_ctor_set(v___x_294_, 0, v___x_418_);
v___x_422_ = v___x_294_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_k_413_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_v_414_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_r_412_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(2u);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v_impl_298_);
lean_ctor_set(v___x_294_, 3, v_r_412_);
lean_ctor_set(v___x_294_, 0, v___x_429_);
v___x_431_ = v___x_294_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_r_412_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_impl_298_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v___x_434_; 
lean_dec(v_v_290_);
lean_dec(v_k_289_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 2, v_v_286_);
lean_ctor_set(v___x_294_, 1, v_k_285_);
v___x_434_ = v___x_294_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_size_288_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_l_291_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_r_292_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_impl_436_; lean_object* v___x_437_; 
lean_dec(v_size_288_);
v_impl_436_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_k_285_, v_v_286_, v_l_291_);
v___x_437_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_292_) == 0)
{
lean_object* v_size_438_; lean_object* v_size_439_; lean_object* v_k_440_; lean_object* v_v_441_; lean_object* v_l_442_; lean_object* v_r_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_size_438_ = lean_ctor_get(v_r_292_, 0);
v_size_439_ = lean_ctor_get(v_impl_436_, 0);
v_k_440_ = lean_ctor_get(v_impl_436_, 1);
v_v_441_ = lean_ctor_get(v_impl_436_, 2);
v_l_442_ = lean_ctor_get(v_impl_436_, 3);
v_r_443_ = lean_ctor_get(v_impl_436_, 4);
lean_inc(v_r_443_);
v___x_444_ = lean_unsigned_to_nat(3u);
v___x_445_ = lean_nat_mul(v___x_444_, v_size_438_);
v___x_446_ = lean_nat_dec_lt(v___x_445_, v_size_439_);
lean_dec(v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
lean_dec(v_r_443_);
v___x_447_ = lean_nat_add(v___x_437_, v_size_439_);
v___x_448_ = lean_nat_add(v___x_447_, v_size_438_);
lean_dec(v___x_447_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 3, v_impl_436_);
lean_ctor_set(v___x_294_, 0, v___x_448_);
v___x_450_ = v___x_294_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_impl_436_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_r_292_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_517_; 
lean_inc(v_l_442_);
lean_inc(v_v_441_);
lean_inc(v_k_440_);
lean_inc(v_size_439_);
v_isSharedCheck_517_ = !lean_is_exclusive(v_impl_436_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; lean_object* v_unused_522_; 
v_unused_518_ = lean_ctor_get(v_impl_436_, 4);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_impl_436_, 3);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_impl_436_, 2);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_impl_436_, 1);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_impl_436_, 0);
lean_dec(v_unused_522_);
v___x_453_ = v_impl_436_;
v_isShared_454_ = v_isSharedCheck_517_;
goto v_resetjp_452_;
}
else
{
lean_dec(v_impl_436_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_517_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_size_455_; lean_object* v_size_456_; lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v_l_459_; lean_object* v_r_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_size_455_ = lean_ctor_get(v_l_442_, 0);
v_size_456_ = lean_ctor_get(v_r_443_, 0);
v_k_457_ = lean_ctor_get(v_r_443_, 1);
v_v_458_ = lean_ctor_get(v_r_443_, 2);
v_l_459_ = lean_ctor_get(v_r_443_, 3);
v_r_460_ = lean_ctor_get(v_r_443_, 4);
v___x_461_ = lean_unsigned_to_nat(2u);
v___x_462_ = lean_nat_mul(v___x_461_, v_size_455_);
v___x_463_ = lean_nat_dec_lt(v_size_456_, v___x_462_);
lean_dec(v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_492_; 
lean_inc(v_r_460_);
lean_inc(v_l_459_);
lean_inc(v_v_458_);
lean_inc(v_k_457_);
v_isSharedCheck_492_ = !lean_is_exclusive(v_r_443_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_493_ = lean_ctor_get(v_r_443_, 4);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_r_443_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_r_443_, 2);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_r_443_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_r_443_, 0);
lean_dec(v_unused_497_);
v___x_465_ = v_r_443_;
v_isShared_466_ = v_isSharedCheck_492_;
goto v_resetjp_464_;
}
else
{
lean_dec(v_r_443_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_492_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___x_480_; lean_object* v___y_482_; 
v___x_467_ = lean_nat_add(v___x_437_, v_size_439_);
lean_dec(v_size_439_);
v___x_468_ = lean_nat_add(v___x_467_, v_size_438_);
lean_dec(v___x_467_);
v___x_480_ = lean_nat_add(v___x_437_, v_size_455_);
if (lean_obj_tag(v_l_459_) == 0)
{
lean_object* v_size_490_; 
v_size_490_ = lean_ctor_get(v_l_459_, 0);
lean_inc(v_size_490_);
v___y_482_ = v_size_490_;
goto v___jp_481_;
}
else
{
lean_object* v___x_491_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___y_482_ = v___x_491_;
goto v___jp_481_;
}
v___jp_469_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_nat_add(v___y_470_, v___y_472_);
lean_dec(v___y_472_);
lean_dec(v___y_470_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 4, v_r_292_);
lean_ctor_set(v___x_465_, 3, v_r_460_);
lean_ctor_set(v___x_465_, 2, v_v_290_);
lean_ctor_set(v___x_465_, 1, v_k_289_);
lean_ctor_set(v___x_465_, 0, v___x_473_);
v___x_475_ = v___x_465_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_r_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_r_292_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v___x_475_);
lean_ctor_set(v___x_453_, 3, v___y_471_);
lean_ctor_set(v___x_453_, 2, v_v_458_);
lean_ctor_set(v___x_453_, 1, v_k_457_);
lean_ctor_set(v___x_453_, 0, v___x_468_);
v___x_477_ = v___x_453_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_k_457_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_v_458_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v___y_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_nat_add(v___x_480_, v___y_482_);
lean_dec(v___y_482_);
lean_dec(v___x_480_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v_l_459_);
lean_ctor_set(v___x_294_, 3, v_l_442_);
lean_ctor_set(v___x_294_, 2, v_v_441_);
lean_ctor_set(v___x_294_, 1, v_k_440_);
lean_ctor_set(v___x_294_, 0, v___x_483_);
v___x_485_ = v___x_294_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_440_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_441_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_l_442_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_l_459_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; 
v___x_486_ = lean_nat_add(v___x_437_, v_size_438_);
if (lean_obj_tag(v_r_460_) == 0)
{
lean_object* v_size_487_; 
v_size_487_ = lean_ctor_get(v_r_460_, 0);
lean_inc(v_size_487_);
v___y_470_ = v___x_486_;
v___y_471_ = v___x_485_;
v___y_472_ = v_size_487_;
goto v___jp_469_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___y_470_ = v___x_486_;
v___y_471_ = v___x_485_;
v___y_472_ = v___x_488_;
goto v___jp_469_;
}
}
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_del_object(v___x_294_);
v___x_498_ = lean_nat_add(v___x_437_, v_size_439_);
lean_dec(v_size_439_);
v___x_499_ = lean_nat_add(v___x_498_, v_size_438_);
lean_dec(v___x_498_);
v___x_500_ = lean_nat_add(v___x_437_, v_size_438_);
v___x_501_ = lean_nat_add(v___x_500_, v_size_456_);
lean_dec(v___x_500_);
lean_inc_ref(v_r_292_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_r_292_);
lean_ctor_set(v___x_453_, 3, v_r_443_);
lean_ctor_set(v___x_453_, 2, v_v_290_);
lean_ctor_set(v___x_453_, 1, v_k_289_);
lean_ctor_set(v___x_453_, 0, v___x_501_);
v___x_503_ = v___x_453_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_r_443_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_r_292_);
v___x_503_ = v_reuseFailAlloc_516_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_isSharedCheck_510_ = !lean_is_exclusive(v_r_292_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; lean_object* v_unused_512_; lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; 
v_unused_511_ = lean_ctor_get(v_r_292_, 4);
lean_dec(v_unused_511_);
v_unused_512_ = lean_ctor_get(v_r_292_, 3);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_r_292_, 2);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_r_292_, 1);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_r_292_, 0);
lean_dec(v_unused_515_);
v___x_505_ = v_r_292_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_dec(v_r_292_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 4, v___x_503_);
lean_ctor_set(v___x_505_, 3, v_l_442_);
lean_ctor_set(v___x_505_, 2, v_v_441_);
lean_ctor_set(v___x_505_, 1, v_k_440_);
lean_ctor_set(v___x_505_, 0, v___x_499_);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_440_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_441_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_l_442_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v___x_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_523_; 
v_l_523_ = lean_ctor_get(v_impl_436_, 3);
if (lean_obj_tag(v_l_523_) == 0)
{
lean_object* v_r_524_; lean_object* v_k_525_; lean_object* v_v_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_537_; 
lean_inc_ref(v_l_523_);
v_r_524_ = lean_ctor_get(v_impl_436_, 4);
v_k_525_ = lean_ctor_get(v_impl_436_, 1);
v_v_526_ = lean_ctor_get(v_impl_436_, 2);
v_isSharedCheck_537_ = !lean_is_exclusive(v_impl_436_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; lean_object* v_unused_539_; 
v_unused_538_ = lean_ctor_get(v_impl_436_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_impl_436_, 0);
lean_dec(v_unused_539_);
v___x_528_ = v_impl_436_;
v_isShared_529_ = v_isSharedCheck_537_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_r_524_);
lean_inc(v_v_526_);
lean_inc(v_k_525_);
lean_dec(v_impl_436_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_537_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_524_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 3, v_r_524_);
lean_ctor_set(v___x_528_, 2, v_v_290_);
lean_ctor_set(v___x_528_, 1, v_k_289_);
lean_ctor_set(v___x_528_, 0, v___x_437_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_r_524_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v_r_524_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v___x_532_);
lean_ctor_set(v___x_294_, 3, v_l_523_);
lean_ctor_set(v___x_294_, 2, v_v_526_);
lean_ctor_set(v___x_294_, 1, v_k_525_);
lean_ctor_set(v___x_294_, 0, v___x_530_);
v___x_534_ = v___x_294_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_k_525_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_v_526_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_l_523_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_r_540_; 
v_r_540_ = lean_ctor_get(v_impl_436_, 4);
lean_inc(v_r_540_);
if (lean_obj_tag(v_r_540_) == 0)
{
lean_object* v_k_541_; lean_object* v_v_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_565_; 
lean_inc(v_l_523_);
v_k_541_ = lean_ctor_get(v_impl_436_, 1);
v_v_542_ = lean_ctor_get(v_impl_436_, 2);
v_isSharedCheck_565_ = !lean_is_exclusive(v_impl_436_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_566_ = lean_ctor_get(v_impl_436_, 4);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_impl_436_, 3);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_impl_436_, 0);
lean_dec(v_unused_568_);
v___x_544_ = v_impl_436_;
v_isShared_545_ = v_isSharedCheck_565_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_v_542_);
lean_inc(v_k_541_);
lean_dec(v_impl_436_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_565_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_k_546_; lean_object* v_v_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_561_; 
v_k_546_ = lean_ctor_get(v_r_540_, 1);
v_v_547_ = lean_ctor_get(v_r_540_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v_r_540_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; lean_object* v_unused_564_; 
v_unused_562_ = lean_ctor_get(v_r_540_, 4);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_r_540_, 3);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_r_540_, 0);
lean_dec(v_unused_564_);
v___x_549_ = v_r_540_;
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_v_547_);
lean_inc(v_k_546_);
lean_dec(v_r_540_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_unsigned_to_nat(3u);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 4, v_l_523_);
lean_ctor_set(v___x_549_, 3, v_l_523_);
lean_ctor_set(v___x_549_, 2, v_v_542_);
lean_ctor_set(v___x_549_, 1, v_k_541_);
lean_ctor_set(v___x_549_, 0, v___x_437_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_541_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_542_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_l_523_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_l_523_);
v___x_553_ = v_reuseFailAlloc_560_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 4, v_l_523_);
lean_ctor_set(v___x_544_, 2, v_v_290_);
lean_ctor_set(v___x_544_, 1, v_k_289_);
lean_ctor_set(v___x_544_, 0, v___x_437_);
v___x_555_ = v___x_544_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_l_523_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_l_523_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v___x_555_);
lean_ctor_set(v___x_294_, 3, v___x_553_);
lean_ctor_set(v___x_294_, 2, v_v_547_);
lean_ctor_set(v___x_294_, 1, v_k_546_);
lean_ctor_set(v___x_294_, 0, v___x_551_);
v___x_557_ = v___x_294_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_k_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_v_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(2u);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v_r_540_);
lean_ctor_set(v___x_294_, 3, v_impl_436_);
lean_ctor_set(v___x_294_, 0, v___x_569_);
v___x_571_ = v___x_294_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_impl_436_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_r_540_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_k_285_);
lean_ctor_set(v___x_575_, 2, v_v_286_);
lean_ctor_set(v___x_575_, 3, v_t_287_);
lean_ctor_set(v___x_575_, 4, v_t_287_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(lean_object* v_a_576_, lean_object* v_fallback_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_inc(v_fallback_577_);
return v_fallback_577_;
}
else
{
lean_object* v_key_579_; lean_object* v_value_580_; lean_object* v_tail_581_; uint8_t v___x_582_; 
v_key_579_ = lean_ctor_get(v_x_578_, 0);
v_value_580_ = lean_ctor_get(v_x_578_, 1);
v_tail_581_ = lean_ctor_get(v_x_578_, 2);
v___x_582_ = lean_nat_dec_eq(v_key_579_, v_a_576_);
if (v___x_582_ == 0)
{
v_x_578_ = v_tail_581_;
goto _start;
}
else
{
lean_inc(v_value_580_);
return v_value_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg___boxed(lean_object* v_a_584_, lean_object* v_fallback_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_a_584_, v_fallback_585_, v_x_586_);
lean_dec(v_x_586_);
lean_dec(v_fallback_585_);
lean_dec(v_a_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(lean_object* v_m_588_, lean_object* v_a_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v_buckets_591_; lean_object* v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v_fold_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_buckets_591_ = lean_ctor_get(v_m_588_, 1);
v___x_592_ = lean_array_get_size(v_buckets_591_);
v___x_593_ = lean_uint64_of_nat(v_a_589_);
v___x_594_ = 32ULL;
v___x_595_ = lean_uint64_shift_right(v___x_593_, v___x_594_);
v_fold_596_ = lean_uint64_xor(v___x_593_, v___x_595_);
v___x_597_ = 16ULL;
v___x_598_ = lean_uint64_shift_right(v_fold_596_, v___x_597_);
v___x_599_ = lean_uint64_xor(v_fold_596_, v___x_598_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = lean_usize_of_nat(v___x_592_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_sub(v___x_601_, v___x_602_);
v___x_604_ = lean_usize_land(v___x_600_, v___x_603_);
v___x_605_ = lean_array_uget_borrowed(v_buckets_591_, v___x_604_);
v___x_606_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_a_589_, v_fallback_590_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg___boxed(lean_object* v_m_607_, lean_object* v_a_608_, lean_object* v_fallback_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(v_m_607_, v_a_608_, v_fallback_609_);
lean_dec(v_fallback_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_m_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
return v_x_611_;
}
else
{
lean_object* v_key_613_; lean_object* v_value_614_; lean_object* v_tail_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_638_; 
v_key_613_ = lean_ctor_get(v_x_612_, 0);
v_value_614_ = lean_ctor_get(v_x_612_, 1);
v_tail_615_ = lean_ctor_get(v_x_612_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_638_ == 0)
{
v___x_617_ = v_x_612_;
v_isShared_618_ = v_isSharedCheck_638_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_tail_615_);
lean_inc(v_value_614_);
lean_inc(v_key_613_);
lean_dec(v_x_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_638_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; uint64_t v___x_620_; uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v_fold_623_; uint64_t v___x_624_; uint64_t v___x_625_; uint64_t v___x_626_; size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_619_ = lean_array_get_size(v_x_611_);
v___x_620_ = lean_uint64_of_nat(v_key_613_);
v___x_621_ = 32ULL;
v___x_622_ = lean_uint64_shift_right(v___x_620_, v___x_621_);
v_fold_623_ = lean_uint64_xor(v___x_620_, v___x_622_);
v___x_624_ = 16ULL;
v___x_625_ = lean_uint64_shift_right(v_fold_623_, v___x_624_);
v___x_626_ = lean_uint64_xor(v_fold_623_, v___x_625_);
v___x_627_ = lean_uint64_to_usize(v___x_626_);
v___x_628_ = lean_usize_of_nat(v___x_619_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_sub(v___x_628_, v___x_629_);
v___x_631_ = lean_usize_land(v___x_627_, v___x_630_);
v___x_632_ = lean_array_uget_borrowed(v_x_611_, v___x_631_);
lean_inc(v___x_632_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 2, v___x_632_);
v___x_634_ = v___x_617_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_key_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_value_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v___x_632_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = lean_array_uset(v_x_611_, v___x_631_, v___x_634_);
v_x_611_ = v___x_635_;
v_x_612_ = v_tail_615_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(lean_object* v_i_639_, lean_object* v_source_640_, lean_object* v_target_641_){
_start:
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_array_get_size(v_source_640_);
v___x_643_ = lean_nat_dec_lt(v_i_639_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_source_640_);
lean_dec(v_i_639_);
return v_target_641_;
}
else
{
lean_object* v_es_644_; lean_object* v___x_645_; lean_object* v_source_646_; lean_object* v_target_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_es_644_ = lean_array_fget(v_source_640_, v_i_639_);
v___x_645_ = lean_box(0);
v_source_646_ = lean_array_fset(v_source_640_, v_i_639_, v___x_645_);
v_target_647_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(v_target_641_, v_es_644_);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_add(v_i_639_, v___x_648_);
lean_dec(v_i_639_);
v_i_639_ = v___x_649_;
v_source_640_ = v_source_646_;
v_target_641_ = v_target_647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(lean_object* v_data_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_nbuckets_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_652_ = lean_array_get_size(v_data_651_);
v___x_653_ = lean_unsigned_to_nat(2u);
v_nbuckets_654_ = lean_nat_mul(v___x_652_, v___x_653_);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_box(0);
v___x_657_ = lean_mk_array(v_nbuckets_654_, v___x_656_);
v___x_658_ = lean_array_propagate_mark(v_data_651_, v___x_657_);
v___x_659_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(v___x_655_, v_data_651_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(lean_object* v_a_660_, lean_object* v_b_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_dec(v_b_661_);
lean_dec(v_a_660_);
return v_x_662_;
}
else
{
lean_object* v_key_663_; lean_object* v_value_664_; lean_object* v_tail_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_677_; 
v_key_663_ = lean_ctor_get(v_x_662_, 0);
v_value_664_ = lean_ctor_get(v_x_662_, 1);
v_tail_665_ = lean_ctor_get(v_x_662_, 2);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_662_);
if (v_isSharedCheck_677_ == 0)
{
v___x_667_ = v_x_662_;
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_tail_665_);
lean_inc(v_value_664_);
lean_inc(v_key_663_);
lean_dec(v_x_662_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_eq(v_key_663_, v_a_660_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(v_a_660_, v_b_661_, v_tail_665_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 2, v___x_670_);
v___x_672_ = v___x_667_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_key_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_value_664_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v___x_675_; 
lean_dec(v_value_664_);
lean_dec(v_key_663_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v_b_661_);
lean_ctor_set(v___x_667_, 0, v_a_660_);
v___x_675_ = v___x_667_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_660_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_b_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_tail_665_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object* v_m_678_, lean_object* v_a_679_, lean_object* v_b_680_){
_start:
{
lean_object* v_size_681_; lean_object* v_buckets_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_725_; 
v_size_681_ = lean_ctor_get(v_m_678_, 0);
v_buckets_682_ = lean_ctor_get(v_m_678_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_m_678_);
if (v_isSharedCheck_725_ == 0)
{
v___x_684_ = v_m_678_;
v_isShared_685_ = v_isSharedCheck_725_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_buckets_682_);
lean_inc(v_size_681_);
lean_dec(v_m_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_725_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v_fold_690_; uint64_t v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v_bkt_699_; uint8_t v___x_700_; 
v___x_686_ = lean_array_get_size(v_buckets_682_);
v___x_687_ = lean_uint64_of_nat(v_a_679_);
v___x_688_ = 32ULL;
v___x_689_ = lean_uint64_shift_right(v___x_687_, v___x_688_);
v_fold_690_ = lean_uint64_xor(v___x_687_, v___x_689_);
v___x_691_ = 16ULL;
v___x_692_ = lean_uint64_shift_right(v_fold_690_, v___x_691_);
v___x_693_ = lean_uint64_xor(v_fold_690_, v___x_692_);
v___x_694_ = lean_uint64_to_usize(v___x_693_);
v___x_695_ = lean_usize_of_nat(v___x_686_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_sub(v___x_695_, v___x_696_);
v___x_698_ = lean_usize_land(v___x_694_, v___x_697_);
v_bkt_699_ = lean_array_uget_borrowed(v_buckets_682_, v___x_698_);
v___x_700_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_679_, v_bkt_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v_size_x27_702_; lean_object* v___x_703_; lean_object* v_buckets_x27_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v_size_x27_702_ = lean_nat_add(v_size_681_, v___x_701_);
lean_dec(v_size_681_);
lean_inc(v_bkt_699_);
v___x_703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_703_, 0, v_a_679_);
lean_ctor_set(v___x_703_, 1, v_b_680_);
lean_ctor_set(v___x_703_, 2, v_bkt_699_);
v_buckets_x27_704_ = lean_array_uset(v_buckets_682_, v___x_698_, v___x_703_);
v___x_705_ = lean_unsigned_to_nat(4u);
v___x_706_ = lean_nat_mul(v_size_x27_702_, v___x_705_);
v___x_707_ = lean_unsigned_to_nat(3u);
v___x_708_ = lean_nat_div(v___x_706_, v___x_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_array_get_size(v_buckets_x27_704_);
v___x_710_ = lean_nat_dec_le(v___x_708_, v___x_709_);
lean_dec(v___x_708_);
if (v___x_710_ == 0)
{
lean_object* v_val_711_; lean_object* v___x_713_; 
v_val_711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(v_buckets_x27_704_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_val_711_);
lean_ctor_set(v___x_684_, 0, v_size_x27_702_);
v___x_713_ = v___x_684_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_size_x27_702_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_val_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v___x_716_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_buckets_x27_704_);
lean_ctor_set(v___x_684_, 0, v_size_x27_702_);
v___x_716_ = v___x_684_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_size_x27_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_buckets_x27_704_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v___x_718_; lean_object* v_buckets_x27_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
lean_inc(v_bkt_699_);
v___x_718_ = lean_box(0);
v_buckets_x27_719_ = lean_array_uset(v_buckets_682_, v___x_698_, v___x_718_);
v___x_720_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(v_a_679_, v_b_680_, v_bkt_699_);
v___x_721_ = lean_array_uset(v_buckets_x27_719_, v___x_698_, v___x_720_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_721_);
v___x_723_ = v___x_684_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_size_681_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object* v_assignment_726_, lean_object* v_as_727_, size_t v_sz_728_, size_t v_i_729_, lean_object* v_b_730_){
_start:
{
lean_object* v_a_732_; uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_lt(v_i_729_, v_sz_728_);
if (v___x_736_ == 0)
{
return v_b_730_;
}
else
{
lean_object* v_a_737_; lean_object* v_fst_738_; 
v_a_737_ = lean_array_uget_borrowed(v_as_727_, v_i_729_);
v_fst_738_ = lean_ctor_get(v_a_737_, 0);
if (lean_obj_tag(v_fst_738_) == 1)
{
lean_object* v_snd_739_; lean_object* v_idx_740_; uint8_t v___y_742_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_snd_739_ = lean_ctor_get(v_a_737_, 1);
v_idx_740_ = lean_ctor_get(v_fst_738_, 0);
v___x_750_ = lean_array_get_size(v_assignment_726_);
v___x_751_ = lean_nat_dec_lt(v_snd_739_, v___x_750_);
if (v___x_751_ == 0)
{
v___y_742_ = v___x_736_;
goto v___jp_741_;
}
else
{
lean_object* v___x_752_; lean_object* v_fst_753_; uint8_t v___x_754_; 
v___x_752_ = lean_array_fget_borrowed(v_assignment_726_, v_snd_739_);
v_fst_753_ = lean_ctor_get(v___x_752_, 0);
v___x_754_ = lean_unbox(v_fst_753_);
v___y_742_ = v___x_754_;
goto v___jp_741_;
}
v___jp_741_:
{
lean_object* v_var_743_; lean_object* v_idx_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_var_743_ = lean_ctor_get(v_idx_740_, 0);
v_idx_744_ = lean_ctor_get(v_idx_740_, 2);
v___x_745_ = lean_box(1);
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(v_b_730_, v_var_743_, v___x_745_);
v___x_747_ = lean_box(v___y_742_);
lean_inc(v_idx_744_);
v___x_748_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_idx_744_, v___x_747_, v___x_746_);
lean_inc(v_var_743_);
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_b_730_, v_var_743_, v___x_748_);
v_a_732_ = v___x_749_;
goto v___jp_731_;
}
}
else
{
v_a_732_ = v_b_730_;
goto v___jp_731_;
}
}
v___jp_731_:
{
size_t v___x_733_; size_t v___x_734_; 
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_add(v_i_729_, v___x_733_);
v_i_729_ = v___x_734_;
v_b_730_ = v_a_732_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_assignment_726_ = stack[0].m_obj;
lean_object* v_as_727_ = stack[1].m_obj;
size_t v_sz_728_ = stack[2].m_num;
size_t v_i_729_ = stack[3].m_num;
lean_object* v_b_730_ = stack[4].m_obj;
lean_object* v_res_755_;
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_assignment_726_, v_as_727_, v_sz_728_, v_i_729_, v_b_730_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object* v_assignment_756_, lean_object* v_as_757_, lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_b_760_){
_start:
{
size_t v_sz_boxed_761_; size_t v_i_boxed_762_; lean_object* v_res_763_; 
v_sz_boxed_761_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_762_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_assignment_756_, v_as_757_, v_sz_boxed_761_, v_i_boxed_762_, v_b_760_);
lean_dec_ref(v_as_757_);
lean_dec_ref(v_assignment_756_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_unsigned_to_nat(16u);
v___x_766_ = lean_mk_array(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_sparseMap_769_; 
v___x_767_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0);
v___x_768_ = lean_unsigned_to_nat(0u);
v_sparseMap_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_sparseMap_769_, 0, v___x_768_);
lean_ctor_set(v_sparseMap_769_, 1, v___x_767_);
return v_sparseMap_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object* v_aig_772_, lean_object* v_assignment_773_, lean_object* v_atomsAssignment_774_){
_start:
{
lean_object* v_decls_775_; lean_object* v___x_776_; lean_object* v_sparseMap_777_; lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v_buckets_782_; lean_object* v_buckets_783_; size_t v_sz_784_; lean_object* v___x_785_; lean_object* v___x_786_; size_t v_sz_787_; lean_object* v___x_788_; 
v_decls_775_ = lean_ctor_get(v_aig_772_, 0);
lean_inc_ref(v_decls_775_);
lean_dec_ref(v_aig_772_);
v___x_776_ = lean_unsigned_to_nat(0u);
v_sparseMap_777_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1);
v___x_778_ = l_Array_zipIdx___redArg(v_decls_775_, v___x_776_);
v_sz_779_ = lean_array_size(v___x_778_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_assignment_773_, v___x_778_, v_sz_779_, v___x_780_, v_sparseMap_777_);
lean_dec_ref(v___x_778_);
v_buckets_782_ = lean_ctor_get(v___x_781_, 1);
v_buckets_783_ = lean_ctor_get(v_atomsAssignment_774_, 1);
v_sz_784_ = lean_array_size(v_buckets_782_);
v___x_785_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2));
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_atomsAssignment_774_, v_buckets_782_, v_sz_784_, v___x_780_, v___x_785_);
v_sz_787_ = lean_array_size(v_buckets_783_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v___x_781_, v_buckets_783_, v_sz_787_, v___x_780_, v___x_786_);
lean_dec_ref(v___x_781_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object* v_aig_789_, lean_object* v_assignment_790_, lean_object* v_atomsAssignment_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_789_, v_assignment_790_, v_atomsAssignment_791_);
lean_dec_ref(v_atomsAssignment_791_);
lean_dec_ref(v_assignment_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_fallback_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(v_m_794_, v_a_795_, v_fallback_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object* v_00_u03b2_798_, lean_object* v_m_799_, lean_object* v_a_800_, lean_object* v_fallback_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_00_u03b2_798_, v_m_799_, v_a_800_, v_fallback_801_);
lean_dec(v_fallback_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_m_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object* v_00_u03b2_803_, lean_object* v_k_804_, lean_object* v_v_805_, lean_object* v_t_806_, lean_object* v_hl_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_k_804_, v_v_805_, v_t_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object* v_00_u03b2_809_, lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_m_810_, v_a_811_, v_b_812_);
return v___x_813_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object* v_00_u03b2_814_, lean_object* v_m_815_, lean_object* v_a_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v_m_815_, v_a_816_);
return v___x_817_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_815_ = stack[1].m_obj;
lean_object* v_a_816_ = stack[2].m_obj;
uint8_t v_res_818_;
v_res_818_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_box(0), v_m_815_, v_a_816_);
stack->m_num = v_res_818_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object* v_00_u03b2_819_, lean_object* v_m_820_, lean_object* v_a_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_00_u03b2_819_, v_m_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_m_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_fallback_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_a_825_, v_fallback_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object* v_00_u03b2_829_, lean_object* v_a_830_, lean_object* v_fallback_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_00_u03b2_829_, v_a_830_, v_fallback_831_, v_x_832_);
lean_dec(v_x_832_);
lean_dec(v_fallback_831_);
lean_dec(v_a_830_);
return v_res_833_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4(lean_object* v_00_u03b2_834_, lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_835_ = stack[1].m_obj;
lean_object* v_x_836_ = stack[2].m_obj;
uint8_t v_res_838_;
v_res_838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4(lean_box(0), v_a_835_, v_x_836_);
stack->m_num = v_res_838_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___boxed(lean_object* v_00_u03b2_839_, lean_object* v_a_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4(v_00_u03b2_839_, v_a_840_, v_x_841_);
lean_dec(v_x_841_);
lean_dec(v_a_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5(lean_object* v_00_u03b2_844_, lean_object* v_data_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(v_data_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6(lean_object* v_00_u03b2_847_, lean_object* v_a_848_, lean_object* v_b_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(v_a_848_, v_b_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_852_, lean_object* v_i_853_, lean_object* v_source_854_, lean_object* v_target_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(v_i_853_, v_source_854_, v_target_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(v_x_858_, v_x_859_);
return v___x_860_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(lean_object* v_mvarId_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_861_, v_x_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_868_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_868_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_861_ = stack[0].m_obj;
lean_object* v_x_862_ = stack[1].m_obj;
lean_object* v___y_863_ = stack[2].m_obj;
lean_object* v___y_864_ = stack[3].m_obj;
lean_object* v___y_865_ = stack[4].m_obj;
lean_object* v___y_866_ = stack[5].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_861_, v_x_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(lean_object* v_mvarId_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_886_, v_x_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_893_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_object* v_00_u03b1_894_, lean_object* v_mvarId_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_902_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_895_ = stack[1].m_obj;
lean_object* v_x_896_ = stack[2].m_obj;
lean_object* v___y_897_ = stack[3].m_obj;
lean_object* v___y_898_ = stack[4].m_obj;
lean_object* v___y_899_ = stack[5].m_obj;
lean_object* v___y_900_ = stack[6].m_obj;
lean_object* v_res_903_;
v_res_903_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_box(0), v_mvarId_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(lean_object* v_00_u03b1_904_, lean_object* v_mvarId_905_, lean_object* v_x_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(v_00_u03b1_904_, v_mvarId_905_, v_x_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_912_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(lean_object* v___x_913_, lean_object* v_x_914_, lean_object* v_counterExample_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_st_mk_ref(v___x_913_);
lean_inc(v___x_921_);
v___x_922_ = lean_apply_7(v_x_914_, v_counterExample_915_, v___x_921_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_931_);
v___x_924_ = v___x_922_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_st_ref_get(v___x_921_);
lean_dec(v___x_921_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v___x_921_);
v_a_932_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_922_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_922_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_913_ = stack[0].m_obj;
lean_object* v_x_914_ = stack[1].m_obj;
lean_object* v_counterExample_915_ = stack[2].m_obj;
lean_object* v___y_916_ = stack[3].m_obj;
lean_object* v___y_917_ = stack[4].m_obj;
lean_object* v___y_918_ = stack[5].m_obj;
lean_object* v___y_919_ = stack[6].m_obj;
lean_object* v_res_940_;
v_res_940_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_913_, v_x_914_, v_counterExample_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(lean_object* v___x_941_, lean_object* v_x_942_, lean_object* v_counterExample_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_941_, v_x_942_, v_counterExample_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v_res_949_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_unsigned_to_nat(16u);
v___x_952_ = lean_mk_array(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0);
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
return v___x_955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3));
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2));
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1);
v___x_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_961_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
lean_ctor_set(v___x_963_, 3, v___x_962_);
lean_ctor_set(v___x_963_, 4, v___x_960_);
return v___x_963_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(lean_object* v_x_964_, lean_object* v_counterExample_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_goal_971_; lean_object* v___x_972_; lean_object* v___f_973_; lean_object* v___x_974_; 
v_goal_971_ = lean_ctor_get(v_counterExample_965_, 0);
lean_inc(v_goal_971_);
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4);
v___f_973_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed), 8, 3);
lean_closure_set(v___f_973_, 0, v___x_972_);
lean_closure_set(v___f_973_, 1, v_x_964_);
lean_closure_set(v___f_973_, 2, v_counterExample_965_);
v___x_974_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_goal_971_, v___f_973_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
return v___x_974_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_964_ = stack[0].m_obj;
lean_object* v_counterExample_965_ = stack[1].m_obj;
lean_object* v_a_966_ = stack[2].m_obj;
lean_object* v_a_967_ = stack[3].m_obj;
lean_object* v_a_968_ = stack[4].m_obj;
lean_object* v_a_969_ = stack[5].m_obj;
lean_object* v_res_975_;
v_res_975_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_964_, v_counterExample_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(lean_object* v_x_976_, lean_object* v_counterExample_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_976_, v_counterExample_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
return v_res_983_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(lean_object* v_a_984_){
_start:
{
lean_object* v_unusedHypotheses_986_; lean_object* v___x_987_; 
v_unusedHypotheses_986_ = lean_ctor_get(v_a_984_, 1);
lean_inc_ref(v_unusedHypotheses_986_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_unusedHypotheses_986_);
return v___x_987_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_984_ = stack[0].m_obj;
lean_object* v_res_988_;
v_res_988_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_984_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_989_);
lean_dec_ref(v_a_989_);
return v_res_991_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_unusedHypotheses_999_; lean_object* v___x_1000_; 
v_unusedHypotheses_999_ = lean_ctor_get(v_a_992_, 1);
lean_inc_ref(v_unusedHypotheses_999_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_unusedHypotheses_999_);
return v___x_1000_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_992_ = stack[0].m_obj;
lean_object* v_a_993_ = stack[1].m_obj;
lean_object* v_a_994_ = stack[2].m_obj;
lean_object* v_a_995_ = stack[3].m_obj;
lean_object* v_a_996_ = stack[4].m_obj;
lean_object* v_a_997_ = stack[5].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1009_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(lean_object* v_a_1010_){
_start:
{
lean_object* v_equations_1012_; lean_object* v___x_1013_; 
v_equations_1012_ = lean_ctor_get(v_a_1010_, 2);
lean_inc_ref(v_equations_1012_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_equations_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1010_ = stack[0].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_1010_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_1015_);
lean_dec_ref(v_a_1015_);
return v_res_1017_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_equations_1025_; lean_object* v___x_1026_; 
v_equations_1025_ = lean_ctor_get(v_a_1018_, 2);
lean_inc_ref(v_equations_1025_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_equations_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1018_ = stack[0].m_obj;
lean_object* v_a_1019_ = stack[1].m_obj;
lean_object* v_a_1020_ = stack[2].m_obj;
lean_object* v_a_1021_ = stack[3].m_obj;
lean_object* v_a_1022_ = stack[4].m_obj;
lean_object* v_a_1023_ = stack[5].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1035_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(lean_object* v_e_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_uninterpretedSymbols_1044_; lean_object* v_functionSymbols_1045_; lean_object* v_functionSymbolSet_1046_; lean_object* v_unusedRelevantHypotheses_1047_; lean_object* v_derivedEquations_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1059_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1043_ = lean_st_ref_take(v_a_1039_);
v_uninterpretedSymbols_1044_ = lean_ctor_get(v___x_1043_, 0);
v_functionSymbols_1045_ = lean_ctor_get(v___x_1043_, 1);
v_functionSymbolSet_1046_ = lean_ctor_get(v___x_1043_, 2);
v_unusedRelevantHypotheses_1047_ = lean_ctor_get(v___x_1043_, 3);
v_derivedEquations_1048_ = lean_ctor_get(v___x_1043_, 4);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1050_ = v___x_1043_;
v_isShared_1051_ = v_isSharedCheck_1059_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_derivedEquations_1048_);
lean_inc(v_unusedRelevantHypotheses_1047_);
lean_inc(v_functionSymbolSet_1046_);
lean_inc(v_functionSymbols_1045_);
lean_inc(v_uninterpretedSymbols_1044_);
lean_dec(v___x_1043_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1059_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1041_, v___x_1042_, v_uninterpretedSymbols_1044_, v_e_1038_, v___x_1052_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_functionSymbols_1045_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_functionSymbolSet_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_unusedRelevantHypotheses_1047_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_derivedEquations_1048_);
v___x_1055_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_st_ref_put(v_a_1039_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1052_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1038_ = stack[0].m_obj;
lean_object* v_a_1039_ = stack[1].m_obj;
lean_object* v_res_1060_;
v_res_1060_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_1038_, v_a_1039_);
stack->m_obj
 = v_res_1060_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object* v_e_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_1061_, v_a_1062_);
lean_dec(v_a_1062_);
return v_res_1064_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(lean_object* v_e_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_uninterpretedSymbols_1076_; lean_object* v_functionSymbols_1077_; lean_object* v_functionSymbolSet_1078_; lean_object* v_unusedRelevantHypotheses_1079_; lean_object* v_derivedEquations_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1091_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1075_ = lean_st_ref_take(v_a_1067_);
v_uninterpretedSymbols_1076_ = lean_ctor_get(v___x_1075_, 0);
v_functionSymbols_1077_ = lean_ctor_get(v___x_1075_, 1);
v_functionSymbolSet_1078_ = lean_ctor_get(v___x_1075_, 2);
v_unusedRelevantHypotheses_1079_ = lean_ctor_get(v___x_1075_, 3);
v_derivedEquations_1080_ = lean_ctor_get(v___x_1075_, 4);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1082_ = v___x_1075_;
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_derivedEquations_1080_);
lean_inc(v_unusedRelevantHypotheses_1079_);
lean_inc(v_functionSymbolSet_1078_);
lean_inc(v_functionSymbols_1077_);
lean_inc(v_uninterpretedSymbols_1076_);
lean_dec(v___x_1075_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1073_, v___x_1074_, v_uninterpretedSymbols_1076_, v_e_1065_, v___x_1084_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_functionSymbols_1077_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_functionSymbolSet_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_unusedRelevantHypotheses_1079_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_derivedEquations_1080_);
v___x_1087_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_st_ref_put(v_a_1067_, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1084_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1065_ = stack[0].m_obj;
lean_object* v_a_1066_ = stack[1].m_obj;
lean_object* v_a_1067_ = stack[2].m_obj;
lean_object* v_a_1068_ = stack[3].m_obj;
lean_object* v_a_1069_ = stack[4].m_obj;
lean_object* v_a_1070_ = stack[5].m_obj;
lean_object* v_a_1071_ = stack[6].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(lean_object* v_e_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1101_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg(lean_object* v_e_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_uninterpretedSymbols_1108_; lean_object* v_functionSymbols_1109_; lean_object* v_functionSymbolSet_1110_; lean_object* v_unusedRelevantHypotheses_1111_; lean_object* v_derivedEquations_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1124_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1107_ = lean_st_ref_take(v_a_1103_);
v_uninterpretedSymbols_1108_ = lean_ctor_get(v___x_1107_, 0);
v_functionSymbols_1109_ = lean_ctor_get(v___x_1107_, 1);
v_functionSymbolSet_1110_ = lean_ctor_get(v___x_1107_, 2);
v_unusedRelevantHypotheses_1111_ = lean_ctor_get(v___x_1107_, 3);
v_derivedEquations_1112_ = lean_ctor_get(v___x_1107_, 4);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1114_ = v___x_1107_;
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_derivedEquations_1112_);
lean_inc(v_unusedRelevantHypotheses_1111_);
lean_inc(v_functionSymbolSet_1110_);
lean_inc(v_functionSymbols_1109_);
lean_inc(v_uninterpretedSymbols_1108_);
lean_dec(v___x_1107_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1116_ = lean_box(0);
lean_inc_ref(v_e_1102_);
v___x_1117_ = lean_array_push(v_functionSymbols_1109_, v_e_1102_);
v___x_1118_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1105_, v___x_1106_, v_functionSymbolSet_1110_, v_e_1102_, v___x_1116_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 2, v___x_1118_);
lean_ctor_set(v___x_1114_, 1, v___x_1117_);
v___x_1120_ = v___x_1114_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_uninterpretedSymbols_1108_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_unusedRelevantHypotheses_1111_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_derivedEquations_1112_);
v___x_1120_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_st_ref_put(v_a_1103_, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1116_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1102_ = stack[0].m_obj;
lean_object* v_a_1103_ = stack[1].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg(v_e_1102_, v_a_1103_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg___boxed(lean_object* v_e_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg(v_e_1126_, v_a_1127_);
lean_dec(v_a_1127_);
return v_res_1129_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol(lean_object* v_e_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_uninterpretedSymbols_1141_; lean_object* v_functionSymbols_1142_; lean_object* v_functionSymbolSet_1143_; lean_object* v_unusedRelevantHypotheses_1144_; lean_object* v_derivedEquations_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1157_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1140_ = lean_st_ref_take(v_a_1132_);
v_uninterpretedSymbols_1141_ = lean_ctor_get(v___x_1140_, 0);
v_functionSymbols_1142_ = lean_ctor_get(v___x_1140_, 1);
v_functionSymbolSet_1143_ = lean_ctor_get(v___x_1140_, 2);
v_unusedRelevantHypotheses_1144_ = lean_ctor_get(v___x_1140_, 3);
v_derivedEquations_1145_ = lean_ctor_get(v___x_1140_, 4);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1147_ = v___x_1140_;
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_derivedEquations_1145_);
lean_inc(v_unusedRelevantHypotheses_1144_);
lean_inc(v_functionSymbolSet_1143_);
lean_inc(v_functionSymbols_1142_);
lean_inc(v_uninterpretedSymbols_1141_);
lean_dec(v___x_1140_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1149_ = lean_box(0);
lean_inc_ref(v_e_1130_);
v___x_1150_ = lean_array_push(v_functionSymbols_1142_, v_e_1130_);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1138_, v___x_1139_, v_functionSymbolSet_1143_, v_e_1130_, v___x_1149_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 2, v___x_1151_);
lean_ctor_set(v___x_1147_, 1, v___x_1150_);
v___x_1153_ = v___x_1147_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_uninterpretedSymbols_1141_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_unusedRelevantHypotheses_1144_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_derivedEquations_1145_);
v___x_1153_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_st_ref_put(v_a_1132_, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1149_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1130_ = stack[0].m_obj;
lean_object* v_a_1131_ = stack[1].m_obj;
lean_object* v_a_1132_ = stack[2].m_obj;
lean_object* v_a_1133_ = stack[3].m_obj;
lean_object* v_a_1134_ = stack[4].m_obj;
lean_object* v_a_1135_ = stack[5].m_obj;
lean_object* v_a_1136_ = stack[6].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol(v_e_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___boxed(lean_object* v_e_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1167_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg(lean_object* v_e_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_functionSymbolSet_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1173_ = lean_st_ref_get(v_a_1169_);
v_functionSymbolSet_1174_ = lean_ctor_get(v___x_1173_, 2);
lean_inc_ref(v_functionSymbolSet_1174_);
lean_dec(v___x_1173_);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1171_, v___x_1172_, v_functionSymbolSet_1174_, v_e_1168_);
lean_dec_ref(v_functionSymbolSet_1174_);
v___x_1176_ = lean_box(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1168_ = stack[0].m_obj;
lean_object* v_a_1169_ = stack[1].m_obj;
lean_object* v_res_1178_;
v_res_1178_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg(v_e_1168_, v_a_1169_);
stack->m_obj
 = v_res_1178_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg___boxed(lean_object* v_e_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg(v_e_1179_, v_a_1180_);
lean_dec(v_a_1180_);
return v_res_1182_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol(lean_object* v_e_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_functionSymbolSet_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1193_ = lean_st_ref_get(v_a_1185_);
v_functionSymbolSet_1194_ = lean_ctor_get(v___x_1193_, 2);
lean_inc_ref(v_functionSymbolSet_1194_);
lean_dec(v___x_1193_);
v___x_1195_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1191_, v___x_1192_, v_functionSymbolSet_1194_, v_e_1183_);
lean_dec_ref(v_functionSymbolSet_1194_);
v___x_1196_ = lean_box(v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1183_ = stack[0].m_obj;
lean_object* v_a_1184_ = stack[1].m_obj;
lean_object* v_a_1185_ = stack[2].m_obj;
lean_object* v_a_1186_ = stack[3].m_obj;
lean_object* v_a_1187_ = stack[4].m_obj;
lean_object* v_a_1188_ = stack[5].m_obj;
lean_object* v_a_1189_ = stack[6].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol(v_e_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___boxed(lean_object* v_e_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol(v_e_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1207_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object* v_hyp_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v_uninterpretedSymbols_1216_; lean_object* v_functionSymbols_1217_; lean_object* v_functionSymbolSet_1218_; lean_object* v_unusedRelevantHypotheses_1219_; lean_object* v_derivedEquations_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1231_; 
v___f_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1215_ = lean_st_ref_take(v_a_1211_);
v_uninterpretedSymbols_1216_ = lean_ctor_get(v___x_1215_, 0);
v_functionSymbols_1217_ = lean_ctor_get(v___x_1215_, 1);
v_functionSymbolSet_1218_ = lean_ctor_get(v___x_1215_, 2);
v_unusedRelevantHypotheses_1219_ = lean_ctor_get(v___x_1215_, 3);
v_derivedEquations_1220_ = lean_ctor_get(v___x_1215_, 4);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1222_ = v___x_1215_;
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_derivedEquations_1220_);
lean_inc(v_unusedRelevantHypotheses_1219_);
lean_inc(v_functionSymbolSet_1218_);
lean_inc(v_functionSymbols_1217_);
lean_inc(v_uninterpretedSymbols_1216_);
lean_dec(v___x_1215_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1213_, v___f_1214_, v_unusedRelevantHypotheses_1219_, v_hyp_1210_, v___x_1224_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 3, v___x_1225_);
v___x_1227_ = v___x_1222_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_uninterpretedSymbols_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_functionSymbols_1217_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_functionSymbolSet_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_derivedEquations_1220_);
v___x_1227_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_st_ref_put(v_a_1211_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1224_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_1210_ = stack[0].m_obj;
lean_object* v_a_1211_ = stack[1].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_hyp_1210_, v_a_1211_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object* v_hyp_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_hyp_1233_, v_a_1234_);
lean_dec(v_a_1234_);
return v_res_1236_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(lean_object* v_hyp_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v_uninterpretedSymbols_1248_; lean_object* v_functionSymbols_1249_; lean_object* v_functionSymbolSet_1250_; lean_object* v_unusedRelevantHypotheses_1251_; lean_object* v_derivedEquations_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1263_; 
v___f_1245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1247_ = lean_st_ref_take(v_a_1239_);
v_uninterpretedSymbols_1248_ = lean_ctor_get(v___x_1247_, 0);
v_functionSymbols_1249_ = lean_ctor_get(v___x_1247_, 1);
v_functionSymbolSet_1250_ = lean_ctor_get(v___x_1247_, 2);
v_unusedRelevantHypotheses_1251_ = lean_ctor_get(v___x_1247_, 3);
v_derivedEquations_1252_ = lean_ctor_get(v___x_1247_, 4);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1254_ = v___x_1247_;
v_isShared_1255_ = v_isSharedCheck_1263_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_derivedEquations_1252_);
lean_inc(v_unusedRelevantHypotheses_1251_);
lean_inc(v_functionSymbolSet_1250_);
lean_inc(v_functionSymbols_1249_);
lean_inc(v_uninterpretedSymbols_1248_);
lean_dec(v___x_1247_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1263_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1245_, v___f_1246_, v_unusedRelevantHypotheses_1251_, v_hyp_1237_, v___x_1256_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 3, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_uninterpretedSymbols_1248_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_functionSymbols_1249_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_functionSymbolSet_1250_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_derivedEquations_1252_);
v___x_1259_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_st_ref_put(v_a_1239_, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1256_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_1237_ = stack[0].m_obj;
lean_object* v_a_1238_ = stack[1].m_obj;
lean_object* v_a_1239_ = stack[2].m_obj;
lean_object* v_a_1240_ = stack[3].m_obj;
lean_object* v_a_1241_ = stack[4].m_obj;
lean_object* v_a_1242_ = stack[5].m_obj;
lean_object* v_a_1243_ = stack[6].m_obj;
lean_object* v_res_1264_;
v_res_1264_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_hyp_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object* v_hyp_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_hyp_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
return v_res_1273_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(lean_object* v_var_1274_, lean_object* v_value_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_uninterpretedSymbols_1279_; lean_object* v_functionSymbols_1280_; lean_object* v_functionSymbolSet_1281_; lean_object* v_unusedRelevantHypotheses_1282_; lean_object* v_derivedEquations_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1295_; 
v___x_1278_ = lean_st_ref_take(v_a_1276_);
v_uninterpretedSymbols_1279_ = lean_ctor_get(v___x_1278_, 0);
v_functionSymbols_1280_ = lean_ctor_get(v___x_1278_, 1);
v_functionSymbolSet_1281_ = lean_ctor_get(v___x_1278_, 2);
v_unusedRelevantHypotheses_1282_ = lean_ctor_get(v___x_1278_, 3);
v_derivedEquations_1283_ = lean_ctor_get(v___x_1278_, 4);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1285_ = v___x_1278_;
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_derivedEquations_1283_);
lean_inc(v_unusedRelevantHypotheses_1282_);
lean_inc(v_functionSymbolSet_1281_);
lean_inc(v_functionSymbols_1280_);
lean_inc(v_uninterpretedSymbols_1279_);
lean_dec(v___x_1278_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_var_1274_);
lean_ctor_set(v___x_1288_, 1, v_value_1275_);
v___x_1289_ = lean_array_push(v_derivedEquations_1283_, v___x_1288_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1289_);
v___x_1291_ = v___x_1285_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_uninterpretedSymbols_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_functionSymbols_1280_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_functionSymbolSet_1281_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_unusedRelevantHypotheses_1282_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_st_ref_put(v_a_1276_, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1287_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_var_1274_ = stack[0].m_obj;
lean_object* v_value_1275_ = stack[1].m_obj;
lean_object* v_a_1276_ = stack[2].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_1274_, v_value_1275_, v_a_1276_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object* v_var_1297_, lean_object* v_value_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_1297_, v_value_1298_, v_a_1299_);
lean_dec(v_a_1299_);
return v_res_1301_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(lean_object* v_var_1302_, lean_object* v_value_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_uninterpretedSymbols_1312_; lean_object* v_functionSymbols_1313_; lean_object* v_functionSymbolSet_1314_; lean_object* v_unusedRelevantHypotheses_1315_; lean_object* v_derivedEquations_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1328_; 
v___x_1311_ = lean_st_ref_take(v_a_1305_);
v_uninterpretedSymbols_1312_ = lean_ctor_get(v___x_1311_, 0);
v_functionSymbols_1313_ = lean_ctor_get(v___x_1311_, 1);
v_functionSymbolSet_1314_ = lean_ctor_get(v___x_1311_, 2);
v_unusedRelevantHypotheses_1315_ = lean_ctor_get(v___x_1311_, 3);
v_derivedEquations_1316_ = lean_ctor_get(v___x_1311_, 4);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1318_ = v___x_1311_;
v_isShared_1319_ = v_isSharedCheck_1328_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_derivedEquations_1316_);
lean_inc(v_unusedRelevantHypotheses_1315_);
lean_inc(v_functionSymbolSet_1314_);
lean_inc(v_functionSymbols_1313_);
lean_inc(v_uninterpretedSymbols_1312_);
lean_dec(v___x_1311_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1328_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_var_1302_);
lean_ctor_set(v___x_1321_, 1, v_value_1303_);
v___x_1322_ = lean_array_push(v_derivedEquations_1316_, v___x_1321_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 4, v___x_1322_);
v___x_1324_ = v___x_1318_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_uninterpretedSymbols_1312_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_functionSymbols_1313_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_functionSymbolSet_1314_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_unusedRelevantHypotheses_1315_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_st_ref_put(v_a_1305_, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1320_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation_0interp(lean_interpreter_value* stack)
{
lean_object* v_var_1302_ = stack[0].m_obj;
lean_object* v_value_1303_ = stack[1].m_obj;
lean_object* v_a_1304_ = stack[2].m_obj;
lean_object* v_a_1305_ = stack[3].m_obj;
lean_object* v_a_1306_ = stack[4].m_obj;
lean_object* v_a_1307_ = stack[5].m_obj;
lean_object* v_a_1308_ = stack[6].m_obj;
lean_object* v_a_1309_ = stack[7].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_1302_, v_value_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(lean_object* v_var_1330_, lean_object* v_value_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_1330_, v_value_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
return v_res_1339_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object* v_a_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 0)
{
uint8_t v___x_1342_; 
v___x_1342_ = 0;
return v___x_1342_;
}
else
{
lean_object* v_key_1343_; lean_object* v_tail_1344_; lean_object* v_type_1345_; lean_object* v_type_1346_; uint8_t v___x_1347_; 
v_key_1343_ = lean_ctor_get(v_x_1341_, 0);
v_tail_1344_ = lean_ctor_get(v_x_1341_, 2);
v_type_1345_ = lean_ctor_get(v_key_1343_, 1);
v_type_1346_ = lean_ctor_get(v_a_1340_, 1);
v___x_1347_ = lean_expr_eqv(v_type_1345_, v_type_1346_);
if (v___x_1347_ == 0)
{
v_x_1341_ = v_tail_1344_;
goto _start;
}
else
{
return v___x_1347_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1340_ = stack[0].m_obj;
lean_object* v_x_1341_ = stack[1].m_obj;
uint8_t v_res_1349_;
v_res_1349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1340_, v_x_1341_);
stack->m_num = v_res_1349_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object* v_a_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1350_, v_x_1351_);
lean_dec(v_x_1351_);
lean_dec_ref(v_a_1350_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
if (lean_obj_tag(v_x_1355_) == 0)
{
return v_x_1354_;
}
else
{
lean_object* v_key_1356_; lean_object* v_value_1357_; lean_object* v_tail_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1382_; 
v_key_1356_ = lean_ctor_get(v_x_1355_, 0);
v_value_1357_ = lean_ctor_get(v_x_1355_, 1);
v_tail_1358_ = lean_ctor_get(v_x_1355_, 2);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1355_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1360_ = v_x_1355_;
v_isShared_1361_ = v_isSharedCheck_1382_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_tail_1358_);
lean_inc(v_value_1357_);
lean_inc(v_key_1356_);
lean_dec(v_x_1355_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1382_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_type_1362_; lean_object* v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v_fold_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v_type_1362_ = lean_ctor_get(v_key_1356_, 1);
v___x_1363_ = lean_array_get_size(v_x_1354_);
v___x_1364_ = l_Lean_Expr_hash(v_type_1362_);
v___x_1365_ = 32ULL;
v___x_1366_ = lean_uint64_shift_right(v___x_1364_, v___x_1365_);
v_fold_1367_ = lean_uint64_xor(v___x_1364_, v___x_1366_);
v___x_1368_ = 16ULL;
v___x_1369_ = lean_uint64_shift_right(v_fold_1367_, v___x_1368_);
v___x_1370_ = lean_uint64_xor(v_fold_1367_, v___x_1369_);
v___x_1371_ = lean_uint64_to_usize(v___x_1370_);
v___x_1372_ = lean_usize_of_nat(v___x_1363_);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_usize_land(v___x_1371_, v___x_1374_);
v___x_1376_ = lean_array_uget_borrowed(v_x_1354_, v___x_1375_);
lean_inc(v___x_1376_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 2, v___x_1376_);
v___x_1378_ = v___x_1360_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_key_1356_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_value_1357_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_array_uset(v_x_1354_, v___x_1375_, v___x_1378_);
v_x_1354_ = v___x_1379_;
v_x_1355_ = v_tail_1358_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1383_, lean_object* v_source_1384_, lean_object* v_target_1385_){
_start:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = lean_array_get_size(v_source_1384_);
v___x_1387_ = lean_nat_dec_lt(v_i_1383_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v_source_1384_);
lean_dec(v_i_1383_);
return v_target_1385_;
}
else
{
lean_object* v_es_1388_; lean_object* v___x_1389_; lean_object* v_source_1390_; lean_object* v_target_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_es_1388_ = lean_array_fget(v_source_1384_, v_i_1383_);
v___x_1389_ = lean_box(0);
v_source_1390_ = lean_array_fset(v_source_1384_, v_i_1383_, v___x_1389_);
v_target_1391_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_target_1385_, v_es_1388_);
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_add(v_i_1383_, v___x_1392_);
lean_dec(v_i_1383_);
v_i_1383_ = v___x_1393_;
v_source_1384_ = v_source_1390_;
v_target_1385_ = v_target_1391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(lean_object* v_data_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_nbuckets_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1396_ = lean_array_get_size(v_data_1395_);
v___x_1397_ = lean_unsigned_to_nat(2u);
v_nbuckets_1398_ = lean_nat_mul(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_mk_array(v_nbuckets_1398_, v___x_1400_);
v___x_1402_ = lean_array_propagate_mark(v_data_1395_, v___x_1401_);
v___x_1403_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v___x_1399_, v_data_1395_, v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object* v_m_1404_, lean_object* v_a_1405_, lean_object* v_b_1406_){
_start:
{
lean_object* v_size_1407_; lean_object* v_buckets_1408_; lean_object* v_type_1409_; lean_object* v___x_1410_; uint64_t v___x_1411_; uint64_t v___x_1412_; uint64_t v___x_1413_; uint64_t v_fold_1414_; uint64_t v___x_1415_; uint64_t v___x_1416_; uint64_t v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; lean_object* v_bkt_1423_; uint8_t v___x_1424_; 
v_size_1407_ = lean_ctor_get(v_m_1404_, 0);
v_buckets_1408_ = lean_ctor_get(v_m_1404_, 1);
v_type_1409_ = lean_ctor_get(v_a_1405_, 1);
v___x_1410_ = lean_array_get_size(v_buckets_1408_);
v___x_1411_ = l_Lean_Expr_hash(v_type_1409_);
v___x_1412_ = 32ULL;
v___x_1413_ = lean_uint64_shift_right(v___x_1411_, v___x_1412_);
v_fold_1414_ = lean_uint64_xor(v___x_1411_, v___x_1413_);
v___x_1415_ = 16ULL;
v___x_1416_ = lean_uint64_shift_right(v_fold_1414_, v___x_1415_);
v___x_1417_ = lean_uint64_xor(v_fold_1414_, v___x_1416_);
v___x_1418_ = lean_uint64_to_usize(v___x_1417_);
v___x_1419_ = lean_usize_of_nat(v___x_1410_);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_sub(v___x_1419_, v___x_1420_);
v___x_1422_ = lean_usize_land(v___x_1418_, v___x_1421_);
v_bkt_1423_ = lean_array_uget_borrowed(v_buckets_1408_, v___x_1422_);
v___x_1424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1405_, v_bkt_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1445_; 
lean_inc_ref(v_buckets_1408_);
lean_inc(v_size_1407_);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_m_1404_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1446_ = lean_ctor_get(v_m_1404_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_m_1404_, 0);
lean_dec(v_unused_1447_);
v___x_1426_ = v_m_1404_;
v_isShared_1427_ = v_isSharedCheck_1445_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v_m_1404_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1445_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v_size_x27_1429_; lean_object* v___x_1430_; lean_object* v_buckets_x27_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v_size_x27_1429_ = lean_nat_add(v_size_1407_, v___x_1428_);
lean_dec(v_size_1407_);
lean_inc(v_bkt_1423_);
v___x_1430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1405_);
lean_ctor_set(v___x_1430_, 1, v_b_1406_);
lean_ctor_set(v___x_1430_, 2, v_bkt_1423_);
v_buckets_x27_1431_ = lean_array_uset(v_buckets_1408_, v___x_1422_, v___x_1430_);
v___x_1432_ = lean_unsigned_to_nat(4u);
v___x_1433_ = lean_nat_mul(v_size_x27_1429_, v___x_1432_);
v___x_1434_ = lean_unsigned_to_nat(3u);
v___x_1435_ = lean_nat_div(v___x_1433_, v___x_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_array_get_size(v_buckets_x27_1431_);
v___x_1437_ = lean_nat_dec_le(v___x_1435_, v___x_1436_);
lean_dec(v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v_val_1438_; lean_object* v___x_1440_; 
v_val_1438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_buckets_x27_1431_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_val_1438_);
lean_ctor_set(v___x_1426_, 0, v_size_x27_1429_);
v___x_1440_ = v___x_1426_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_size_x27_1429_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_val_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1443_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_buckets_x27_1431_);
lean_ctor_set(v___x_1426_, 0, v_size_x27_1429_);
v___x_1443_ = v___x_1426_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_size_x27_1429_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_buckets_x27_1431_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_dec(v_b_1406_);
lean_dec_ref(v_a_1405_);
return v_m_1404_;
}
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object* v_fvar_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v___y_1451_){
_start:
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1450_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
else
{
lean_object* v_key_1455_; lean_object* v_tail_1456_; lean_object* v_type_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_key_1455_ = lean_ctor_get(v_a_1449_, 0);
lean_inc(v_key_1455_);
v_tail_1456_ = lean_ctor_get(v_a_1449_, 2);
lean_inc(v_tail_1456_);
lean_dec_ref_known(v_a_1449_, 3);
v_type_1457_ = lean_ctor_get(v_key_1455_, 1);
v___x_1458_ = lean_box(0);
v___x_1459_ = l_Lean_Expr_containsFVar(v_type_1457_, v_fvar_1448_);
if (v___x_1459_ == 0)
{
lean_dec(v_key_1455_);
v_a_1449_ = v_tail_1456_;
v_a_1450_ = v___x_1458_;
goto _start;
}
else
{
lean_object* v___x_1461_; lean_object* v_uninterpretedSymbols_1462_; lean_object* v_functionSymbols_1463_; lean_object* v_functionSymbolSet_1464_; lean_object* v_unusedRelevantHypotheses_1465_; lean_object* v_derivedEquations_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1476_; 
v___x_1461_ = lean_st_ref_take(v___y_1451_);
v_uninterpretedSymbols_1462_ = lean_ctor_get(v___x_1461_, 0);
v_functionSymbols_1463_ = lean_ctor_get(v___x_1461_, 1);
v_functionSymbolSet_1464_ = lean_ctor_get(v___x_1461_, 2);
v_unusedRelevantHypotheses_1465_ = lean_ctor_get(v___x_1461_, 3);
v_derivedEquations_1466_ = lean_ctor_get(v___x_1461_, 4);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1468_ = v___x_1461_;
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_derivedEquations_1466_);
lean_inc(v_unusedRelevantHypotheses_1465_);
lean_inc(v_functionSymbolSet_1464_);
lean_inc(v_functionSymbols_1463_);
lean_inc(v_uninterpretedSymbols_1462_);
lean_dec(v___x_1461_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_unusedRelevantHypotheses_1465_, v_key_1455_, v___x_1458_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 3, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_uninterpretedSymbols_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_functionSymbols_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_functionSymbolSet_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_derivedEquations_1466_);
v___x_1472_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_st_ref_put(v___y_1451_, v___x_1472_);
v_a_1449_ = v_tail_1456_;
v_a_1450_ = v___x_1458_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_1448_ = stack[0].m_obj;
lean_object* v_a_1449_ = stack[1].m_obj;
lean_object* v_a_1450_ = stack[2].m_obj;
lean_object* v___y_1451_ = stack[3].m_obj;
lean_object* v_res_1477_;
v_res_1477_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1448_, v_a_1449_, v_a_1450_, v___y_1451_);
stack->m_obj
 = v_res_1477_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object* v_fvar_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1478_, v_a_1479_, v_a_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec(v_fvar_1478_);
return v_res_1483_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object* v_fvar_1484_, lean_object* v_as_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1488_);
return v___x_1497_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_array_uget_borrowed(v_as_1485_, v_i_1487_);
lean_inc(v_a_1498_);
v___x_1499_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1484_, v_a_1498_, v_b_1488_, v___y_1490_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1512_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1512_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1512_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
if (lean_obj_tag(v_a_1500_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; 
v_a_1504_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v_a_1500_, 1);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_a_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
else
{
lean_object* v_a_1508_; size_t v___x_1509_; size_t v___x_1510_; 
lean_del_object(v___x_1502_);
v_a_1508_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v_a_1500_, 1);
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_add(v_i_1487_, v___x_1509_);
v_i_1487_ = v___x_1510_;
v_b_1488_ = v_a_1508_;
goto _start;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1499_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1499_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_1484_ = stack[0].m_obj;
lean_object* v_as_1485_ = stack[1].m_obj;
size_t v_sz_1486_ = stack[2].m_num;
size_t v_i_1487_ = stack[3].m_num;
lean_object* v_b_1488_ = stack[4].m_obj;
lean_object* v___y_1489_ = stack[5].m_obj;
lean_object* v___y_1490_ = stack[6].m_obj;
lean_object* v___y_1491_ = stack[7].m_obj;
lean_object* v___y_1492_ = stack[8].m_obj;
lean_object* v___y_1493_ = stack[9].m_obj;
lean_object* v___y_1494_ = stack[10].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1484_, v_as_1485_, v_sz_1486_, v_i_1487_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object* v_fvar_1522_, lean_object* v_as_1523_, lean_object* v_sz_1524_, lean_object* v_i_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
size_t v_sz_boxed_1534_; size_t v_i_boxed_1535_; lean_object* v_res_1536_; 
v_sz_boxed_1534_ = lean_unbox_usize(v_sz_1524_);
lean_dec(v_sz_1524_);
v_i_boxed_1535_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1522_, v_as_1523_, v_sz_boxed_1534_, v_i_boxed_1535_, v_b_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v_as_1523_);
lean_dec(v_fvar_1522_);
return v_res_1536_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object* v_fvar_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_unusedHypotheses_1545_; lean_object* v_buckets_1546_; lean_object* v___x_1547_; size_t v_sz_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v_unusedHypotheses_1545_ = lean_ctor_get(v_a_1538_, 1);
v_buckets_1546_ = lean_ctor_get(v_unusedHypotheses_1545_, 1);
v___x_1547_ = lean_box(0);
v_sz_1548_ = lean_array_size(v_buckets_1546_);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1537_, v_buckets_1546_, v_sz_1548_, v___x_1549_, v___x_1547_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v___x_1550_, 0);
lean_dec(v_unused_1558_);
v___x_1552_ = v___x_1550_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v___x_1550_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1547_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
return v___x_1550_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_1537_ = stack[0].m_obj;
lean_object* v_a_1538_ = stack[1].m_obj;
lean_object* v_a_1539_ = stack[2].m_obj;
lean_object* v_a_1540_ = stack[3].m_obj;
lean_object* v_a_1541_ = stack[4].m_obj;
lean_object* v_a_1542_ = stack[5].m_obj;
lean_object* v_a_1543_ = stack[6].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object* v_fvar_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_fvar_1560_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object* v_00_u03b2_1569_, lean_object* v_m_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_1570_, v_a_1571_, v_b_1572_);
return v___x_1573_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object* v_fvar_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1574_, v_a_1575_, v_a_1576_, v___y_1578_);
return v___x_1584_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_1574_ = stack[0].m_obj;
lean_object* v_a_1575_ = stack[1].m_obj;
lean_object* v_a_1576_ = stack[2].m_obj;
lean_object* v___y_1577_ = stack[3].m_obj;
lean_object* v___y_1578_ = stack[4].m_obj;
lean_object* v___y_1579_ = stack[5].m_obj;
lean_object* v___y_1580_ = stack[6].m_obj;
lean_object* v___y_1581_ = stack[7].m_obj;
lean_object* v___y_1582_ = stack[8].m_obj;
lean_object* v_res_1585_;
v_res_1585_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_fvar_1574_, v_a_1575_, v_a_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
stack->m_obj
 = v_res_1585_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object* v_fvar_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_fvar_1586_, v_a_1587_, v_a_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v_fvar_1586_);
return v_res_1596_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object* v_00_u03b2_1597_, lean_object* v_a_1598_, lean_object* v_x_1599_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1598_, v_x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1598_ = stack[1].m_obj;
lean_object* v_x_1599_ = stack[2].m_obj;
uint8_t v_res_1601_;
v_res_1601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_box(0), v_a_1598_, v_x_1599_);
stack->m_num = v_res_1601_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1602_, lean_object* v_a_1603_, lean_object* v_x_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(v_00_u03b2_1602_, v_a_1603_, v_x_1604_);
lean_dec(v_x_1604_);
lean_dec_ref(v_a_1603_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1(lean_object* v_00_u03b2_1607_, lean_object* v_data_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_data_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1610_, lean_object* v_i_1611_, lean_object* v_source_1612_, lean_object* v_target_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v_i_1611_, v_source_1612_, v_target_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_x_1616_, v_x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_instMonadEIO___redArg();
return v___x_1619_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = l_Lean_instInhabitedExpr;
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
return v___x_1625_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(lean_object* v_msg_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_toApplicative_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1699_; 
v___x_1634_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0);
v___x_1635_ = l_StateRefT_x27_instMonad___redArg(v___x_1634_);
v_toApplicative_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v___x_1635_, 1);
lean_dec(v_unused_1700_);
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1699_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_toApplicative_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1699_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_toFunctor_1640_; lean_object* v_toSeq_1641_; lean_object* v_toSeqLeft_1642_; lean_object* v_toSeqRight_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1697_; 
v_toFunctor_1640_ = lean_ctor_get(v_toApplicative_1636_, 0);
v_toSeq_1641_ = lean_ctor_get(v_toApplicative_1636_, 2);
v_toSeqLeft_1642_ = lean_ctor_get(v_toApplicative_1636_, 3);
v_toSeqRight_1643_ = lean_ctor_get(v_toApplicative_1636_, 4);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_toApplicative_1636_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_toApplicative_1636_, 1);
lean_dec(v_unused_1698_);
v___x_1645_ = v_toApplicative_1636_;
v_isShared_1646_ = v_isSharedCheck_1697_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_toSeqRight_1643_);
lean_inc(v_toSeqLeft_1642_);
lean_inc(v_toSeq_1641_);
lean_inc(v_toFunctor_1640_);
lean_dec(v_toApplicative_1636_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1697_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___f_1647_; lean_object* v___f_1648_; lean_object* v___f_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___x_1656_; 
v___f_1647_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1));
v___f_1648_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1640_);
v___f_1649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1649_, 0, v_toFunctor_1640_);
v___f_1650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1650_, 0, v_toFunctor_1640_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___f_1649_);
lean_ctor_set(v___x_1651_, 1, v___f_1650_);
v___f_1652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1652_, 0, v_toSeqRight_1643_);
v___f_1653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1653_, 0, v_toSeqLeft_1642_);
v___f_1654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1654_, 0, v_toSeq_1641_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 4, v___f_1652_);
lean_ctor_set(v___x_1645_, 3, v___f_1653_);
lean_ctor_set(v___x_1645_, 2, v___f_1654_);
lean_ctor_set(v___x_1645_, 1, v___f_1647_);
lean_ctor_set(v___x_1645_, 0, v___x_1651_);
v___x_1656_ = v___x_1645_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___f_1647_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v___f_1654_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v___f_1653_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v___f_1652_);
v___x_1656_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v___f_1648_);
lean_ctor_set(v___x_1638_, 0, v___x_1656_);
v___x_1658_ = v___x_1638_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___f_1648_);
v___x_1658_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1659_; lean_object* v_toApplicative_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1693_; 
v___x_1659_ = l_StateRefT_x27_instMonad___redArg(v___x_1658_);
v_toApplicative_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1659_, 1);
lean_dec(v_unused_1694_);
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1693_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_toApplicative_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1693_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_toFunctor_1664_; lean_object* v_toSeq_1665_; lean_object* v_toSeqLeft_1666_; lean_object* v_toSeqRight_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1691_; 
v_toFunctor_1664_ = lean_ctor_get(v_toApplicative_1660_, 0);
v_toSeq_1665_ = lean_ctor_get(v_toApplicative_1660_, 2);
v_toSeqLeft_1666_ = lean_ctor_get(v_toApplicative_1660_, 3);
v_toSeqRight_1667_ = lean_ctor_get(v_toApplicative_1660_, 4);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_toApplicative_1660_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v_toApplicative_1660_, 1);
lean_dec(v_unused_1692_);
v___x_1669_ = v_toApplicative_1660_;
v_isShared_1670_ = v_isSharedCheck_1691_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_toSeqRight_1667_);
lean_inc(v_toSeqLeft_1666_);
lean_inc(v_toSeq_1665_);
lean_inc(v_toFunctor_1664_);
lean_dec(v_toApplicative_1660_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1691_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___f_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___x_1680_; 
v___f_1671_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3));
v___f_1672_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1664_);
v___f_1673_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1673_, 0, v_toFunctor_1664_);
v___f_1674_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1674_, 0, v_toFunctor_1664_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___f_1673_);
lean_ctor_set(v___x_1675_, 1, v___f_1674_);
v___f_1676_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1676_, 0, v_toSeqRight_1667_);
v___f_1677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1677_, 0, v_toSeqLeft_1666_);
v___f_1678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1678_, 0, v_toSeq_1665_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 4, v___f_1676_);
lean_ctor_set(v___x_1669_, 3, v___f_1677_);
lean_ctor_set(v___x_1669_, 2, v___f_1678_);
lean_ctor_set(v___x_1669_, 1, v___f_1671_);
lean_ctor_set(v___x_1669_, 0, v___x_1675_);
v___x_1680_ = v___x_1669_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___f_1671_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v___f_1678_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v___f_1677_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v___f_1676_);
v___x_1680_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___f_1672_);
lean_ctor_set(v___x_1662_, 0, v___x_1680_);
v___x_1682_ = v___x_1662_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___f_1672_);
v___x_1682_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___f_1686_; lean_object* v___x_12394__overap_1687_; lean_object* v___x_1688_; 
v___x_1683_ = l_StateRefT_x27_instMonad___redArg(v___x_1682_);
v___x_1684_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5);
v___x_1685_ = l_instInhabitedOfMonad___redArg(v___x_1683_, v___x_1684_);
v___f_1686_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1686_, 0, v___x_1685_);
v___x_12394__overap_1687_ = lean_panic_fn_borrowed(v___f_1686_, v_msg_1626_);
lean_dec_ref(v___f_1686_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
v___x_1688_ = lean_apply_7(v___x_12394__overap_1687_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, lean_box(0));
return v___x_1688_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1626_ = stack[0].m_obj;
lean_object* v___y_1627_ = stack[1].m_obj;
lean_object* v___y_1628_ = stack[2].m_obj;
lean_object* v___y_1629_ = stack[3].m_obj;
lean_object* v___y_1630_ = stack[4].m_obj;
lean_object* v___y_1631_ = stack[5].m_obj;
lean_object* v___y_1632_ = stack[6].m_obj;
lean_object* v_res_1701_;
v_res_1701_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
stack->m_obj
 = v_res_1701_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(lean_object* v_msg_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1710_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(lean_object* v_msgData_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v_env_1718_; uint8_t v___x_1719_; lean_object* v_env_1720_; lean_object* v___x_1721_; lean_object* v_toCold_1722_; lean_object* v_mctx_1723_; lean_object* v_lctx_1724_; lean_object* v_options_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1717_ = lean_st_ref_get(v___y_1715_);
v_env_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc_ref(v_env_1718_);
lean_dec(v___x_1717_);
v___x_1719_ = 0;
v_env_1720_ = l_Lean_Environment_setRecordingDeps(v_env_1718_, v___x_1719_);
v___x_1721_ = lean_st_ref_get(v___y_1713_);
v_toCold_1722_ = lean_ctor_get(v___y_1714_, 0);
v_mctx_1723_ = lean_ctor_get(v___x_1721_, 0);
lean_inc_ref(v_mctx_1723_);
lean_dec(v___x_1721_);
v_lctx_1724_ = lean_ctor_get(v___y_1712_, 2);
v_options_1725_ = lean_ctor_get(v_toCold_1722_, 2);
lean_inc_ref(v_options_1725_);
lean_inc_ref(v_lctx_1724_);
v___x_1726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1726_, 0, v_env_1720_);
lean_ctor_set(v___x_1726_, 1, v_mctx_1723_);
lean_ctor_set(v___x_1726_, 2, v_lctx_1724_);
lean_ctor_set(v___x_1726_, 3, v_options_1725_);
v___x_1727_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_msgData_1711_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1711_ = stack[0].m_obj;
lean_object* v___y_1712_ = stack[1].m_obj;
lean_object* v___y_1713_ = stack[2].m_obj;
lean_object* v___y_1714_ = stack[3].m_obj;
lean_object* v___y_1715_ = stack[4].m_obj;
lean_object* v_res_1729_;
v_res_1729_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
stack->m_obj
 = v_res_1729_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(lean_object* v_msgData_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1736_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(lean_object* v_msg_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_ref_1743_; lean_object* v___x_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1753_; 
v_ref_1743_ = lean_ctor_get(v___y_1740_, 2);
v___x_1744_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msg_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_inc(v_ref_1743_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_ref_1743_);
lean_ctor_set(v___x_1749_, 1, v_a_1745_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 1);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1737_ = stack[0].m_obj;
lean_object* v___y_1738_ = stack[1].m_obj;
lean_object* v___y_1739_ = stack[2].m_obj;
lean_object* v___y_1740_ = stack[3].m_obj;
lean_object* v___y_1741_ = stack[4].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1761_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1762_, lean_object* v_msg_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_toCold_1771_; lean_object* v_currRecDepth_1772_; lean_object* v_ref_1773_; uint16_t v_optionFlags_1774_; uint8_t v_suppressElabErrors_1775_; uint8_t v_isRecordingDeps_1776_; lean_object* v_ref_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_toCold_1771_ = lean_ctor_get(v___y_1768_, 0);
v_currRecDepth_1772_ = lean_ctor_get(v___y_1768_, 1);
v_ref_1773_ = lean_ctor_get(v___y_1768_, 2);
v_optionFlags_1774_ = lean_ctor_get_uint16(v___y_1768_, sizeof(void*)*3);
v_suppressElabErrors_1775_ = lean_ctor_get_uint8(v___y_1768_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1776_ = lean_ctor_get_uint8(v___y_1768_, sizeof(void*)*3 + 3);
v_ref_1777_ = l_Lean_replaceRef(v_ref_1762_, v_ref_1773_);
lean_inc(v_currRecDepth_1772_);
lean_inc_ref(v_toCold_1771_);
v___x_1778_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1778_, 0, v_toCold_1771_);
lean_ctor_set(v___x_1778_, 1, v_currRecDepth_1772_);
lean_ctor_set(v___x_1778_, 2, v_ref_1777_);
lean_ctor_set_uint16(v___x_1778_, sizeof(void*)*3, v_optionFlags_1774_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 2, v_suppressElabErrors_1775_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 3, v_isRecordingDeps_1776_);
v___x_1779_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1763_, v___y_1766_, v___y_1767_, v___x_1778_, v___y_1769_);
lean_dec_ref_known(v___x_1778_, 3);
return v___x_1779_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1762_ = stack[0].m_obj;
lean_object* v_msg_1763_ = stack[1].m_obj;
lean_object* v___y_1764_ = stack[2].m_obj;
lean_object* v___y_1765_ = stack[3].m_obj;
lean_object* v___y_1766_ = stack[4].m_obj;
lean_object* v___y_1767_ = stack[5].m_obj;
lean_object* v___y_1768_ = stack[6].m_obj;
lean_object* v___y_1769_ = stack[7].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1762_, v_msg_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1781_, lean_object* v_msg_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1781_, v_msg_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v_ref_1781_);
return v_res_1790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
lean_ctor_set(v___x_1797_, 3, v___x_1796_);
lean_ctor_set(v___x_1797_, 4, v___x_1795_);
lean_ctor_set(v___x_1797_, 5, v___x_1795_);
lean_ctor_set(v___x_1797_, 6, v___x_1795_);
lean_ctor_set(v___x_1797_, 7, v___x_1795_);
lean_ctor_set(v___x_1797_, 8, v___x_1795_);
lean_ctor_set(v___x_1797_, 9, v___x_1795_);
lean_ctor_set(v___x_1797_, 10, v___x_1795_);
lean_ctor_set(v___x_1797_, 11, v___x_1794_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_unsigned_to_nat(32u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1801_ = ((size_t)5ULL);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_unsigned_to_nat(32u);
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1803_);
v___x_1805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1806_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1804_);
lean_ctor_set(v___x_1806_, 2, v___x_1802_);
lean_ctor_set(v___x_1806_, 3, v___x_1802_);
lean_ctor_set_usize(v___x_1806_, 4, v___x_1801_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_box(1);
v___x_1808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___x_1808_);
lean_ctor_set(v___x_1810_, 2, v___x_1807_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1844_, lean_object* v_declHint_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_env_1850_; uint8_t v___x_1851_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_st_ref_get(v___y_1846_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = l_Lean_Name_isAnonymous(v_declHint_1845_);
if (v___x_1851_ == 0)
{
uint8_t v_isExporting_1852_; 
v_isExporting_1852_ = lean_ctor_get_uint8(v_env_1850_, sizeof(void*)*13);
if (v_isExporting_1852_ == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_msg_1844_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
lean_inc_ref(v_env_1850_);
v___x_1854_ = l_Lean_Environment_setExporting(v_env_1850_, v___x_1851_);
lean_inc(v_declHint_1845_);
lean_inc_ref(v___x_1854_);
v___x_1855_ = l_Lean_Environment_contains(v___x_1854_, v_declHint_1845_, v_isExporting_1852_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1854_);
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_msg_1844_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_c_1862_; lean_object* v___x_1863_; 
v___x_1857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_1858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1859_ = l_Lean_Options_empty;
v___x_1860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1854_);
lean_ctor_set(v___x_1860_, 1, v___x_1857_);
lean_ctor_set(v___x_1860_, 2, v___x_1858_);
lean_ctor_set(v___x_1860_, 3, v___x_1859_);
lean_inc(v_declHint_1845_);
v___x_1861_ = l_Lean_MessageData_ofConstName(v_declHint_1845_, v___x_1851_);
v_c_1862_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1862_, 0, v___x_1860_);
lean_ctor_set(v_c_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1850_, v_declHint_1845_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_c_1862_);
v___x_1866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_MessageData_note(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_msg_1844_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
else
{
lean_object* v_val_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1927_; 
v_val_1871_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1873_ = v___x_1863_;
v_isShared_1874_ = v_isSharedCheck_1927_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_val_1871_);
lean_dec(v___x_1863_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1927_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v_modules_1876_; lean_object* v_moduleNames_1877_; lean_object* v_mod_1878_; uint8_t v___y_1880_; uint8_t v___x_1910_; 
v___x_1875_ = l_Lean_Environment_header(v_env_1850_);
lean_dec_ref(v_env_1850_);
v_modules_1876_ = lean_ctor_get(v___x_1875_, 3);
lean_inc_ref(v_modules_1876_);
v_moduleNames_1877_ = lean_ctor_get(v___x_1875_, 4);
lean_inc_ref(v_moduleNames_1877_);
lean_dec_ref(v___x_1875_);
v_mod_1878_ = lean_array_get(v___x_1848_, v_moduleNames_1877_, v_val_1871_);
lean_dec_ref(v_moduleNames_1877_);
v___x_1910_ = l_Lean_isPrivateName(v_declHint_1845_);
lean_dec(v_declHint_1845_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = lean_array_get_size(v_modules_1876_);
v___x_1912_ = lean_nat_dec_lt(v_val_1871_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_dec_ref(v_modules_1876_);
lean_dec(v_val_1871_);
v___y_1880_ = v___x_1910_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1913_; lean_object* v_toImport_1914_; uint8_t v_isExported_1915_; 
v___x_1913_ = lean_array_fget(v_modules_1876_, v_val_1871_);
lean_dec(v_val_1871_);
lean_dec_ref(v_modules_1876_);
v_toImport_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_toImport_1914_);
lean_dec(v___x_1913_);
v_isExported_1915_ = lean_ctor_get_uint8(v_toImport_1914_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1914_);
v___y_1880_ = v_isExported_1915_;
goto v___jp_1879_;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_modules_1876_);
lean_del_object(v___x_1873_);
lean_dec(v_val_1871_);
v___x_1916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v_c_1862_);
v___x_1918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_MessageData_ofName(v_mod_1878_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_MessageData_note(v___x_1923_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_msg_1844_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
v___jp_1879_:
{
if (v___y_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_c_1862_);
v___x_1883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_MessageData_ofName(v_mod_1878_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_MessageData_note(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_msg_1844_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1890_);
v___x_1892_ = v___x_1873_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v_c_1862_);
v___x_1896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = l_Lean_MessageData_ofName(v_mod_1878_);
lean_inc_ref(v___x_1898_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1898_);
v___x_1903_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_MessageData_note(v___x_1904_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_msg_1844_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1906_);
v___x_1908_ = v___x_1873_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
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
lean_object* v___x_1928_; 
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_msg_1844_);
return v___x_1928_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1844_ = stack[0].m_obj;
lean_object* v_declHint_1845_ = stack[1].m_obj;
lean_object* v___y_1846_ = stack[2].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1844_, v_declHint_1845_, v___y_1846_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1930_, lean_object* v_declHint_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1930_, v_declHint_1931_, v___y_1932_);
lean_dec(v___y_1932_);
return v_res_1934_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_1935_, lean_object* v_declHint_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1954_; 
v___x_1944_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1935_, v_declHint_1936_, v___y_1942_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1949_ = l_Lean_unknownIdentifierMessageTag;
v___x_1950_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v_a_1945_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1950_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1935_ = stack[0].m_obj;
lean_object* v_declHint_1936_ = stack[1].m_obj;
lean_object* v___y_1937_ = stack[2].m_obj;
lean_object* v___y_1938_ = stack[3].m_obj;
lean_object* v___y_1939_ = stack[4].m_obj;
lean_object* v___y_1940_ = stack[5].m_obj;
lean_object* v___y_1941_ = stack[6].m_obj;
lean_object* v___y_1942_ = stack[7].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1935_, v_declHint_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
stack->m_obj
 = v_res_1955_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_1956_, lean_object* v_declHint_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1956_, v_declHint_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1965_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_1966_, lean_object* v_msg_1967_, lean_object* v_declHint_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v_a_1977_; lean_object* v___x_1978_; 
v___x_1976_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1967_, v_declHint_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1966_, v_a_1977_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1978_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1966_ = stack[0].m_obj;
lean_object* v_msg_1967_ = stack[1].m_obj;
lean_object* v_declHint_1968_ = stack[2].m_obj;
lean_object* v___y_1969_ = stack[3].m_obj;
lean_object* v___y_1970_ = stack[4].m_obj;
lean_object* v___y_1971_ = stack[5].m_obj;
lean_object* v___y_1972_ = stack[6].m_obj;
lean_object* v___y_1973_ = stack[7].m_obj;
lean_object* v___y_1974_ = stack[8].m_obj;
lean_object* v_res_1979_;
v_res_1979_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1966_, v_msg_1967_, v_declHint_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
stack->m_obj
 = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1980_, lean_object* v_msg_1981_, lean_object* v_declHint_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1980_, v_msg_1981_, v_declHint_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v_ref_1980_);
return v_res_1990_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1993_ = l_Lean_stringToMessageData(v___x_1992_);
return v___x_1993_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1996_ = l_Lean_stringToMessageData(v___x_1995_);
return v___x_1996_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1997_, lean_object* v_constName_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2006_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_2007_ = 0;
lean_inc(v_constName_1998_);
v___x_2008_ = l_Lean_MessageData_ofConstName(v_constName_1998_, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2006_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1997_, v___x_2011_, v_constName_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
return v___x_2012_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1997_ = stack[0].m_obj;
lean_object* v_constName_1998_ = stack[1].m_obj;
lean_object* v___y_1999_ = stack[2].m_obj;
lean_object* v___y_2000_ = stack[3].m_obj;
lean_object* v___y_2001_ = stack[4].m_obj;
lean_object* v___y_2002_ = stack[5].m_obj;
lean_object* v___y_2003_ = stack[6].m_obj;
lean_object* v___y_2004_ = stack[7].m_obj;
lean_object* v_res_2013_;
v_res_2013_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1997_, v_constName_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
stack->m_obj
 = v_res_2013_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_2014_, lean_object* v_constName_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2014_, v_constName_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v_ref_2014_);
return v_res_2023_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object* v_constName_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_ref_2032_; lean_object* v___x_2033_; 
v_ref_2032_ = lean_ctor_get(v___y_2029_, 2);
v___x_2033_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2032_, v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
return v___x_2033_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2024_ = stack[0].m_obj;
lean_object* v___y_2025_ = stack[1].m_obj;
lean_object* v___y_2026_ = stack[2].m_obj;
lean_object* v___y_2027_ = stack[3].m_obj;
lean_object* v___y_2028_ = stack[4].m_obj;
lean_object* v___y_2029_ = stack[5].m_obj;
lean_object* v___y_2030_ = stack[6].m_obj;
lean_object* v_res_2034_;
v_res_2034_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
stack->m_obj
 = v_res_2034_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2043_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(lean_object* v_constName_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v_env_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = lean_st_ref_get(v___y_2050_);
v_env_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_env_2053_);
lean_dec(v___x_2052_);
v___x_2054_ = 0;
lean_inc(v_constName_2044_);
v___x_2055_ = l_Lean_Environment_find_x3f(v_env_2053_, v_constName_2044_, v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2056_;
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_constName_2044_);
v_val_2057_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2055_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_val_2057_);
lean_dec(v___x_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 0);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_val_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2044_ = stack[0].m_obj;
lean_object* v___y_2045_ = stack[1].m_obj;
lean_object* v___y_2046_ = stack[2].m_obj;
lean_object* v___y_2047_ = stack[3].m_obj;
lean_object* v___y_2048_ = stack[4].m_obj;
lean_object* v___y_2049_ = stack[5].m_obj;
lean_object* v___y_2050_ = stack[6].m_obj;
lean_object* v_res_2065_;
v_res_2065_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
stack->m_obj
 = v_res_2065_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object* v_constName_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2));
v___x_2082_ = l_Lean_Expr_const___override(v___x_2081_, v___x_2080_);
return v___x_2082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5));
v___x_2086_ = lean_unsigned_to_nat(61u);
v___x_2087_ = lean_unsigned_to_nat(243u);
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4));
v___x_2089_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0));
v___x_2090_ = l_mkPanicMessageWithDecl(v___x_2089_, v___x_2088_, v___x_2087_, v___x_2086_, v___x_2085_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = l_Lean_Level_ofNat(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_box(0);
v___x_2157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39));
v___x_2161_ = l_Lean_Expr_const___override(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_box(0);
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43));
v___x_2166_ = l_Lean_mkConst(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_box(0);
v___x_2172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46));
v___x_2173_ = l_Lean_Expr_const___override(v___x_2172_, v___x_2171_);
return v___x_2173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50));
v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
return v___x_2179_;
}
}
static size_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52(void){
_start:
{
lean_object* v___x_2180_; size_t v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_isize_of_nat(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55));
v___x_2189_ = l_Lean_Expr_const___override(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57));
v___x_2194_ = l_Lean_Expr_const___override(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = lean_box(0);
v___x_2200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60));
v___x_2201_ = l_Lean_Expr_const___override(v___x_2200_, v___x_2199_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66));
v___x_2212_ = l_Lean_mkConst(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69));
v___x_2219_ = l_Lean_mkConst(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73));
v___x_2227_ = l_Lean_mkConst(v___x_2226_, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75));
v___x_2233_ = l_Lean_Expr_const___override(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79));
v___x_2241_ = l_Lean_mkConst(v___x_2240_, v___x_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81));
v___x_2247_ = l_Lean_Expr_const___override(v___x_2246_, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_box(0);
v___x_2254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85));
v___x_2255_ = l_Lean_mkConst(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = lean_box(0);
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87));
v___x_2261_ = l_Lean_Expr_const___override(v___x_2260_, v___x_2259_);
return v___x_2261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89));
v___x_2264_ = l_Lean_stringToMessageData(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91));
v___x_2269_ = l_Lean_mkConst(v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93));
v___x_2275_ = l_Lean_Expr_const___override(v___x_2274_, v___x_2273_);
return v___x_2275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95));
v___x_2278_ = l_Lean_stringToMessageData(v___x_2277_);
return v___x_2278_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97(void){
_start:
{
lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_int8_of_nat(v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_box(0);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98));
v___x_2285_ = l_Lean_Expr_const___override(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100));
v___x_2291_ = l_Lean_Expr_const___override(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102));
v___x_2294_ = l_Lean_stringToMessageData(v___x_2293_);
return v___x_2294_;
}
}
static uint16_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104(void){
_start:
{
lean_object* v___x_2295_; uint16_t v___x_2296_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_int16_of_nat(v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_box(0);
v___x_2300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105));
v___x_2301_ = l_Lean_Expr_const___override(v___x_2300_, v___x_2299_);
return v___x_2301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_box(0);
v___x_2306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107));
v___x_2307_ = l_Lean_Expr_const___override(v___x_2306_, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109));
v___x_2310_ = l_Lean_stringToMessageData(v___x_2309_);
return v___x_2310_;
}
}
static uint32_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111(void){
_start:
{
lean_object* v___x_2311_; uint32_t v___x_2312_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_int32_of_nat(v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112));
v___x_2317_ = l_Lean_Expr_const___override(v___x_2316_, v___x_2315_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114));
v___x_2323_ = l_Lean_Expr_const___override(v___x_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116));
v___x_2326_ = l_Lean_stringToMessageData(v___x_2325_);
return v___x_2326_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118(void){
_start:
{
lean_object* v___x_2327_; uint64_t v___x_2328_; 
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = lean_int64_of_nat(v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_box(0);
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119));
v___x_2333_ = l_Lean_Expr_const___override(v___x_2332_, v___x_2331_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_box(0);
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121));
v___x_2339_ = l_Lean_Expr_const___override(v___x_2338_, v___x_2337_);
return v___x_2339_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object* v_var_2340_, lean_object* v_value_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Lean_Expr_isFVar(v_var_2340_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___x_2427_; 
v___x_2365_ = lean_box(0);
lean_inc_ref(v_var_2340_);
v___x_2427_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_2340_, v_a_2345_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2876_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2876_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2876_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = l_Lean_Expr_cleanupAnnotations(v_a_2428_);
v___x_2433_ = l_Lean_Expr_isApp(v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v___x_2432_);
lean_del_object(v___x_2430_);
v___y_2367_ = v_a_2342_;
v___y_2368_ = v_a_2343_;
v___y_2369_ = v_a_2344_;
v___y_2370_ = v_a_2345_;
v___y_2371_ = v_a_2346_;
v___y_2372_ = v_a_2347_;
goto v___jp_2366_;
}
else
{
lean_object* v_arg_2434_; lean_object* v___y_2436_; lean_object* v___y_2442_; lean_object* v___y_2446_; lean_object* v___y_2450_; lean_object* v___y_2454_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_arg_2434_ = lean_ctor_get(v___x_2432_, 1);
lean_inc_ref(v_arg_2434_);
v___x_2457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2432_);
v___x_2458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9));
v___x_2459_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
lean_del_object(v___x_2430_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11));
v___x_2461_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13));
v___x_2463_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15));
v___x_2465_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17));
v___x_2467_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19));
v___x_2469_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21));
v___x_2471_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23));
v___x_2473_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25));
v___x_2475_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2474_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
lean_dec_ref(v_arg_2434_);
v___x_2476_ = l_Lean_Expr_isApp(v___x_2457_);
if (v___x_2476_ == 0)
{
lean_dec_ref(v___x_2457_);
v___y_2367_ = v_a_2342_;
v___y_2368_ = v_a_2343_;
v___y_2369_ = v_a_2344_;
v___y_2370_ = v_a_2345_;
v___y_2371_ = v_a_2346_;
v___y_2372_ = v_a_2347_;
goto v___jp_2366_;
}
else
{
lean_object* v_arg_2477_; lean_object* v___y_2479_; lean_object* v___y_2483_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v_arg_2477_ = lean_ctor_get(v___x_2457_, 1);
lean_inc_ref(v_arg_2477_);
v___x_2486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2457_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28));
v___x_2488_ = l_Lean_Expr_isConstOf(v___x_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30));
v___x_2490_ = l_Lean_Expr_isConstOf(v___x_2486_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32));
v___x_2492_ = l_Lean_Expr_isConstOf(v___x_2486_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33));
v___x_2494_ = l_Lean_Expr_isConstOf(v___x_2486_, v___x_2493_);
lean_dec_ref(v___x_2486_);
if (v___x_2494_ == 0)
{
lean_dec_ref(v_arg_2477_);
v___y_2367_ = v_a_2342_;
v___y_2368_ = v_a_2343_;
v___y_2369_ = v_a_2344_;
v___y_2370_ = v_a_2345_;
v___y_2371_ = v_a_2346_;
v___y_2372_ = v_a_2347_;
goto v___jp_2366_;
}
else
{
lean_object* v_w_2495_; lean_object* v_bv_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_var_2340_);
v_w_2495_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2496_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2498_ = v_value_2341_;
v_isShared_2499_ = v_isSharedCheck_2524_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_bv_2496_);
lean_inc(v_w_2495_);
lean_dec(v_value_2341_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2524_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = lean_unsigned_to_nat(32u);
v___x_2501_ = lean_nat_dec_eq(v_w_2495_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; 
lean_dec(v_bv_2496_);
lean_dec_ref(v_arg_2477_);
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35);
v___x_2503_ = l_Nat_reprFast(v_w_2495_);
v___x_2504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
v___x_2505_ = l_Lean_MessageData_ofFormat(v___x_2504_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set_tag(v___x_2498_, 7);
lean_ctor_set(v___x_2498_, 1, v___x_2505_);
lean_ctor_set(v___x_2498_, 0, v___x_2502_);
v___x_2507_ = v___x_2498_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2509_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2510_;
}
}
else
{
size_t v___x_2512_; lean_object* v___x_2513_; lean_object* v_r_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_dec(v_w_2495_);
v___x_2512_ = lean_usize_of_nat(v_bv_2496_);
lean_dec(v_bv_2496_);
v___x_2513_ = lean_usize_to_nat(v___x_2512_);
v_r_2514_ = l_Lean_mkRawNatLit(v___x_2513_);
v___x_2515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2516_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2514_);
v___x_2518_ = l_Lean_Expr_app___override(v___x_2517_, v_r_2514_);
v___x_2519_ = l_Lean_mkApp3(v___x_2515_, v___x_2516_, v_r_2514_, v___x_2518_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___x_2519_);
lean_ctor_set(v___x_2498_, 0, v_arg_2477_);
v___x_2521_ = v___x_2498_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_arg_2477_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
}
}
}
else
{
lean_object* v_w_2525_; lean_object* v_bv_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2554_; 
lean_dec_ref(v___x_2486_);
lean_dec_ref(v_var_2340_);
v_w_2525_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2526_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2528_ = v_value_2341_;
v_isShared_2529_ = v_isSharedCheck_2554_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_bv_2526_);
lean_inc(v_w_2525_);
lean_dec(v_value_2341_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2554_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = lean_unsigned_to_nat(64u);
v___x_2531_ = lean_nat_dec_eq(v_w_2525_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_dec(v_bv_2526_);
lean_dec_ref(v_arg_2477_);
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49);
v___x_2533_ = l_Nat_reprFast(v_w_2525_);
v___x_2534_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
v___x_2535_ = l_Lean_MessageData_ofFormat(v___x_2534_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 7);
lean_ctor_set(v___x_2528_, 1, v___x_2535_);
lean_ctor_set(v___x_2528_, 0, v___x_2532_);
v___x_2537_ = v___x_2528_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2539_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2540_;
}
}
else
{
size_t v___x_2542_; lean_object* v___x_2543_; lean_object* v_r_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_dec(v_w_2525_);
v___x_2542_ = lean_usize_of_nat(v_bv_2526_);
lean_dec(v_bv_2526_);
v___x_2543_ = lean_usize_to_nat(v___x_2542_);
v_r_2544_ = l_Lean_mkRawNatLit(v___x_2543_);
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2544_);
v___x_2548_ = l_Lean_Expr_app___override(v___x_2547_, v_r_2544_);
v___x_2549_ = l_Lean_mkApp3(v___x_2545_, v___x_2546_, v_r_2544_, v___x_2548_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2549_);
lean_ctor_set(v___x_2528_, 0, v_arg_2477_);
v___x_2551_ = v___x_2528_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_arg_2477_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
}
}
}
else
{
lean_object* v_w_2555_; lean_object* v_bv_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v___x_2486_);
lean_dec_ref(v_var_2340_);
v_w_2555_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2556_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2558_ = v_value_2341_;
v_isShared_2559_ = v_isSharedCheck_2587_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_bv_2556_);
lean_inc(v_w_2555_);
lean_dec(v_value_2341_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2587_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = lean_unsigned_to_nat(32u);
v___x_2561_ = lean_nat_dec_eq(v_w_2555_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
lean_dec(v_bv_2556_);
lean_dec_ref(v_arg_2477_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51);
v___x_2563_ = l_Nat_reprFast(v_w_2555_);
v___x_2564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
v___x_2565_ = l_Lean_MessageData_ofFormat(v___x_2564_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 7);
lean_ctor_set(v___x_2558_, 1, v___x_2565_);
lean_ctor_set(v___x_2558_, 0, v___x_2562_);
v___x_2567_ = v___x_2558_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2569_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2570_;
}
}
else
{
lean_object* v___x_2572_; size_t v___x_2573_; size_t v___x_2574_; uint8_t v___x_2575_; 
lean_del_object(v___x_2558_);
v___x_2572_ = l_BitVec_toInt(v_w_2555_, v_bv_2556_);
lean_dec(v_w_2555_);
v___x_2573_ = lean_isize_of_int(v___x_2572_);
lean_dec(v___x_2572_);
v___x_2574_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2575_ = lean_isize_dec_le(v___x_2574_, v___x_2573_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2578_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2579_ = lean_isize_to_int(v___x_2573_);
v___x_2580_ = lean_int_neg(v___x_2579_);
lean_dec(v___x_2579_);
v___x_2581_ = l_Int_toNat(v___x_2580_);
lean_dec(v___x_2580_);
v___x_2582_ = l_Lean_instToExprISize_mkNat(v___x_2581_);
v___x_2583_ = l_Lean_mkApp3(v___x_2576_, v___x_2577_, v___x_2578_, v___x_2582_);
v___y_2483_ = v___x_2583_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_isize_to_int(v___x_2573_);
v___x_2585_ = l_Int_toNat(v___x_2584_);
lean_dec(v___x_2584_);
v___x_2586_ = l_Lean_instToExprISize_mkNat(v___x_2585_);
v___y_2483_ = v___x_2586_;
goto v___jp_2482_;
}
}
}
}
}
else
{
lean_object* v_w_2588_; lean_object* v_bv_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___x_2486_);
lean_dec_ref(v_var_2340_);
v_w_2588_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2589_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2591_ = v_value_2341_;
v_isShared_2592_ = v_isSharedCheck_2620_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_bv_2589_);
lean_inc(v_w_2588_);
lean_dec(v_value_2341_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2620_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(64u);
v___x_2594_ = lean_nat_dec_eq(v_w_2588_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_bv_2589_);
lean_dec_ref(v_arg_2477_);
v___x_2595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63);
v___x_2596_ = l_Nat_reprFast(v_w_2588_);
v___x_2597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
v___x_2598_ = l_Lean_MessageData_ofFormat(v___x_2597_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set_tag(v___x_2591_, 7);
lean_ctor_set(v___x_2591_, 1, v___x_2598_);
lean_ctor_set(v___x_2591_, 0, v___x_2595_);
v___x_2600_ = v___x_2591_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2602_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2603_;
}
}
else
{
lean_object* v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; uint8_t v___x_2608_; 
lean_del_object(v___x_2591_);
v___x_2605_ = l_BitVec_toInt(v_w_2588_, v_bv_2589_);
lean_dec(v_w_2588_);
v___x_2606_ = lean_isize_of_int(v___x_2605_);
lean_dec(v___x_2605_);
v___x_2607_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2608_ = lean_isize_dec_le(v___x_2607_, v___x_2606_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2612_ = lean_isize_to_int(v___x_2606_);
v___x_2613_ = lean_int_neg(v___x_2612_);
lean_dec(v___x_2612_);
v___x_2614_ = l_Int_toNat(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2615_ = l_Lean_instToExprISize_mkNat(v___x_2614_);
v___x_2616_ = l_Lean_mkApp3(v___x_2609_, v___x_2610_, v___x_2611_, v___x_2615_);
v___y_2479_ = v___x_2616_;
goto v___jp_2478_;
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_isize_to_int(v___x_2606_);
v___x_2618_ = l_Int_toNat(v___x_2617_);
lean_dec(v___x_2617_);
v___x_2619_ = l_Lean_instToExprISize_mkNat(v___x_2618_);
v___y_2479_ = v___x_2619_;
goto v___jp_2478_;
}
}
}
}
v___jp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_arg_2477_);
lean_ctor_set(v___x_2480_, 1, v___y_2479_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_arg_2477_);
lean_ctor_set(v___x_2484_, 1, v___y_2483_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
}
else
{
lean_object* v_w_2621_; lean_object* v_bv_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2621_ = lean_ctor_get(v_value_2341_, 0);
lean_inc(v_w_2621_);
v_bv_2622_ = lean_ctor_get(v_value_2341_, 1);
lean_inc(v_bv_2622_);
lean_dec_ref(v_value_2341_);
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = l_BitVec_ofNat(v_w_2621_, v___x_2623_);
lean_dec(v_w_2621_);
v___x_2625_ = lean_nat_dec_eq(v_bv_2622_, v___x_2624_);
lean_dec(v___x_2624_);
lean_dec(v_bv_2622_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67);
v___y_2454_ = v___x_2626_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70);
v___y_2454_ = v___x_2627_;
goto v___jp_2453_;
}
}
}
else
{
lean_object* v_w_2628_; lean_object* v_bv_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2628_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2629_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2631_ = v_value_2341_;
v_isShared_2632_ = v_isSharedCheck_2657_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_bv_2629_);
lean_inc(v_w_2628_);
lean_dec(v_value_2341_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2657_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = lean_unsigned_to_nat(8u);
v___x_2634_ = lean_nat_dec_eq(v_w_2628_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v_bv_2629_);
lean_dec_ref(v_arg_2434_);
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72);
v___x_2636_ = l_Nat_reprFast(v_w_2628_);
v___x_2637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = l_Lean_MessageData_ofFormat(v___x_2637_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 7);
lean_ctor_set(v___x_2631_, 1, v___x_2638_);
lean_ctor_set(v___x_2631_, 0, v___x_2635_);
v___x_2640_ = v___x_2631_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2642_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2643_;
}
}
else
{
uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v_r_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_dec(v_w_2628_);
v___x_2645_ = lean_uint8_of_nat_mk(v_bv_2629_);
v___x_2646_ = lean_uint8_to_nat(v___x_2645_);
v_r_2647_ = l_Lean_mkRawNatLit(v___x_2646_);
v___x_2648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74);
v___x_2650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76);
lean_inc_ref(v_r_2647_);
v___x_2651_ = l_Lean_Expr_app___override(v___x_2650_, v_r_2647_);
v___x_2652_ = l_Lean_mkApp3(v___x_2648_, v___x_2649_, v_r_2647_, v___x_2651_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v___x_2652_);
lean_ctor_set(v___x_2631_, 0, v_arg_2434_);
v___x_2654_ = v___x_2631_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_arg_2434_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
}
}
}
}
else
{
lean_object* v_w_2658_; lean_object* v_bv_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2658_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2659_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2661_ = v_value_2341_;
v_isShared_2662_ = v_isSharedCheck_2687_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_bv_2659_);
lean_inc(v_w_2658_);
lean_dec(v_value_2341_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2687_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = lean_unsigned_to_nat(16u);
v___x_2664_ = lean_nat_dec_eq(v_w_2658_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_dec(v_bv_2659_);
lean_dec_ref(v_arg_2434_);
v___x_2665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78);
v___x_2666_ = l_Nat_reprFast(v_w_2658_);
v___x_2667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
v___x_2668_ = l_Lean_MessageData_ofFormat(v___x_2667_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 7);
lean_ctor_set(v___x_2661_, 1, v___x_2668_);
lean_ctor_set(v___x_2661_, 0, v___x_2665_);
v___x_2670_ = v___x_2661_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2672_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2673_;
}
}
else
{
uint16_t v___x_2675_; lean_object* v___x_2676_; lean_object* v_r_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec(v_w_2658_);
v___x_2675_ = lean_uint16_of_nat_mk(v_bv_2659_);
v___x_2676_ = lean_uint16_to_nat(v___x_2675_);
v_r_2677_ = l_Lean_mkRawNatLit(v___x_2676_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80);
v___x_2680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82);
lean_inc_ref(v_r_2677_);
v___x_2681_ = l_Lean_Expr_app___override(v___x_2680_, v_r_2677_);
v___x_2682_ = l_Lean_mkApp3(v___x_2678_, v___x_2679_, v_r_2677_, v___x_2681_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2682_);
lean_ctor_set(v___x_2661_, 0, v_arg_2434_);
v___x_2684_ = v___x_2661_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_arg_2434_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
}
}
}
else
{
lean_object* v_w_2688_; lean_object* v_bv_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2688_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2689_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2691_ = v_value_2341_;
v_isShared_2692_ = v_isSharedCheck_2717_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_bv_2689_);
lean_inc(v_w_2688_);
lean_dec(v_value_2341_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2717_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = lean_unsigned_to_nat(32u);
v___x_2694_ = lean_nat_dec_eq(v_w_2688_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec(v_bv_2689_);
lean_dec_ref(v_arg_2434_);
v___x_2695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84);
v___x_2696_ = l_Nat_reprFast(v_w_2688_);
v___x_2697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_ofFormat(v___x_2697_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 7);
lean_ctor_set(v___x_2691_, 1, v___x_2698_);
lean_ctor_set(v___x_2691_, 0, v___x_2695_);
v___x_2700_ = v___x_2691_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2702_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2703_;
}
}
else
{
uint32_t v___x_2705_; lean_object* v___x_2706_; lean_object* v_r_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_dec(v_w_2688_);
v___x_2705_ = lean_uint32_of_nat_mk(v_bv_2689_);
v___x_2706_ = lean_uint32_to_nat(v___x_2705_);
v_r_2707_ = l_Lean_mkRawNatLit(v___x_2706_);
v___x_2708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86);
v___x_2710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88);
lean_inc_ref(v_r_2707_);
v___x_2711_ = l_Lean_Expr_app___override(v___x_2710_, v_r_2707_);
v___x_2712_ = l_Lean_mkApp3(v___x_2708_, v___x_2709_, v_r_2707_, v___x_2711_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v___x_2712_);
lean_ctor_set(v___x_2691_, 0, v_arg_2434_);
v___x_2714_ = v___x_2691_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_arg_2434_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v_w_2718_; lean_object* v_bv_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2718_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2719_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2721_ = v_value_2341_;
v_isShared_2722_ = v_isSharedCheck_2747_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_bv_2719_);
lean_inc(v_w_2718_);
lean_dec(v_value_2341_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2747_;
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
lean_dec_ref(v_arg_2434_);
v___x_2725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90);
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
v___x_2733_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2732_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2733_;
}
}
else
{
uint64_t v___x_2735_; lean_object* v___x_2736_; lean_object* v_r_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
lean_dec(v_w_2718_);
v___x_2735_ = lean_uint64_of_nat_mk(v_bv_2719_);
v___x_2736_ = lean_uint64_to_nat(v___x_2735_);
v_r_2737_ = l_Lean_mkRawNatLit(v___x_2736_);
v___x_2738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92);
v___x_2740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94);
lean_inc_ref(v_r_2737_);
v___x_2741_ = l_Lean_Expr_app___override(v___x_2740_, v_r_2737_);
v___x_2742_ = l_Lean_mkApp3(v___x_2738_, v___x_2739_, v_r_2737_, v___x_2741_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 1, v___x_2742_);
lean_ctor_set(v___x_2721_, 0, v_arg_2434_);
v___x_2744_ = v___x_2721_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_arg_2434_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v_w_2748_; lean_object* v_bv_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2748_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2749_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2751_ = v_value_2341_;
v_isShared_2752_ = v_isSharedCheck_2779_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_bv_2749_);
lean_inc(v_w_2748_);
lean_dec(v_value_2341_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2779_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = lean_unsigned_to_nat(8u);
v___x_2754_ = lean_nat_dec_eq(v_w_2748_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
lean_dec(v_bv_2749_);
lean_dec_ref(v_arg_2434_);
v___x_2755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96);
v___x_2756_ = l_Nat_reprFast(v_w_2748_);
v___x_2757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
v___x_2758_ = l_Lean_MessageData_ofFormat(v___x_2757_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 7);
lean_ctor_set(v___x_2751_, 1, v___x_2758_);
lean_ctor_set(v___x_2751_, 0, v___x_2755_);
v___x_2760_ = v___x_2751_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2762_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2763_;
}
}
else
{
uint8_t v___x_2765_; uint8_t v___x_2766_; uint8_t v___x_2767_; 
lean_del_object(v___x_2751_);
lean_dec(v_w_2748_);
v___x_2765_ = lean_uint8_of_nat_mk(v_bv_2749_);
v___x_2766_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97);
v___x_2767_ = lean_int8_dec_le(v___x_2766_, v___x_2765_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99);
v___x_2770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101);
v___x_2771_ = lean_int8_to_int(v___x_2765_);
v___x_2772_ = lean_int_neg(v___x_2771_);
v___x_2773_ = l_Int_toNat(v___x_2772_);
lean_dec(v___x_2772_);
v___x_2774_ = l_Lean_instToExprInt8_mkNat(v___x_2773_);
v___x_2775_ = l_Lean_mkApp3(v___x_2768_, v___x_2769_, v___x_2770_, v___x_2774_);
v___y_2450_ = v___x_2775_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_int8_to_int(v___x_2765_);
v___x_2777_ = l_Int_toNat(v___x_2776_);
v___x_2778_ = l_Lean_instToExprInt8_mkNat(v___x_2777_);
v___y_2450_ = v___x_2778_;
goto v___jp_2449_;
}
}
}
}
}
else
{
lean_object* v_w_2780_; lean_object* v_bv_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2780_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2781_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2783_ = v_value_2341_;
v_isShared_2784_ = v_isSharedCheck_2811_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_bv_2781_);
lean_inc(v_w_2780_);
lean_dec(v_value_2341_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2811_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = lean_unsigned_to_nat(16u);
v___x_2786_ = lean_nat_dec_eq(v_w_2780_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
lean_dec(v_bv_2781_);
lean_dec_ref(v_arg_2434_);
v___x_2787_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103);
v___x_2788_ = l_Nat_reprFast(v_w_2780_);
v___x_2789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
v___x_2790_ = l_Lean_MessageData_ofFormat(v___x_2789_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 7);
lean_ctor_set(v___x_2783_, 1, v___x_2790_);
lean_ctor_set(v___x_2783_, 0, v___x_2787_);
v___x_2792_ = v___x_2783_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2794_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2795_;
}
}
else
{
uint16_t v___x_2797_; uint16_t v___x_2798_; uint8_t v___x_2799_; 
lean_del_object(v___x_2783_);
lean_dec(v_w_2780_);
v___x_2797_ = lean_uint16_of_nat_mk(v_bv_2781_);
v___x_2798_ = lean_uint16_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104);
v___x_2799_ = lean_int16_dec_le(v___x_2798_, v___x_2797_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106);
v___x_2802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108);
v___x_2803_ = lean_int16_to_int(v___x_2797_);
v___x_2804_ = lean_int_neg(v___x_2803_);
v___x_2805_ = l_Int_toNat(v___x_2804_);
lean_dec(v___x_2804_);
v___x_2806_ = l_Lean_instToExprInt16_mkNat(v___x_2805_);
v___x_2807_ = l_Lean_mkApp3(v___x_2800_, v___x_2801_, v___x_2802_, v___x_2806_);
v___y_2446_ = v___x_2807_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = lean_int16_to_int(v___x_2797_);
v___x_2809_ = l_Int_toNat(v___x_2808_);
v___x_2810_ = l_Lean_instToExprInt16_mkNat(v___x_2809_);
v___y_2446_ = v___x_2810_;
goto v___jp_2445_;
}
}
}
}
}
else
{
lean_object* v_w_2812_; lean_object* v_bv_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2812_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2813_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2815_ = v_value_2341_;
v_isShared_2816_ = v_isSharedCheck_2843_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_bv_2813_);
lean_inc(v_w_2812_);
lean_dec(v_value_2341_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2843_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = lean_unsigned_to_nat(32u);
v___x_2818_ = lean_nat_dec_eq(v_w_2812_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
lean_dec(v_bv_2813_);
lean_dec_ref(v_arg_2434_);
v___x_2819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110);
v___x_2820_ = l_Nat_reprFast(v_w_2812_);
v___x_2821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
v___x_2822_ = l_Lean_MessageData_ofFormat(v___x_2821_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 7);
lean_ctor_set(v___x_2815_, 1, v___x_2822_);
lean_ctor_set(v___x_2815_, 0, v___x_2819_);
v___x_2824_ = v___x_2815_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2826_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2827_;
}
}
else
{
uint32_t v___x_2829_; uint32_t v___x_2830_; uint8_t v___x_2831_; 
lean_del_object(v___x_2815_);
lean_dec(v_w_2812_);
v___x_2829_ = lean_uint32_of_nat_mk(v_bv_2813_);
v___x_2830_ = lean_uint32_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111);
v___x_2831_ = lean_int32_dec_le(v___x_2830_, v___x_2829_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113);
v___x_2834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115);
v___x_2835_ = lean_int32_to_int(v___x_2829_);
v___x_2836_ = lean_int_neg(v___x_2835_);
lean_dec(v___x_2835_);
v___x_2837_ = l_Int_toNat(v___x_2836_);
lean_dec(v___x_2836_);
v___x_2838_ = l_Lean_instToExprInt32_mkNat(v___x_2837_);
v___x_2839_ = l_Lean_mkApp3(v___x_2832_, v___x_2833_, v___x_2834_, v___x_2838_);
v___y_2442_ = v___x_2839_;
goto v___jp_2441_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = lean_int32_to_int(v___x_2829_);
v___x_2841_ = l_Int_toNat(v___x_2840_);
lean_dec(v___x_2840_);
v___x_2842_ = l_Lean_instToExprInt32_mkNat(v___x_2841_);
v___y_2442_ = v___x_2842_;
goto v___jp_2441_;
}
}
}
}
}
else
{
lean_object* v_w_2844_; lean_object* v_bv_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v___x_2457_);
lean_dec_ref(v_var_2340_);
v_w_2844_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2845_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2847_ = v_value_2341_;
v_isShared_2848_ = v_isSharedCheck_2875_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_bv_2845_);
lean_inc(v_w_2844_);
lean_dec(v_value_2341_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2875_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(64u);
v___x_2850_ = lean_nat_dec_eq(v_w_2844_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
lean_dec(v_bv_2845_);
lean_dec_ref(v_arg_2434_);
lean_del_object(v___x_2430_);
v___x_2851_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117);
v___x_2852_ = l_Nat_reprFast(v_w_2844_);
v___x_2853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
v___x_2854_ = l_Lean_MessageData_ofFormat(v___x_2853_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 7);
lean_ctor_set(v___x_2847_, 1, v___x_2854_);
lean_ctor_set(v___x_2847_, 0, v___x_2851_);
v___x_2856_ = v___x_2847_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2858_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2859_;
}
}
else
{
uint64_t v___x_2861_; uint64_t v___x_2862_; uint8_t v___x_2863_; 
lean_del_object(v___x_2847_);
lean_dec(v_w_2844_);
v___x_2861_ = lean_uint64_of_nat_mk(v_bv_2845_);
v___x_2862_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118);
v___x_2863_ = lean_int64_dec_le(v___x_2862_, v___x_2861_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120);
v___x_2866_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122);
v___x_2867_ = lean_int64_to_int_sint(v___x_2861_);
v___x_2868_ = lean_int_neg(v___x_2867_);
lean_dec(v___x_2867_);
v___x_2869_ = l_Int_toNat(v___x_2868_);
lean_dec(v___x_2868_);
v___x_2870_ = l_Lean_instToExprInt64_mkNat(v___x_2869_);
v___x_2871_ = l_Lean_mkApp3(v___x_2864_, v___x_2865_, v___x_2866_, v___x_2870_);
v___y_2436_ = v___x_2871_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_int64_to_int_sint(v___x_2861_);
v___x_2873_ = l_Int_toNat(v___x_2872_);
lean_dec(v___x_2872_);
v___x_2874_ = l_Lean_instToExprInt64_mkNat(v___x_2873_);
v___y_2436_ = v___x_2874_;
goto v___jp_2435_;
}
}
}
}
v___jp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v_arg_2434_);
lean_ctor_set(v___x_2437_, 1, v___y_2436_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2437_);
v___x_2439_ = v___x_2430_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
v___jp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v_arg_2434_);
lean_ctor_set(v___x_2443_, 1, v___y_2442_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
v___jp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_arg_2434_);
lean_ctor_set(v___x_2447_, 1, v___y_2446_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
v___jp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v_arg_2434_);
lean_ctor_set(v___x_2451_, 1, v___y_2450_);
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
v___jp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
lean_inc_ref(v___y_2454_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_arg_2434_);
lean_ctor_set(v___x_2455_, 1, v___y_2454_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v_value_2341_);
lean_dec_ref(v_var_2340_);
v_a_2877_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2427_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2427_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
v___jp_2366_:
{
if (lean_obj_tag(v_var_2340_) == 5)
{
lean_object* v_fn_2373_; 
v_fn_2373_ = lean_ctor_get(v_var_2340_, 0);
if (lean_obj_tag(v_fn_2373_) == 4)
{
lean_object* v_arg_2374_; lean_object* v_declName_2375_; lean_object* v_us_2376_; lean_object* v___x_2377_; lean_object* v_env_2378_; lean_object* v___x_2379_; 
v_arg_2374_ = lean_ctor_get(v_var_2340_, 1);
v_declName_2375_ = lean_ctor_get(v_fn_2373_, 0);
v_us_2376_ = lean_ctor_get(v_fn_2373_, 1);
v___x_2377_ = lean_st_ref_get(v___y_2372_);
v_env_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc_ref(v_env_2378_);
lean_dec(v___x_2377_);
lean_inc(v_declName_2375_);
v___x_2379_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecType_x3f(v_env_2378_, v_declName_2375_);
if (lean_obj_tag(v___x_2379_) == 1)
{
lean_object* v_val_2380_; lean_object* v___x_2381_; 
lean_inc(v_us_2376_);
lean_inc_ref(v_arg_2374_);
lean_dec_ref_known(v_var_2340_, 2);
v_val_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_val_2380_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2404_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2404_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2404_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
if (lean_obj_tag(v_a_2382_) == 5)
{
lean_object* v_val_2386_; lean_object* v_ctors_2387_; lean_object* v_bv_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2400_; 
v_val_2386_ = lean_ctor_get(v_a_2382_, 0);
lean_inc_ref(v_val_2386_);
lean_dec_ref_known(v_a_2382_, 1);
v_ctors_2387_ = lean_ctor_get(v_val_2386_, 4);
lean_inc(v_ctors_2387_);
lean_dec_ref(v_val_2386_);
v_bv_2388_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; 
v_unused_2401_ = lean_ctor_get(v_value_2341_, 0);
lean_dec(v_unused_2401_);
v___x_2390_ = v_value_2341_;
v_isShared_2391_ = v_isSharedCheck_2400_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_bv_2388_);
lean_dec(v_value_2341_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2400_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2392_ = l_List_get_x21Internal___redArg(v___x_2365_, v_ctors_2387_, v_bv_2388_);
lean_dec(v_ctors_2387_);
v___x_2393_ = l_Lean_mkConst(v___x_2392_, v_us_2376_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2393_);
lean_ctor_set(v___x_2390_, 0, v_arg_2374_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_arg_2374_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2397_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2395_);
v___x_2397_ = v___x_2384_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_del_object(v___x_2384_);
lean_dec(v_a_2382_);
lean_dec(v_us_2376_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_value_2341_);
v___x_2402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6);
v___x_2403_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v___x_2402_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2403_;
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_us_2376_);
lean_dec_ref(v_arg_2374_);
lean_dec_ref(v_value_2341_);
v_a_2405_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2381_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2381_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_w_2413_; lean_object* v_bv_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v___x_2379_);
v_w_2413_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2414_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2416_ = v_value_2341_;
v_isShared_2417_ = v_isSharedCheck_2426_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_bv_2414_);
lean_inc(v_w_2413_);
lean_dec(v_value_2341_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2426_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2419_ = l_Lean_mkNatLit(v_w_2413_);
v___x_2420_ = l_Lean_mkNatLit(v_bv_2414_);
v___x_2421_ = l_Lean_mkAppB(v___x_2418_, v___x_2419_, v___x_2420_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2421_);
lean_ctor_set(v___x_2416_, 0, v_var_2340_);
v___x_2423_ = v___x_2416_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_var_2340_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
}
}
else
{
goto v___jp_2349_;
}
}
else
{
goto v___jp_2349_;
}
}
}
else
{
lean_object* v_w_2885_; lean_object* v_bv_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2898_; 
v_w_2885_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2886_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2888_ = v_value_2341_;
v_isShared_2889_ = v_isSharedCheck_2898_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_bv_2886_);
lean_inc(v_w_2885_);
lean_dec(v_value_2341_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2898_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2891_ = l_Lean_mkNatLit(v_w_2885_);
v___x_2892_ = l_Lean_mkNatLit(v_bv_2886_);
v___x_2893_ = l_Lean_mkAppB(v___x_2890_, v___x_2891_, v___x_2892_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2893_);
lean_ctor_set(v___x_2888_, 0, v_var_2340_);
v___x_2895_ = v___x_2888_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_var_2340_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
}
v___jp_2349_:
{
lean_object* v_w_2350_; lean_object* v_bv_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2363_; 
v_w_2350_ = lean_ctor_get(v_value_2341_, 0);
v_bv_2351_ = lean_ctor_get(v_value_2341_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_value_2341_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2353_ = v_value_2341_;
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_bv_2351_);
lean_inc(v_w_2350_);
lean_dec(v_value_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2356_ = l_Lean_mkNatLit(v_w_2350_);
v___x_2357_ = l_Lean_mkNatLit(v_bv_2351_);
v___x_2358_ = l_Lean_mkAppB(v___x_2355_, v___x_2356_, v___x_2357_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v___x_2358_);
lean_ctor_set(v___x_2353_, 0, v_var_2340_);
v___x_2360_ = v___x_2353_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_var_2340_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_0interp(lean_interpreter_value* stack)
{
lean_object* v_var_2340_ = stack[0].m_obj;
lean_object* v_value_2341_ = stack[1].m_obj;
lean_object* v_a_2342_ = stack[2].m_obj;
lean_object* v_a_2343_ = stack[3].m_obj;
lean_object* v_a_2344_ = stack[4].m_obj;
lean_object* v_a_2345_ = stack[5].m_obj;
lean_object* v_a_2346_ = stack[6].m_obj;
lean_object* v_a_2347_ = stack[7].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_2340_, v_value_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object* v_var_2900_, lean_object* v_value_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_2900_, v_value_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2909_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_object* v_00_u03b1_2910_, lean_object* v_msg_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_2911_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2911_ = stack[1].m_obj;
lean_object* v___y_2912_ = stack[2].m_obj;
lean_object* v___y_2913_ = stack[3].m_obj;
lean_object* v___y_2914_ = stack[4].m_obj;
lean_object* v___y_2915_ = stack[5].m_obj;
lean_object* v___y_2916_ = stack[6].m_obj;
lean_object* v___y_2917_ = stack[7].m_obj;
lean_object* v_res_2920_;
v_res_2920_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_box(0), v_msg_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
stack->m_obj
 = v_res_2920_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(lean_object* v_00_u03b1_2921_, lean_object* v_msg_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(v_00_u03b1_2921_, v_msg_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2930_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object* v_00_u03b1_2931_, lean_object* v_constName_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2932_ = stack[1].m_obj;
lean_object* v___y_2933_ = stack[2].m_obj;
lean_object* v___y_2934_ = stack[3].m_obj;
lean_object* v___y_2935_ = stack[4].m_obj;
lean_object* v___y_2936_ = stack[5].m_obj;
lean_object* v___y_2937_ = stack[6].m_obj;
lean_object* v___y_2938_ = stack[7].m_obj;
lean_object* v_res_2941_;
v_res_2941_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_box(0), v_constName_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
stack->m_obj
 = v_res_2941_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_constName_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(v_00_u03b1_2942_, v_constName_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
return v_res_2951_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2952_, lean_object* v_ref_2953_, lean_object* v_constName_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2953_, v_constName_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2953_ = stack[1].m_obj;
lean_object* v_constName_2954_ = stack[2].m_obj;
lean_object* v___y_2955_ = stack[3].m_obj;
lean_object* v___y_2956_ = stack[4].m_obj;
lean_object* v___y_2957_ = stack[5].m_obj;
lean_object* v___y_2958_ = stack[6].m_obj;
lean_object* v___y_2959_ = stack[7].m_obj;
lean_object* v___y_2960_ = stack[8].m_obj;
lean_object* v_res_2963_;
v_res_2963_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_box(0), v_ref_2953_, v_constName_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
stack->m_obj
 = v_res_2963_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_ref_2965_, lean_object* v_constName_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(v_00_u03b1_2964_, v_ref_2965_, v_constName_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v_ref_2965_);
return v_res_2974_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_2975_, lean_object* v_ref_2976_, lean_object* v_msg_2977_, lean_object* v_declHint_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2976_, v_msg_2977_, v_declHint_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2976_ = stack[1].m_obj;
lean_object* v_msg_2977_ = stack[2].m_obj;
lean_object* v_declHint_2978_ = stack[3].m_obj;
lean_object* v___y_2979_ = stack[4].m_obj;
lean_object* v___y_2980_ = stack[5].m_obj;
lean_object* v___y_2981_ = stack[6].m_obj;
lean_object* v___y_2982_ = stack[7].m_obj;
lean_object* v___y_2983_ = stack[8].m_obj;
lean_object* v___y_2984_ = stack[9].m_obj;
lean_object* v_res_2987_;
v_res_2987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_box(0), v_ref_2976_, v_msg_2977_, v_declHint_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
stack->m_obj
 = v_res_2987_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_ref_2989_, lean_object* v_msg_2990_, lean_object* v_declHint_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_2988_, v_ref_2989_, v_msg_2990_, v_declHint_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v_ref_2989_);
return v_res_2999_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_3000_, lean_object* v_declHint_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_3000_, v_declHint_3001_, v___y_3007_);
return v___x_3009_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3000_ = stack[0].m_obj;
lean_object* v_declHint_3001_ = stack[1].m_obj;
lean_object* v___y_3002_ = stack[2].m_obj;
lean_object* v___y_3003_ = stack[3].m_obj;
lean_object* v___y_3004_ = stack[4].m_obj;
lean_object* v___y_3005_ = stack[5].m_obj;
lean_object* v___y_3006_ = stack[6].m_obj;
lean_object* v___y_3007_ = stack[7].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_3000_, v_declHint_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
stack->m_obj
 = v_res_3010_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3011_, lean_object* v_declHint_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_3011_, v_declHint_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3020_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3021_, lean_object* v_ref_3022_, lean_object* v_msg_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_3022_, v_msg_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3022_ = stack[1].m_obj;
lean_object* v_msg_3023_ = stack[2].m_obj;
lean_object* v___y_3024_ = stack[3].m_obj;
lean_object* v___y_3025_ = stack[4].m_obj;
lean_object* v___y_3026_ = stack[5].m_obj;
lean_object* v___y_3027_ = stack[6].m_obj;
lean_object* v___y_3028_ = stack[7].m_obj;
lean_object* v___y_3029_ = stack[8].m_obj;
lean_object* v_res_3032_;
v_res_3032_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_box(0), v_ref_3022_, v_msg_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
stack->m_obj
 = v_res_3032_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3033_, lean_object* v_ref_3034_, lean_object* v_msg_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_3033_, v_ref_3034_, v_msg_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v_ref_3034_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_3044_, lean_object* v_x_3045_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
return v_x_3044_;
}
else
{
lean_object* v_key_3046_; lean_object* v_value_3047_; lean_object* v_tail_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3071_; 
v_key_3046_ = lean_ctor_get(v_x_3045_, 0);
v_value_3047_ = lean_ctor_get(v_x_3045_, 1);
v_tail_3048_ = lean_ctor_get(v_x_3045_, 2);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_x_3045_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3050_ = v_x_3045_;
v_isShared_3051_ = v_isSharedCheck_3071_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_tail_3048_);
lean_inc(v_value_3047_);
lean_inc(v_key_3046_);
lean_dec(v_x_3045_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3071_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; uint64_t v___x_3053_; uint64_t v___x_3054_; uint64_t v___x_3055_; uint64_t v_fold_3056_; uint64_t v___x_3057_; uint64_t v___x_3058_; uint64_t v___x_3059_; size_t v___x_3060_; size_t v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v___x_3052_ = lean_array_get_size(v_x_3044_);
v___x_3053_ = l_Lean_Expr_hash(v_key_3046_);
v___x_3054_ = 32ULL;
v___x_3055_ = lean_uint64_shift_right(v___x_3053_, v___x_3054_);
v_fold_3056_ = lean_uint64_xor(v___x_3053_, v___x_3055_);
v___x_3057_ = 16ULL;
v___x_3058_ = lean_uint64_shift_right(v_fold_3056_, v___x_3057_);
v___x_3059_ = lean_uint64_xor(v_fold_3056_, v___x_3058_);
v___x_3060_ = lean_uint64_to_usize(v___x_3059_);
v___x_3061_ = lean_usize_of_nat(v___x_3052_);
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_sub(v___x_3061_, v___x_3062_);
v___x_3064_ = lean_usize_land(v___x_3060_, v___x_3063_);
v___x_3065_ = lean_array_uget_borrowed(v_x_3044_, v___x_3064_);
lean_inc(v___x_3065_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 2, v___x_3065_);
v___x_3067_ = v___x_3050_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_key_3046_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_value_3047_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_array_uset(v_x_3044_, v___x_3064_, v___x_3067_);
v_x_3044_ = v___x_3068_;
v_x_3045_ = v_tail_3048_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3072_, lean_object* v_source_3073_, lean_object* v_target_3074_){
_start:
{
lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = lean_array_get_size(v_source_3073_);
v___x_3076_ = lean_nat_dec_lt(v_i_3072_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_dec_ref(v_source_3073_);
lean_dec(v_i_3072_);
return v_target_3074_;
}
else
{
lean_object* v_es_3077_; lean_object* v___x_3078_; lean_object* v_source_3079_; lean_object* v_target_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_es_3077_ = lean_array_fget(v_source_3073_, v_i_3072_);
v___x_3078_ = lean_box(0);
v_source_3079_ = lean_array_fset(v_source_3073_, v_i_3072_, v___x_3078_);
v_target_3080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(v_target_3074_, v_es_3077_);
v___x_3081_ = lean_unsigned_to_nat(1u);
v___x_3082_ = lean_nat_add(v_i_3072_, v___x_3081_);
lean_dec(v_i_3072_);
v_i_3072_ = v___x_3082_;
v_source_3073_ = v_source_3079_;
v_target_3074_ = v_target_3080_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(lean_object* v_data_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_nbuckets_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3085_ = lean_array_get_size(v_data_3084_);
v___x_3086_ = lean_unsigned_to_nat(2u);
v_nbuckets_3087_ = lean_nat_mul(v___x_3085_, v___x_3086_);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_mk_array(v_nbuckets_3087_, v___x_3089_);
v___x_3091_ = lean_array_propagate_mark(v_data_3084_, v___x_3090_);
v___x_3092_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v___x_3088_, v_data_3084_, v___x_3091_);
return v___x_3092_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object* v_a_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
uint8_t v___x_3095_; 
v___x_3095_ = 0;
return v___x_3095_;
}
else
{
lean_object* v_key_3096_; lean_object* v_tail_3097_; uint8_t v___x_3098_; 
v_key_3096_ = lean_ctor_get(v_x_3094_, 0);
v_tail_3097_ = lean_ctor_get(v_x_3094_, 2);
v___x_3098_ = lean_expr_eqv(v_key_3096_, v_a_3093_);
if (v___x_3098_ == 0)
{
v_x_3094_ = v_tail_3097_;
goto _start;
}
else
{
return v___x_3098_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3093_ = stack[0].m_obj;
lean_object* v_x_3094_ = stack[1].m_obj;
uint8_t v_res_3100_;
v_res_3100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3093_, v_x_3094_);
stack->m_num = v_res_3100_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object* v_a_3101_, lean_object* v_x_3102_){
_start:
{
uint8_t v_res_3103_; lean_object* v_r_3104_; 
v_res_3103_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3101_, v_x_3102_);
lean_dec(v_x_3102_);
lean_dec_ref(v_a_3101_);
v_r_3104_ = lean_box(v_res_3103_);
return v_r_3104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(lean_object* v_m_3105_, lean_object* v_a_3106_, lean_object* v_b_3107_){
_start:
{
lean_object* v_size_3108_; lean_object* v_buckets_3109_; lean_object* v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v___x_3113_; uint64_t v_fold_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; uint64_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; size_t v___x_3122_; lean_object* v_bkt_3123_; uint8_t v___x_3124_; 
v_size_3108_ = lean_ctor_get(v_m_3105_, 0);
v_buckets_3109_ = lean_ctor_get(v_m_3105_, 1);
v___x_3110_ = lean_array_get_size(v_buckets_3109_);
v___x_3111_ = l_Lean_Expr_hash(v_a_3106_);
v___x_3112_ = 32ULL;
v___x_3113_ = lean_uint64_shift_right(v___x_3111_, v___x_3112_);
v_fold_3114_ = lean_uint64_xor(v___x_3111_, v___x_3113_);
v___x_3115_ = 16ULL;
v___x_3116_ = lean_uint64_shift_right(v_fold_3114_, v___x_3115_);
v___x_3117_ = lean_uint64_xor(v_fold_3114_, v___x_3116_);
v___x_3118_ = lean_uint64_to_usize(v___x_3117_);
v___x_3119_ = lean_usize_of_nat(v___x_3110_);
v___x_3120_ = ((size_t)1ULL);
v___x_3121_ = lean_usize_sub(v___x_3119_, v___x_3120_);
v___x_3122_ = lean_usize_land(v___x_3118_, v___x_3121_);
v_bkt_3123_ = lean_array_uget_borrowed(v_buckets_3109_, v___x_3122_);
v___x_3124_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3106_, v_bkt_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3145_; 
lean_inc_ref(v_buckets_3109_);
lean_inc(v_size_3108_);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_m_3105_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; 
v_unused_3146_ = lean_ctor_get(v_m_3105_, 1);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_m_3105_, 0);
lean_dec(v_unused_3147_);
v___x_3126_ = v_m_3105_;
v_isShared_3127_ = v_isSharedCheck_3145_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v_m_3105_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3145_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v_size_x27_3129_; lean_object* v___x_3130_; lean_object* v_buckets_x27_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3128_ = lean_unsigned_to_nat(1u);
v_size_x27_3129_ = lean_nat_add(v_size_3108_, v___x_3128_);
lean_dec(v_size_3108_);
lean_inc(v_bkt_3123_);
v___x_3130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3106_);
lean_ctor_set(v___x_3130_, 1, v_b_3107_);
lean_ctor_set(v___x_3130_, 2, v_bkt_3123_);
v_buckets_x27_3131_ = lean_array_uset(v_buckets_3109_, v___x_3122_, v___x_3130_);
v___x_3132_ = lean_unsigned_to_nat(4u);
v___x_3133_ = lean_nat_mul(v_size_x27_3129_, v___x_3132_);
v___x_3134_ = lean_unsigned_to_nat(3u);
v___x_3135_ = lean_nat_div(v___x_3133_, v___x_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_array_get_size(v_buckets_x27_3131_);
v___x_3137_ = lean_nat_dec_le(v___x_3135_, v___x_3136_);
lean_dec(v___x_3135_);
if (v___x_3137_ == 0)
{
lean_object* v_val_3138_; lean_object* v___x_3140_; 
v_val_3138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_buckets_x27_3131_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v_val_3138_);
lean_ctor_set(v___x_3126_, 0, v_size_x27_3129_);
v___x_3140_ = v___x_3126_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_size_x27_3129_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_val_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
else
{
lean_object* v___x_3143_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v_buckets_x27_3131_);
lean_ctor_set(v___x_3126_, 0, v_size_x27_3129_);
v___x_3143_ = v___x_3126_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_size_x27_3129_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_buckets_x27_3131_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_dec(v_b_3107_);
lean_dec_ref(v_a_3106_);
return v_m_3105_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object* v_m_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_buckets_3150_; lean_object* v___x_3151_; uint64_t v___x_3152_; uint64_t v___x_3153_; uint64_t v___x_3154_; uint64_t v_fold_3155_; uint64_t v___x_3156_; uint64_t v___x_3157_; uint64_t v___x_3158_; size_t v___x_3159_; size_t v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_buckets_3150_ = lean_ctor_get(v_m_3148_, 1);
v___x_3151_ = lean_array_get_size(v_buckets_3150_);
v___x_3152_ = l_Lean_Expr_hash(v_a_3149_);
v___x_3153_ = 32ULL;
v___x_3154_ = lean_uint64_shift_right(v___x_3152_, v___x_3153_);
v_fold_3155_ = lean_uint64_xor(v___x_3152_, v___x_3154_);
v___x_3156_ = 16ULL;
v___x_3157_ = lean_uint64_shift_right(v_fold_3155_, v___x_3156_);
v___x_3158_ = lean_uint64_xor(v_fold_3155_, v___x_3157_);
v___x_3159_ = lean_uint64_to_usize(v___x_3158_);
v___x_3160_ = lean_usize_of_nat(v___x_3151_);
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_sub(v___x_3160_, v___x_3161_);
v___x_3163_ = lean_usize_land(v___x_3159_, v___x_3162_);
v___x_3164_ = lean_array_uget_borrowed(v_buckets_3150_, v___x_3163_);
v___x_3165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3149_, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3148_ = stack[0].m_obj;
lean_object* v_a_3149_ = stack[1].m_obj;
uint8_t v_res_3166_;
v_res_3166_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3148_, v_a_3149_);
stack->m_num = v_res_3166_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg___boxed(lean_object* v_m_3167_, lean_object* v_a_3168_){
_start:
{
uint8_t v_res_3169_; lean_object* v_r_3170_; 
v_res_3169_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3167_, v_a_3168_);
lean_dec_ref(v_a_3168_);
lean_dec_ref(v_m_3167_);
v_r_3170_ = lean_box(v_res_3169_);
return v_r_3170_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(lean_object* v_as_3171_, size_t v_sz_3172_, size_t v_i_3173_, lean_object* v_b_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_a_3183_; uint8_t v___x_3187_; 
v___x_3187_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_b_3174_);
return v___x_3188_;
}
else
{
lean_object* v_a_3189_; lean_object* v_fst_3190_; lean_object* v_snd_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_a_3189_ = lean_array_uget_borrowed(v_as_3171_, v_i_3173_);
v_fst_3190_ = lean_ctor_get(v_a_3189_, 0);
v_snd_3191_ = lean_ctor_get(v_a_3189_, 1);
v___x_3192_ = lean_box(0);
lean_inc(v_snd_3191_);
lean_inc(v_fst_3190_);
v___x_3193_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_3190_, v_snd_3191_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v_fst_3195_; lean_object* v___x_3196_; lean_object* v_uninterpretedSymbols_3197_; lean_object* v_functionSymbols_3198_; lean_object* v_functionSymbolSet_3199_; lean_object* v_unusedRelevantHypotheses_3200_; lean_object* v_derivedEquations_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3230_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v_fst_3195_ = lean_ctor_get(v_a_3194_, 0);
lean_inc(v_fst_3195_);
v___x_3196_ = lean_st_ref_take(v___y_3176_);
v_uninterpretedSymbols_3197_ = lean_ctor_get(v___x_3196_, 0);
v_functionSymbols_3198_ = lean_ctor_get(v___x_3196_, 1);
v_functionSymbolSet_3199_ = lean_ctor_get(v___x_3196_, 2);
v_unusedRelevantHypotheses_3200_ = lean_ctor_get(v___x_3196_, 3);
v_derivedEquations_3201_ = lean_ctor_get(v___x_3196_, 4);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3203_ = v___x_3196_;
v_isShared_3204_ = v_isSharedCheck_3230_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_derivedEquations_3201_);
lean_inc(v_unusedRelevantHypotheses_3200_);
lean_inc(v_functionSymbolSet_3199_);
lean_inc(v_functionSymbols_3198_);
lean_inc(v_uninterpretedSymbols_3197_);
lean_dec(v___x_3196_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3230_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3205_ = lean_array_push(v_derivedEquations_3201_, v_a_3194_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v___x_3205_);
v___x_3207_ = v___x_3203_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_uninterpretedSymbols_3197_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_functionSymbols_3198_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_functionSymbolSet_3199_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_unusedRelevantHypotheses_3200_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_st_ref_put(v___y_3176_, v___x_3207_);
if (lean_obj_tag(v_fst_3195_) == 1)
{
lean_object* v_fvarId_3209_; lean_object* v___x_3210_; 
v_fvarId_3209_ = lean_ctor_get(v_fst_3195_, 0);
lean_inc(v_fvarId_3209_);
lean_dec_ref_known(v_fst_3195_, 1);
v___x_3210_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvarId_3209_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v_fvarId_3209_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_dec_ref_known(v___x_3210_, 1);
v_a_3183_ = v___x_3192_;
goto v___jp_3182_;
}
else
{
return v___x_3210_;
}
}
else
{
lean_object* v___x_3211_; lean_object* v_functionSymbolSet_3212_; uint8_t v___x_3213_; 
v___x_3211_ = lean_st_ref_get(v___y_3176_);
v_functionSymbolSet_3212_ = lean_ctor_get(v___x_3211_, 2);
lean_inc_ref(v_functionSymbolSet_3212_);
lean_dec(v___x_3211_);
v___x_3213_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_functionSymbolSet_3212_, v_fst_3195_);
lean_dec_ref(v_functionSymbolSet_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v_uninterpretedSymbols_3215_; lean_object* v_functionSymbols_3216_; lean_object* v_functionSymbolSet_3217_; lean_object* v_unusedRelevantHypotheses_3218_; lean_object* v_derivedEquations_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3228_; 
v___x_3214_ = lean_st_ref_take(v___y_3176_);
v_uninterpretedSymbols_3215_ = lean_ctor_get(v___x_3214_, 0);
v_functionSymbols_3216_ = lean_ctor_get(v___x_3214_, 1);
v_functionSymbolSet_3217_ = lean_ctor_get(v___x_3214_, 2);
v_unusedRelevantHypotheses_3218_ = lean_ctor_get(v___x_3214_, 3);
v_derivedEquations_3219_ = lean_ctor_get(v___x_3214_, 4);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3221_ = v___x_3214_;
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_derivedEquations_3219_);
lean_inc(v_unusedRelevantHypotheses_3218_);
lean_inc(v_functionSymbolSet_3217_);
lean_inc(v_functionSymbols_3216_);
lean_inc(v_uninterpretedSymbols_3215_);
lean_dec(v___x_3214_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_uninterpretedSymbols_3215_, v_fst_3195_, v___x_3192_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3223_);
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_functionSymbols_3216_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_functionSymbolSet_3217_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_unusedRelevantHypotheses_3218_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_derivedEquations_3219_);
v___x_3225_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_st_ref_put(v___y_3176_, v___x_3225_);
v_a_3183_ = v___x_3192_;
goto v___jp_3182_;
}
}
}
else
{
lean_dec(v_fst_3195_);
v_a_3183_ = v___x_3192_;
goto v___jp_3182_;
}
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v_a_3231_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3193_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3193_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
v___jp_3182_:
{
size_t v___x_3184_; size_t v___x_3185_; 
v___x_3184_ = ((size_t)1ULL);
v___x_3185_ = lean_usize_add(v_i_3173_, v___x_3184_);
v_i_3173_ = v___x_3185_;
v_b_3174_ = v_a_3183_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3171_ = stack[0].m_obj;
size_t v_sz_3172_ = stack[1].m_num;
size_t v_i_3173_ = stack[2].m_num;
lean_object* v_b_3174_ = stack[3].m_obj;
lean_object* v___y_3175_ = stack[4].m_obj;
lean_object* v___y_3176_ = stack[5].m_obj;
lean_object* v___y_3177_ = stack[6].m_obj;
lean_object* v___y_3178_ = stack[7].m_obj;
lean_object* v___y_3179_ = stack[8].m_obj;
lean_object* v___y_3180_ = stack[9].m_obj;
lean_object* v_res_3239_;
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_as_3171_, v_sz_3172_, v_i_3173_, v_b_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
stack->m_obj
 = v_res_3239_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3___boxed(lean_object* v_as_3240_, lean_object* v_sz_3241_, lean_object* v_i_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
size_t v_sz_boxed_3251_; size_t v_i_boxed_3252_; lean_object* v_res_3253_; 
v_sz_boxed_3251_ = lean_unbox_usize(v_sz_3241_);
lean_dec(v_sz_3241_);
v_i_boxed_3252_ = lean_unbox_usize(v_i_3242_);
lean_dec(v_i_3242_);
v_res_3253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_as_3240_, v_sz_boxed_3251_, v_i_boxed_3252_, v_b_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v_as_3240_);
return v_res_3253_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(lean_object* v_as_3254_, size_t v_sz_3255_, size_t v_i_3256_, lean_object* v_b_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3256_, v_sz_3255_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_b_3257_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v_uninterpretedSymbols_3265_; lean_object* v_functionSymbols_3266_; lean_object* v_functionSymbolSet_3267_; lean_object* v_unusedRelevantHypotheses_3268_; lean_object* v_derivedEquations_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3282_; 
v___x_3262_ = lean_box(0);
v_a_3263_ = lean_array_uget_borrowed(v_as_3254_, v_i_3256_);
v___x_3264_ = lean_st_ref_take(v___y_3258_);
v_uninterpretedSymbols_3265_ = lean_ctor_get(v___x_3264_, 0);
v_functionSymbols_3266_ = lean_ctor_get(v___x_3264_, 1);
v_functionSymbolSet_3267_ = lean_ctor_get(v___x_3264_, 2);
v_unusedRelevantHypotheses_3268_ = lean_ctor_get(v___x_3264_, 3);
v_derivedEquations_3269_ = lean_ctor_get(v___x_3264_, 4);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3271_ = v___x_3264_;
v_isShared_3272_ = v_isSharedCheck_3282_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_derivedEquations_3269_);
lean_inc(v_unusedRelevantHypotheses_3268_);
lean_inc(v_functionSymbolSet_3267_);
lean_inc(v_functionSymbols_3266_);
lean_inc(v_uninterpretedSymbols_3265_);
lean_dec(v___x_3264_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3282_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_inc_n(v_a_3263_, 2);
v___x_3273_ = lean_array_push(v_functionSymbols_3266_, v_a_3263_);
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_functionSymbolSet_3267_, v_a_3263_, v___x_3262_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 2, v___x_3274_);
lean_ctor_set(v___x_3271_, 1, v___x_3273_);
v___x_3276_ = v___x_3271_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_uninterpretedSymbols_3265_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_unusedRelevantHypotheses_3268_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_derivedEquations_3269_);
v___x_3276_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; 
v___x_3277_ = lean_st_ref_put(v___y_3258_, v___x_3276_);
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_add(v_i_3256_, v___x_3278_);
v_i_3256_ = v___x_3279_;
v_b_3257_ = v___x_3262_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3254_ = stack[0].m_obj;
size_t v_sz_3255_ = stack[1].m_num;
size_t v_i_3256_ = stack[2].m_num;
lean_object* v_b_3257_ = stack[3].m_obj;
lean_object* v___y_3258_ = stack[4].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3254_, v_sz_3255_, v_i_3256_, v_b_3257_, v___y_3258_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg___boxed(lean_object* v_as_3284_, lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
size_t v_sz_boxed_3290_; size_t v_i_boxed_3291_; lean_object* v_res_3292_; 
v_sz_boxed_3290_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3291_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3284_, v_sz_boxed_3290_, v_i_boxed_3291_, v_b_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v_as_3284_);
return v_res_3292_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_equations_3300_; lean_object* v_functionAtoms_3301_; lean_object* v___x_3302_; size_t v_sz_3303_; size_t v___x_3304_; lean_object* v___x_3305_; 
v_equations_3300_ = lean_ctor_get(v_a_3293_, 2);
v_functionAtoms_3301_ = lean_ctor_get(v_a_3293_, 3);
v___x_3302_ = lean_box(0);
v_sz_3303_ = lean_array_size(v_functionAtoms_3301_);
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_functionAtoms_3301_, v_sz_3303_, v___x_3304_, v___x_3302_, v_a_3294_);
if (lean_obj_tag(v___x_3305_) == 0)
{
size_t v_sz_3306_; lean_object* v___x_3307_; 
lean_dec_ref_known(v___x_3305_, 1);
v_sz_3306_ = lean_array_size(v_equations_3300_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_equations_3300_, v_sz_3306_, v___x_3304_, v___x_3302_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; 
v_unused_3315_ = lean_ctor_get(v___x_3307_, 0);
lean_dec(v_unused_3315_);
v___x_3309_ = v___x_3307_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v___x_3307_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3302_);
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3302_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
return v___x_3307_;
}
}
else
{
return v___x_3305_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3293_ = stack[0].m_obj;
lean_object* v_a_3294_ = stack[1].m_obj;
lean_object* v_a_3295_ = stack[2].m_obj;
lean_object* v_a_3296_ = stack[3].m_obj;
lean_object* v_a_3297_ = stack[4].m_obj;
lean_object* v_a_3298_ = stack[5].m_obj;
lean_object* v_res_3316_;
v_res_3316_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
stack->m_obj
 = v_res_3316_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
return v_res_3324_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object* v_00_u03b2_3325_, lean_object* v_m_3326_, lean_object* v_a_3327_){
_start:
{
uint8_t v___x_3328_; 
v___x_3328_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3326_, v_a_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3326_ = stack[1].m_obj;
lean_object* v_a_3327_ = stack[2].m_obj;
uint8_t v_res_3329_;
v_res_3329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_box(0), v_m_3326_, v_a_3327_);
stack->m_num = v_res_3329_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___boxed(lean_object* v_00_u03b2_3330_, lean_object* v_m_3331_, lean_object* v_a_3332_){
_start:
{
uint8_t v_res_3333_; lean_object* v_r_3334_; 
v_res_3333_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(v_00_u03b2_3330_, v_m_3331_, v_a_3332_);
lean_dec_ref(v_a_3332_);
lean_dec_ref(v_m_3331_);
v_r_3334_ = lean_box(v_res_3333_);
return v_r_3334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object* v_00_u03b2_3335_, lean_object* v_m_3336_, lean_object* v_a_3337_, lean_object* v_b_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_m_3336_, v_a_3337_, v_b_3338_);
return v___x_3339_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(lean_object* v_as_3340_, size_t v_sz_3341_, size_t v_i_3342_, lean_object* v_b_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3340_, v_sz_3341_, v_i_3342_, v_b_3343_, v___y_3345_);
return v___x_3351_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3340_ = stack[0].m_obj;
size_t v_sz_3341_ = stack[1].m_num;
size_t v_i_3342_ = stack[2].m_num;
lean_object* v_b_3343_ = stack[3].m_obj;
lean_object* v___y_3344_ = stack[4].m_obj;
lean_object* v___y_3345_ = stack[5].m_obj;
lean_object* v___y_3346_ = stack[6].m_obj;
lean_object* v___y_3347_ = stack[7].m_obj;
lean_object* v___y_3348_ = stack[8].m_obj;
lean_object* v___y_3349_ = stack[9].m_obj;
lean_object* v_res_3352_;
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(v_as_3340_, v_sz_3341_, v_i_3342_, v_b_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
stack->m_obj
 = v_res_3352_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___boxed(lean_object* v_as_3353_, lean_object* v_sz_3354_, lean_object* v_i_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
size_t v_sz_boxed_3364_; size_t v_i_boxed_3365_; lean_object* v_res_3366_; 
v_sz_boxed_3364_ = lean_unbox_usize(v_sz_3354_);
lean_dec(v_sz_3354_);
v_i_boxed_3365_ = lean_unbox_usize(v_i_3355_);
lean_dec(v_i_3355_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(v_as_3353_, v_sz_boxed_3364_, v_i_boxed_3365_, v_b_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec_ref(v_as_3353_);
return v_res_3366_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object* v_00_u03b2_3367_, lean_object* v_a_3368_, lean_object* v_x_3369_){
_start:
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3368_, v_x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3368_ = stack[1].m_obj;
lean_object* v_x_3369_ = stack[2].m_obj;
uint8_t v_res_3371_;
v_res_3371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_box(0), v_a_3368_, v_x_3369_);
stack->m_num = v_res_3371_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3372_, lean_object* v_a_3373_, lean_object* v_x_3374_){
_start:
{
uint8_t v_res_3375_; lean_object* v_r_3376_; 
v_res_3375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_3372_, v_a_3373_, v_x_3374_);
lean_dec(v_x_3374_);
lean_dec_ref(v_a_3373_);
v_r_3376_ = lean_box(v_res_3375_);
return v_r_3376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(lean_object* v_00_u03b2_3377_, lean_object* v_data_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_data_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3380_, lean_object* v_i_3381_, lean_object* v_source_3382_, lean_object* v_target_3383_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v_i_3381_, v_source_3382_, v_target_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3385_, lean_object* v_x_3386_, lean_object* v_x_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3386_, v_x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__0));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(lean_object* v_as_x27_3392_, lean_object* v_b_3393_){
_start:
{
if (lean_obj_tag(v_as_x27_3392_) == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_b_3393_);
return v___x_3394_;
}
else
{
lean_object* v_head_3395_; lean_object* v_tail_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_head_3395_ = lean_ctor_get(v_as_x27_3392_, 0);
v_tail_3396_ = lean_ctor_get(v_as_x27_3392_, 1);
v___x_3397_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1);
lean_inc(v_head_3395_);
v___x_3398_ = l_Lean_MessageData_ofExpr(v_head_3395_);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_b_3393_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v_as_x27_3392_ = v_tail_3396_;
v_b_3393_ = v___x_3400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3402_, lean_object* v_b_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v_as_x27_3402_, v_b_3403_);
lean_dec(v_as_x27_3402_);
return v_res_3404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__0));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer(lean_object* v_d_3408_){
_start:
{
lean_object* v_functionSymbols_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_functionSymbols_3409_ = lean_ctor_get(v_d_3408_, 1);
lean_inc_ref(v_functionSymbols_3409_);
lean_dec_ref(v_d_3408_);
v___x_3410_ = lean_array_get_size(v_functionSymbols_3409_);
v___x_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = lean_nat_dec_eq(v___x_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_array_to_list(v_functionSymbols_3409_);
v___x_3414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1);
v___x_3415_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v___x_3413_, v___x_3414_);
lean_dec(v___x_3413_);
return v___x_3415_;
}
else
{
lean_object* v___x_3416_; 
lean_dec_ref(v_functionSymbols_3409_);
v___x_3416_ = lean_box(0);
return v___x_3416_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(lean_object* v_as_3417_, lean_object* v_as_x27_3418_, lean_object* v_b_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v_as_x27_3418_, v_b_3419_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___boxed(lean_object* v_as_3422_, lean_object* v_as_x27_3423_, lean_object* v_b_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(v_as_3422_, v_as_x27_3423_, v_b_3424_, v_a_3425_);
lean_dec(v_as_x27_3423_);
lean_dec(v_as_3422_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object* v_x_3432_, lean_object* v_x_3433_){
_start:
{
if (lean_obj_tag(v_x_3433_) == 0)
{
lean_inc(v_x_3432_);
return v_x_3432_;
}
else
{
lean_object* v_key_3434_; lean_object* v_tail_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_key_3434_ = lean_ctor_get(v_x_3433_, 0);
v_tail_3435_ = lean_ctor_get(v_x_3433_, 2);
v___x_3436_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_x_3432_, v_tail_3435_);
lean_inc(v_key_3434_);
v___x_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_key_3434_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
return v___x_3437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object* v_x_3438_, lean_object* v_x_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_x_3438_, v_x_3439_);
lean_dec(v_x_3439_);
lean_dec(v_x_3438_);
return v_res_3440_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object* v_as_3441_, size_t v_i_3442_, size_t v_stop_3443_, lean_object* v_b_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_eq(v_i_3442_, v_stop_3443_);
if (v___x_3445_ == 0)
{
size_t v___x_3446_; size_t v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_sub(v_i_3442_, v___x_3446_);
v___x_3448_ = lean_array_uget_borrowed(v_as_3441_, v___x_3447_);
v___x_3449_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_b_3444_, v___x_3448_);
lean_dec(v_b_3444_);
v_i_3442_ = v___x_3447_;
v_b_3444_ = v___x_3449_;
goto _start;
}
else
{
return v_b_3444_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3441_ = stack[0].m_obj;
size_t v_i_3442_ = stack[1].m_num;
size_t v_stop_3443_ = stack[2].m_num;
lean_object* v_b_3444_ = stack[3].m_obj;
lean_object* v_res_3451_;
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_as_3441_, v_i_3442_, v_stop_3443_, v_b_3444_);
stack->m_obj
 = v_res_3451_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object* v_as_3452_, lean_object* v_i_3453_, lean_object* v_stop_3454_, lean_object* v_b_3455_){
_start:
{
size_t v_i_boxed_3456_; size_t v_stop_boxed_3457_; lean_object* v_res_3458_; 
v_i_boxed_3456_ = lean_unbox_usize(v_i_3453_);
lean_dec(v_i_3453_);
v_stop_boxed_3457_ = lean_unbox_usize(v_stop_3454_);
lean_dec(v_stop_3454_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_as_3452_, v_i_boxed_3456_, v_stop_boxed_3457_, v_b_3455_);
lean_dec_ref(v_as_3452_);
return v_res_3458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0));
v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object* v_d_3462_){
_start:
{
lean_object* v___y_3464_; lean_object* v_uninterpretedSymbols_3467_; lean_object* v_size_3468_; lean_object* v_buckets_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v_uninterpretedSymbols_3467_ = lean_ctor_get(v_d_3462_, 0);
v_size_3468_ = lean_ctor_get(v_uninterpretedSymbols_3467_, 0);
v_buckets_3469_ = lean_ctor_get(v_uninterpretedSymbols_3467_, 1);
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = lean_nat_dec_eq(v_size_3468_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_array_get_size(v_buckets_3469_);
v___x_3474_ = lean_nat_dec_lt(v___x_3470_, v___x_3473_);
if (v___x_3474_ == 0)
{
v___y_3464_ = v___x_3472_;
goto v___jp_3463_;
}
else
{
size_t v___x_3475_; size_t v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = lean_usize_of_nat(v___x_3473_);
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_buckets_3469_, v___x_3475_, v___x_3476_, v___x_3472_);
v___y_3464_ = v___x_3477_;
goto v___jp_3463_;
}
}
else
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_box(0);
return v___x_3478_;
}
v___jp_3463_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
v___x_3466_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v___y_3464_, v___x_3465_);
lean_dec(v___y_3464_);
return v___x_3466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object* v_d_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_3479_);
lean_dec_ref(v_d_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object* v_x_3481_, lean_object* v_x_3482_){
_start:
{
if (lean_obj_tag(v_x_3482_) == 0)
{
lean_inc(v_x_3481_);
return v_x_3481_;
}
else
{
lean_object* v_key_3483_; lean_object* v_tail_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_key_3483_ = lean_ctor_get(v_x_3482_, 0);
v_tail_3484_ = lean_ctor_get(v_x_3482_, 2);
v___x_3485_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3481_, v_tail_3484_);
lean_inc(v_key_3483_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_key_3483_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3487_, v_x_3488_);
lean_dec(v_x_3488_);
lean_dec(v_x_3487_);
return v_res_3489_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object* v_as_3490_, size_t v_i_3491_, size_t v_stop_3492_, lean_object* v_b_3493_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_eq(v_i_3491_, v_stop_3492_);
if (v___x_3494_ == 0)
{
size_t v___x_3495_; size_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3495_ = ((size_t)1ULL);
v___x_3496_ = lean_usize_sub(v_i_3491_, v___x_3495_);
v___x_3497_ = lean_array_uget_borrowed(v_as_3490_, v___x_3496_);
v___x_3498_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_b_3493_, v___x_3497_);
lean_dec(v_b_3493_);
v_i_3491_ = v___x_3496_;
v_b_3493_ = v___x_3498_;
goto _start;
}
else
{
return v_b_3493_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3490_ = stack[0].m_obj;
size_t v_i_3491_ = stack[1].m_num;
size_t v_stop_3492_ = stack[2].m_num;
lean_object* v_b_3493_ = stack[3].m_obj;
lean_object* v_res_3500_;
v_res_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_3490_, v_i_3491_, v_stop_3492_, v_b_3493_);
stack->m_obj
 = v_res_3500_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object* v_as_3501_, lean_object* v_i_3502_, lean_object* v_stop_3503_, lean_object* v_b_3504_){
_start:
{
size_t v_i_boxed_3505_; size_t v_stop_boxed_3506_; lean_object* v_res_3507_; 
v_i_boxed_3505_ = lean_unbox_usize(v_i_3502_);
lean_dec(v_i_3502_);
v_stop_boxed_3506_ = lean_unbox_usize(v_stop_3503_);
lean_dec(v_stop_3503_);
v_res_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_3501_, v_i_boxed_3505_, v_stop_boxed_3506_, v_b_3504_);
lean_dec_ref(v_as_3501_);
return v_res_3507_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0));
v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(lean_object* v_as_x27_3511_, lean_object* v_b_3512_){
_start:
{
if (lean_obj_tag(v_as_x27_3511_) == 0)
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_b_3512_);
return v___x_3513_;
}
else
{
lean_object* v_head_3514_; lean_object* v_tail_3515_; lean_object* v_type_3516_; lean_object* v_source_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_head_3514_ = lean_ctor_get(v_as_x27_3511_, 0);
v_tail_3515_ = lean_ctor_get(v_as_x27_3511_, 1);
v_type_3516_ = lean_ctor_get(v_head_3514_, 1);
v_source_3517_ = lean_ctor_get(v_head_3514_, 3);
v___x_3518_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1);
lean_inc_ref(v_type_3516_);
v___x_3519_ = l_Lean_MessageData_ofExpr(v_type_3516_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
lean_inc(v_source_3517_);
v___x_3523_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v_source_3517_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_b_3512_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v_as_x27_3511_ = v_tail_3515_;
v_b_3512_ = v___x_3525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3527_, lean_object* v_b_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3527_, v_b_3528_);
lean_dec(v_as_x27_3527_);
return v_res_3529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0));
v___x_3532_ = l_Lean_stringToMessageData(v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object* v_d_3533_){
_start:
{
lean_object* v___y_3535_; lean_object* v_unusedRelevantHypotheses_3538_; lean_object* v_size_3539_; lean_object* v_buckets_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_unusedRelevantHypotheses_3538_ = lean_ctor_get(v_d_3533_, 3);
v_size_3539_ = lean_ctor_get(v_unusedRelevantHypotheses_3538_, 0);
v_buckets_3540_ = lean_ctor_get(v_unusedRelevantHypotheses_3538_, 1);
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = lean_nat_dec_eq(v_size_3539_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_array_get_size(v_buckets_3540_);
v___x_3545_ = lean_nat_dec_lt(v___x_3541_, v___x_3544_);
if (v___x_3545_ == 0)
{
v___y_3535_ = v___x_3543_;
goto v___jp_3534_;
}
else
{
size_t v___x_3546_; size_t v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_usize_of_nat(v___x_3544_);
v___x_3547_ = ((size_t)0ULL);
v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_buckets_3540_, v___x_3546_, v___x_3547_, v___x_3543_);
v___y_3535_ = v___x_3548_;
goto v___jp_3534_;
}
}
else
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_box(0);
return v___x_3549_;
}
v___jp_3534_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
v___x_3537_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v___y_3535_, v___x_3536_);
lean_dec(v___y_3535_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object* v_d_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_3550_);
lean_dec_ref(v_d_3550_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object* v_as_3552_, lean_object* v_as_x27_3553_, lean_object* v_b_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3553_, v_b_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object* v_as_3557_, lean_object* v_as_x27_3558_, lean_object* v_b_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_as_3557_, v_as_x27_3558_, v_b_3559_, v_a_3560_);
lean_dec(v_as_x27_3558_);
lean_dec(v_as_3557_);
return v_res_3561_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0));
v___x_3573_ = l_Lean_stringToMessageData(v___x_3572_);
return v___x_3573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2));
v___x_3576_ = l_Lean_stringToMessageData(v___x_3575_);
return v___x_3576_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object* v_as_3577_, size_t v_i_3578_, size_t v_stop_3579_, lean_object* v_b_3580_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_usize_dec_eq(v_i_3578_, v_stop_3579_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; size_t v___x_3588_; size_t v___x_3589_; 
v___x_3582_ = lean_array_uget_borrowed(v_as_3577_, v_i_3578_);
v___x_3583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v_b_3580_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
lean_inc(v___x_3582_);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v___x_3582_);
v___x_3586_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = ((size_t)1ULL);
v___x_3589_ = lean_usize_add(v_i_3578_, v___x_3588_);
v_i_3578_ = v___x_3589_;
v_b_3580_ = v___x_3587_;
goto _start;
}
else
{
return v_b_3580_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3577_ = stack[0].m_obj;
size_t v_i_3578_ = stack[1].m_num;
size_t v_stop_3579_ = stack[2].m_num;
lean_object* v_b_3580_ = stack[3].m_obj;
lean_object* v_res_3591_;
v_res_3591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_3577_, v_i_3578_, v_stop_3579_, v_b_3580_);
stack->m_obj
 = v_res_3591_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object* v_as_3592_, lean_object* v_i_3593_, lean_object* v_stop_3594_, lean_object* v_b_3595_){
_start:
{
size_t v_i_boxed_3596_; size_t v_stop_boxed_3597_; lean_object* v_res_3598_; 
v_i_boxed_3596_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_stop_boxed_3597_ = lean_unbox_usize(v_stop_3594_);
lean_dec(v_stop_3594_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_3592_, v_i_boxed_3596_, v_stop_boxed_3597_, v_b_3595_);
lean_dec_ref(v_as_3592_);
return v_res_3598_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0));
v___x_3601_ = l_Lean_stringToMessageData(v___x_3600_);
return v___x_3601_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object* v_as_3602_, size_t v_i_3603_, size_t v_stop_3604_, lean_object* v_b_3605_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_usize_dec_eq(v_i_3603_, v_stop_3604_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v_fst_3608_; lean_object* v_snd_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3626_; 
v___x_3607_ = lean_array_uget(v_as_3602_, v_i_3603_);
v_fst_3608_ = lean_ctor_get(v___x_3607_, 0);
v_snd_3609_ = lean_ctor_get(v___x_3607_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3611_ = v___x_3607_;
v_isShared_3612_ = v_isSharedCheck_3626_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_snd_3609_);
lean_inc(v_fst_3608_);
lean_dec(v___x_3607_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3626_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3616_; 
v___x_3613_ = l_Lean_MessageData_ofExpr(v_fst_3608_);
v___x_3614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 7);
lean_ctor_set(v___x_3611_, 1, v___x_3614_);
lean_ctor_set(v___x_3611_, 0, v___x_3613_);
v___x_3616_ = v___x_3611_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; size_t v___x_3622_; size_t v___x_3623_; 
v___x_3617_ = l_Lean_MessageData_ofExpr(v_snd_3609_);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3621_, 0, v_b_3605_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = ((size_t)1ULL);
v___x_3623_ = lean_usize_add(v_i_3603_, v___x_3622_);
v_i_3603_ = v___x_3623_;
v_b_3605_ = v___x_3621_;
goto _start;
}
}
}
else
{
return v_b_3605_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3602_ = stack[0].m_obj;
size_t v_i_3603_ = stack[1].m_num;
size_t v_stop_3604_ = stack[2].m_num;
lean_object* v_b_3605_ = stack[3].m_obj;
lean_object* v_res_3627_;
v_res_3627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_3602_, v_i_3603_, v_stop_3604_, v_b_3605_);
stack->m_obj
 = v_res_3627_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object* v_as_3628_, lean_object* v_i_3629_, lean_object* v_stop_3630_, lean_object* v_b_3631_){
_start:
{
size_t v_i_boxed_3632_; size_t v_stop_boxed_3633_; lean_object* v_res_3634_; 
v_i_boxed_3632_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_stop_boxed_3633_ = lean_unbox_usize(v_stop_3630_);
lean_dec(v_stop_3630_);
v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_3628_, v_i_boxed_3632_, v_stop_boxed_3633_, v_b_3631_);
lean_dec_ref(v_as_3628_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object* v_a_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_){
_start:
{
if (lean_obj_tag(v_x_3637_) == 0)
{
lean_dec_ref(v_a_3635_);
return v_x_3636_;
}
else
{
lean_object* v_head_3638_; lean_object* v_tail_3639_; lean_object* v___x_3640_; 
v_head_3638_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_head_3638_);
v_tail_3639_ = lean_ctor_get(v_x_3637_, 1);
lean_inc(v_tail_3639_);
lean_dec_ref_known(v_x_3637_, 2);
lean_inc_ref(v_a_3635_);
v___x_3640_ = lean_apply_1(v_head_3638_, v_a_3635_);
if (lean_obj_tag(v___x_3640_) == 1)
{
lean_object* v_val_3641_; lean_object* v___x_3642_; 
v_val_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v___x_3640_, 1);
v___x_3642_ = lean_array_push(v_x_3636_, v_val_3641_);
v_x_3636_ = v___x_3642_;
v_x_3637_ = v_tail_3639_;
goto _start;
}
else
{
lean_dec(v___x_3640_);
v_x_3637_ = v_tail_3639_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0));
v___x_3647_ = l_Lean_stringToMessageData(v___x_3646_);
return v___x_3647_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7));
v___x_3658_ = l_Lean_stringToMessageData(v___x_3657_);
return v___x_3658_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object* v_counterExample_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed), 7, 0);
v___x_3666_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_3665_, v_counterExample_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3738_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3738_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3738_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_err_3672_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v_err_3710_; lean_object* v___y_3726_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3702_ = lean_unsigned_to_nat(0u);
v___x_3703_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2));
v___x_3704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers));
lean_inc_n(v_a_3667_, 2);
v___x_3705_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3667_, v___x_3703_, v___x_3704_);
v___x_3706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers));
v___x_3707_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3667_, v___x_3703_, v___x_3706_);
v___x_3708_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4);
v___x_3728_ = lean_array_get_size(v___x_3705_);
v___x_3729_ = lean_nat_dec_eq(v___x_3728_, v___x_3702_);
if (v___x_3729_ == 0)
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_nat_dec_lt(v___x_3702_, v___x_3728_);
if (v___x_3730_ == 0)
{
lean_dec_ref(v___x_3705_);
v___y_3726_ = v___x_3708_;
goto v___jp_3725_;
}
else
{
uint8_t v___x_3731_; 
v___x_3731_ = lean_nat_dec_le(v___x_3728_, v___x_3728_);
if (v___x_3731_ == 0)
{
if (v___x_3730_ == 0)
{
lean_dec_ref(v___x_3705_);
v___y_3726_ = v___x_3708_;
goto v___jp_3725_;
}
else
{
size_t v___x_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = lean_usize_of_nat(v___x_3728_);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3705_, v___x_3732_, v___x_3733_, v___x_3708_);
lean_dec_ref(v___x_3705_);
v___y_3726_ = v___x_3734_;
goto v___jp_3725_;
}
}
else
{
size_t v___x_3735_; size_t v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = ((size_t)0ULL);
v___x_3736_ = lean_usize_of_nat(v___x_3728_);
v___x_3737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3705_, v___x_3735_, v___x_3736_, v___x_3708_);
lean_dec_ref(v___x_3705_);
v___y_3726_ = v___x_3737_;
goto v___jp_3725_;
}
}
}
else
{
lean_dec_ref(v___x_3705_);
v_err_3710_ = v___x_3708_;
goto v___jp_3709_;
}
v___jp_3671_:
{
lean_object* v_derivedEquations_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_derivedEquations_3673_ = lean_ctor_get(v_a_3667_, 4);
lean_inc_ref(v_derivedEquations_3673_);
lean_dec(v_a_3667_);
v___x_3674_ = lean_unsigned_to_nat(0u);
v___x_3675_ = lean_array_get_size(v_derivedEquations_3673_);
v___x_3676_ = lean_nat_dec_lt(v___x_3674_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3678_; 
lean_dec_ref(v_derivedEquations_3673_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_err_3672_);
v___x_3678_ = v___x_3669_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_err_3672_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
else
{
uint8_t v___x_3680_; 
v___x_3680_ = lean_nat_dec_le(v___x_3675_, v___x_3675_);
if (v___x_3680_ == 0)
{
if (v___x_3676_ == 0)
{
lean_object* v___x_3682_; 
lean_dec_ref(v_derivedEquations_3673_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_err_3672_);
v___x_3682_ = v___x_3669_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_err_3672_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
else
{
size_t v___x_3684_; size_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3684_ = ((size_t)0ULL);
v___x_3685_ = lean_usize_of_nat(v___x_3675_);
v___x_3686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3673_, v___x_3684_, v___x_3685_, v_err_3672_);
lean_dec_ref(v_derivedEquations_3673_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3686_);
v___x_3688_ = v___x_3669_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
else
{
size_t v___x_3690_; size_t v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3690_ = ((size_t)0ULL);
v___x_3691_ = lean_usize_of_nat(v___x_3675_);
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3673_, v___x_3690_, v___x_3691_, v_err_3672_);
lean_dec_ref(v_derivedEquations_3673_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3692_);
v___x_3694_ = v___x_3669_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
v___jp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___y_3697_);
lean_ctor_set(v___x_3699_, 1, v___y_3698_);
v___x_3700_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v_err_3672_ = v___x_3701_;
goto v___jp_3671_;
}
v___jp_3709_:
{
lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = lean_array_get_size(v___x_3707_);
v___x_3712_ = lean_nat_dec_eq(v___x_3711_, v___x_3702_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3713_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_err_3710_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_nat_dec_lt(v___x_3702_, v___x_3711_);
if (v___x_3715_ == 0)
{
lean_dec_ref(v___x_3707_);
v___y_3697_ = v___x_3714_;
v___y_3698_ = v___x_3708_;
goto v___jp_3696_;
}
else
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_nat_dec_le(v___x_3711_, v___x_3711_);
if (v___x_3716_ == 0)
{
if (v___x_3715_ == 0)
{
lean_dec_ref(v___x_3707_);
v___y_3697_ = v___x_3714_;
v___y_3698_ = v___x_3708_;
goto v___jp_3696_;
}
else
{
size_t v___x_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = ((size_t)0ULL);
v___x_3718_ = lean_usize_of_nat(v___x_3711_);
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3707_, v___x_3717_, v___x_3718_, v___x_3708_);
lean_dec_ref(v___x_3707_);
v___y_3697_ = v___x_3714_;
v___y_3698_ = v___x_3719_;
goto v___jp_3696_;
}
}
else
{
size_t v___x_3720_; size_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = lean_usize_of_nat(v___x_3711_);
v___x_3722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3707_, v___x_3720_, v___x_3721_, v___x_3708_);
lean_dec_ref(v___x_3707_);
v___y_3697_ = v___x_3714_;
v___y_3698_ = v___x_3722_;
goto v___jp_3696_;
}
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref(v___x_3707_);
v___x_3723_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_err_3710_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v_err_3672_ = v___x_3724_;
goto v___jp_3671_;
}
}
v___jp_3725_:
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3708_);
lean_ctor_set(v___x_3727_, 1, v___y_3726_);
v_err_3710_ = v___x_3727_;
goto v___jp_3709_;
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3666_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3666_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_0interp(lean_interpreter_value* stack)
{
lean_object* v_counterExample_3659_ = stack[0].m_obj;
lean_object* v_a_3660_ = stack[1].m_obj;
lean_object* v_a_3661_ = stack[2].m_obj;
lean_object* v_a_3662_ = stack[3].m_obj;
lean_object* v_a_3663_ = stack[4].m_obj;
lean_object* v_res_3747_;
v_res_3747_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
stack->m_obj
 = v_res_3747_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object* v_counterExample_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
return v_res_3754_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_Basic(uint8_t builtin);
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
res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
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
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin);
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
res = initialize_Std_Sat_AIG_Basic(builtin);
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

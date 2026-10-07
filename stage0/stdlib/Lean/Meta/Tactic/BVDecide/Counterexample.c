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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(lean_object* v_a_25_, lean_object* v_x_26_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg___boxed(lean_object* v_a_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(lean_object* v_m_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_buckets_38_; lean_object* v___x_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v_fold_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; size_t v___x_47_; size_t v___x_48_; size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_buckets_38_ = lean_ctor_get(v_m_36_, 1);
v___x_39_ = lean_array_get_size(v_buckets_38_);
v___x_40_ = lean_uint64_of_nat(v_a_37_);
v___x_41_ = 32ULL;
v___x_42_ = lean_uint64_shift_right(v___x_40_, v___x_41_);
v_fold_43_ = lean_uint64_xor(v___x_40_, v___x_42_);
v___x_44_ = 16ULL;
v___x_45_ = lean_uint64_shift_right(v_fold_43_, v___x_44_);
v___x_46_ = lean_uint64_xor(v_fold_43_, v___x_45_);
v___x_47_ = lean_uint64_to_usize(v___x_46_);
v___x_48_ = lean_usize_of_nat(v___x_39_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_sub(v___x_48_, v___x_49_);
v___x_51_ = lean_usize_land(v___x_47_, v___x_50_);
v___x_52_ = lean_array_uget_borrowed(v_buckets_38_, v___x_51_);
v___x_53_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_37_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg___boxed(lean_object* v_m_54_, lean_object* v_a_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v_m_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_m_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(lean_object* v___x_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
if (lean_obj_tag(v_a_59_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_60_);
return v___x_61_;
}
else
{
lean_object* v_value_62_; lean_object* v_snd_63_; lean_object* v_key_64_; lean_object* v_tail_65_; lean_object* v_fst_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_89_; 
v_value_62_ = lean_ctor_get(v_a_59_, 1);
lean_inc(v_value_62_);
v_snd_63_ = lean_ctor_get(v_value_62_, 1);
lean_inc(v_snd_63_);
v_key_64_ = lean_ctor_get(v_a_59_, 0);
lean_inc(v_key_64_);
v_tail_65_ = lean_ctor_get(v_a_59_, 2);
lean_inc(v_tail_65_);
lean_dec_ref_known(v_a_59_, 3);
v_fst_66_ = lean_ctor_get(v_value_62_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_value_62_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_value_62_, 1);
lean_dec(v_unused_90_);
v___x_68_ = v_value_62_;
v_isShared_69_ = v_isSharedCheck_89_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_fst_66_);
lean_dec(v_value_62_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_89_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_fst_70_; lean_object* v_snd_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_88_; 
v_fst_70_ = lean_ctor_get(v_snd_63_, 0);
v_snd_71_ = lean_ctor_get(v_snd_63_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_snd_63_);
if (v_isSharedCheck_88_ == 0)
{
v___x_73_ = v_snd_63_;
v_isShared_74_ = v_isSharedCheck_88_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_snd_71_);
lean_inc(v_fst_70_);
lean_dec(v_snd_63_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_88_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v___x_58_, v_key_64_);
lean_dec(v_key_64_);
if (v___x_75_ == 0)
{
lean_object* v_value_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v_value_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = l_BitVec_ofNat(v_fst_66_, v_value_76_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_fst_66_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_78_);
lean_ctor_set(v___x_73_, 0, v_snd_71_);
v___x_80_ = v___x_73_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_snd_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_86_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___x_80_);
lean_ctor_set(v___x_68_, 0, v_fst_70_);
v___x_82_ = v___x_68_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_fst_70_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_85_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; 
v___x_83_ = lean_array_push(v_a_60_, v___x_82_);
v_a_59_ = v_tail_65_;
v_a_60_ = v___x_83_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_73_);
lean_dec(v_snd_71_);
lean_dec(v_fst_70_);
lean_del_object(v___x_68_);
lean_dec(v_fst_66_);
v_a_59_ = v_tail_65_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(lean_object* v___x_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v___x_91_, v_a_92_, v_a_93_);
lean_dec_ref(v___x_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(lean_object* v___x_95_, lean_object* v_as_96_, size_t v_sz_97_, size_t v_i_98_, lean_object* v_b_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_usize_dec_lt(v_i_98_, v_sz_97_);
if (v___x_100_ == 0)
{
return v_b_99_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_102_; 
v_a_101_ = lean_array_uget_borrowed(v_as_96_, v_i_98_);
lean_inc(v_a_101_);
v___x_102_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v___x_95_, v_a_101_, v_b_99_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
return v_a_103_;
}
else
{
lean_object* v_a_104_; size_t v___x_105_; size_t v___x_106_; 
v_a_104_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_102_, 1);
v___x_105_ = ((size_t)1ULL);
v___x_106_ = lean_usize_add(v_i_98_, v___x_105_);
v_i_98_ = v___x_106_;
v_b_99_ = v_a_104_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(lean_object* v___x_108_, lean_object* v_as_109_, lean_object* v_sz_110_, lean_object* v_i_111_, lean_object* v_b_112_){
_start:
{
size_t v_sz_boxed_113_; size_t v_i_boxed_114_; lean_object* v_res_115_; 
v_sz_boxed_113_ = lean_unbox_usize(v_sz_110_);
lean_dec(v_sz_110_);
v_i_boxed_114_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v___x_108_, v_as_109_, v_sz_boxed_113_, v_i_boxed_114_, v_b_112_);
lean_dec_ref(v_as_109_);
lean_dec_ref(v___x_108_);
return v_res_115_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_119_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__2));
v___x_120_ = lean_unsigned_to_nat(6u);
v___x_121_ = lean_unsigned_to_nat(61u);
v___x_122_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__1));
v___x_123_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0));
v___x_124_ = l_mkPanicMessageWithDecl(v___x_123_, v___x_122_, v___x_121_, v___x_120_, v___x_119_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(lean_object* v_init_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v_l_129_; lean_object* v_r_130_; lean_object* v___x_131_; 
v_k_127_ = lean_ctor_get(v_x_126_, 1);
v_v_128_ = lean_ctor_get(v_x_126_, 2);
v_l_129_ = lean_ctor_get(v_x_126_, 3);
v_r_130_ = lean_ctor_get(v_x_126_, 4);
v___x_131_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(v_init_125_, v_l_129_);
if (lean_obj_tag(v___x_131_) == 0)
{
return v___x_131_;
}
else
{
lean_object* v_a_132_; lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_155_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v_fst_133_ = lean_ctor_get(v_a_132_, 0);
v_snd_134_ = lean_ctor_get(v_a_132_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_a_132_);
if (v_isSharedCheck_155_ == 0)
{
v___x_136_ = v_a_132_;
v_isShared_137_ = v_isSharedCheck_155_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_snd_134_);
lean_inc(v_fst_133_);
lean_dec(v_a_132_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_155_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_value_139_; uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_eq(v_k_127_, v_snd_134_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_del_object(v___x_136_);
lean_dec(v_snd_134_);
lean_dec(v_fst_133_);
v___x_147_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__3);
v___x_148_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(v___x_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
return v___x_148_;
}
else
{
lean_object* v_a_149_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v_init_125_ = v_a_149_;
v_x_126_ = v_r_130_;
goto _start;
}
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v_v_128_);
if (v___x_151_ == 0)
{
v_value_139_ = v_fst_133_;
goto v___jp_138_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_shiftl(v___x_152_, v_snd_134_);
v___x_154_ = lean_nat_lor(v_fst_133_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v_fst_133_);
v_value_139_ = v___x_154_;
goto v___jp_138_;
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_snd_134_, v___x_140_);
lean_dec(v_snd_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_141_);
lean_ctor_set(v___x_136_, 0, v_value_139_);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_value_139_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
v_init_125_ = v___x_143_;
v_x_126_ = v_r_130_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_init_125_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___boxed(lean_object* v_init_157_, lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(v_init_157_, v_x_158_);
lean_dec(v_x_158_);
return v_res_159_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0(void){
_start:
{
uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = 0;
v___x_161_ = l_Lean_instInhabitedExpr;
v___x_162_ = lean_box(v___x_160_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10(lean_object* v_msg_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10___closed__0);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_panic_fn_borrowed(v___x_167_, v_msg_164_);
lean_dec_ref_known(v___x_167_, 2);
return v___x_168_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_172_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__2));
v___x_173_ = lean_unsigned_to_nat(11u);
v___x_174_ = lean_unsigned_to_nat(163u);
v___x_175_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__1));
v___x_176_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__0));
v___x_177_ = l_mkPanicMessageWithDecl(v___x_176_, v___x_175_, v___x_174_, v___x_173_, v___x_172_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___closed__3);
v___x_181_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8_spec__10(v___x_180_);
return v___x_181_;
}
else
{
lean_object* v_key_182_; lean_object* v_value_183_; lean_object* v_tail_184_; uint8_t v___x_185_; 
v_key_182_ = lean_ctor_get(v_x_179_, 0);
v_value_183_ = lean_ctor_get(v_x_179_, 1);
v_tail_184_ = lean_ctor_get(v_x_179_, 2);
v___x_185_ = lean_nat_dec_eq(v_key_182_, v_a_178_);
if (v___x_185_ == 0)
{
v_x_179_ = v_tail_184_;
goto _start;
}
else
{
lean_inc(v_value_183_);
return v_value_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8___boxed(lean_object* v_a_187_, lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(v_a_187_, v_x_188_);
lean_dec(v_x_188_);
lean_dec(v_a_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(lean_object* v_m_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_buckets_192_; lean_object* v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v_fold_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_buckets_192_ = lean_ctor_get(v_m_190_, 1);
v___x_193_ = lean_array_get_size(v_buckets_192_);
v___x_194_ = lean_uint64_of_nat(v_a_191_);
v___x_195_ = 32ULL;
v___x_196_ = lean_uint64_shift_right(v___x_194_, v___x_195_);
v_fold_197_ = lean_uint64_xor(v___x_194_, v___x_196_);
v___x_198_ = 16ULL;
v___x_199_ = lean_uint64_shift_right(v_fold_197_, v___x_198_);
v___x_200_ = lean_uint64_xor(v_fold_197_, v___x_199_);
v___x_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = lean_usize_of_nat(v___x_193_);
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_sub(v___x_202_, v___x_203_);
v___x_205_ = lean_usize_land(v___x_201_, v___x_204_);
v___x_206_ = lean_array_uget_borrowed(v_buckets_192_, v___x_205_);
v___x_207_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__8(v_a_191_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(lean_object* v_m_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_m_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_m_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(lean_object* v_atomsAssignment_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
if (lean_obj_tag(v_a_214_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_216_, 0, v_a_215_);
return v___x_216_;
}
else
{
lean_object* v_key_217_; lean_object* v_value_218_; lean_object* v_tail_219_; lean_object* v___y_221_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_a_255_; 
v_key_217_ = lean_ctor_get(v_a_214_, 0);
v_value_218_ = lean_ctor_get(v_a_214_, 1);
v_tail_219_ = lean_ctor_get(v_a_214_, 2);
v___x_253_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___closed__0));
v___x_254_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(v___x_253_, v_value_218_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v___x_254_);
v___y_221_ = v_a_255_;
goto v___jp_220_;
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v_snd_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_251_; 
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_atomsAssignment_213_, v_key_217_);
v_snd_223_ = lean_ctor_get(v___x_222_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v___x_222_, 0);
lean_dec(v_unused_252_);
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_251_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snd_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_251_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_250_; 
v_fst_227_ = lean_ctor_get(v_snd_223_, 0);
v_snd_228_ = lean_ctor_get(v_snd_223_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_snd_223_);
if (v_isSharedCheck_250_ == 0)
{
v___x_230_ = v_snd_223_;
v_isShared_231_ = v_isSharedCheck_250_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v_snd_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_250_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_249_; 
v_fst_232_ = lean_ctor_get(v___y_221_, 0);
v_snd_233_ = lean_ctor_get(v___y_221_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v___y_221_);
if (v_isSharedCheck_249_ == 0)
{
v___x_235_ = v___y_221_;
v_isShared_236_ = v_isSharedCheck_249_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_snd_233_);
lean_inc(v_fst_232_);
lean_dec(v___y_221_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_249_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = l_BitVec_ofNat(v_snd_233_, v_fst_232_);
lean_dec(v_fst_232_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_237_);
lean_ctor_set(v___x_225_, 0, v_snd_233_);
v___x_239_ = v___x_225_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_snd_233_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_248_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_239_);
lean_ctor_set(v___x_235_, 0, v_snd_228_);
v___x_241_ = v___x_235_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_snd_228_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_247_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_241_);
v___x_243_ = v___x_230_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_241_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_array_push(v_a_215_, v___x_243_);
v_a_214_ = v_tail_219_;
v_a_215_ = v___x_244_;
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___boxed(lean_object* v_atomsAssignment_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(v_atomsAssignment_256_, v_a_257_, v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_atomsAssignment_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(lean_object* v_atomsAssignment_260_, lean_object* v_as_261_, size_t v_sz_262_, size_t v_i_263_, lean_object* v_b_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_263_, v_sz_262_);
if (v___x_265_ == 0)
{
return v_b_264_;
}
else
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_array_uget_borrowed(v_as_261_, v_i_263_);
v___x_267_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(v_atomsAssignment_260_, v_a_266_, v_b_264_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
return v_a_268_;
}
else
{
lean_object* v_a_269_; size_t v___x_270_; size_t v___x_271_; 
v_a_269_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_267_, 1);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_add(v_i_263_, v___x_270_);
v_i_263_ = v___x_271_;
v_b_264_ = v_a_269_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(lean_object* v_atomsAssignment_273_, lean_object* v_as_274_, lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_b_277_){
_start:
{
size_t v_sz_boxed_278_; size_t v_i_boxed_279_; lean_object* v_res_280_; 
v_sz_boxed_278_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_279_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_atomsAssignment_273_, v_as_274_, v_sz_boxed_278_, v_i_boxed_279_, v_b_277_);
lean_dec_ref(v_as_274_);
lean_dec_ref(v_atomsAssignment_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(lean_object* v_k_281_, lean_object* v_v_282_, lean_object* v_t_283_){
_start:
{
if (lean_obj_tag(v_t_283_) == 0)
{
lean_object* v_size_284_; lean_object* v_k_285_; lean_object* v_v_286_; lean_object* v_l_287_; lean_object* v_r_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_569_; 
v_size_284_ = lean_ctor_get(v_t_283_, 0);
v_k_285_ = lean_ctor_get(v_t_283_, 1);
v_v_286_ = lean_ctor_get(v_t_283_, 2);
v_l_287_ = lean_ctor_get(v_t_283_, 3);
v_r_288_ = lean_ctor_get(v_t_283_, 4);
v_isSharedCheck_569_ = !lean_is_exclusive(v_t_283_);
if (v_isSharedCheck_569_ == 0)
{
v___x_290_ = v_t_283_;
v_isShared_291_ = v_isSharedCheck_569_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_r_288_);
lean_inc(v_l_287_);
lean_inc(v_v_286_);
lean_inc(v_k_285_);
lean_inc(v_size_284_);
lean_dec(v_t_283_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_569_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
uint8_t v___x_292_; 
v___x_292_ = lean_nat_dec_lt(v_k_281_, v_k_285_);
if (v___x_292_ == 0)
{
uint8_t v___x_293_; 
v___x_293_ = lean_nat_dec_eq(v_k_281_, v_k_285_);
if (v___x_293_ == 0)
{
lean_object* v_impl_294_; lean_object* v___x_295_; 
lean_dec(v_size_284_);
v_impl_294_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_k_281_, v_v_282_, v_r_288_);
v___x_295_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_287_) == 0)
{
lean_object* v_size_296_; lean_object* v_size_297_; lean_object* v_k_298_; lean_object* v_v_299_; lean_object* v_l_300_; lean_object* v_r_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_size_296_ = lean_ctor_get(v_l_287_, 0);
v_size_297_ = lean_ctor_get(v_impl_294_, 0);
v_k_298_ = lean_ctor_get(v_impl_294_, 1);
v_v_299_ = lean_ctor_get(v_impl_294_, 2);
v_l_300_ = lean_ctor_get(v_impl_294_, 3);
lean_inc(v_l_300_);
v_r_301_ = lean_ctor_get(v_impl_294_, 4);
v___x_302_ = lean_unsigned_to_nat(3u);
v___x_303_ = lean_nat_mul(v___x_302_, v_size_296_);
v___x_304_ = lean_nat_dec_lt(v___x_303_, v_size_297_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_dec(v_l_300_);
v___x_305_ = lean_nat_add(v___x_295_, v_size_296_);
v___x_306_ = lean_nat_add(v___x_305_, v_size_297_);
lean_dec(v___x_305_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_impl_294_);
lean_ctor_set(v___x_290_, 0, v___x_306_);
v___x_308_ = v___x_290_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_l_287_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_impl_294_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_373_; 
lean_inc(v_r_301_);
lean_inc(v_v_299_);
lean_inc(v_k_298_);
lean_inc(v_size_297_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_impl_294_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; lean_object* v_unused_376_; lean_object* v_unused_377_; lean_object* v_unused_378_; 
v_unused_374_ = lean_ctor_get(v_impl_294_, 4);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_impl_294_, 3);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_impl_294_, 2);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_impl_294_, 1);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_impl_294_, 0);
lean_dec(v_unused_378_);
v___x_311_ = v_impl_294_;
v_isShared_312_ = v_isSharedCheck_373_;
goto v_resetjp_310_;
}
else
{
lean_dec(v_impl_294_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_373_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_size_313_; lean_object* v_k_314_; lean_object* v_v_315_; lean_object* v_l_316_; lean_object* v_r_317_; lean_object* v_size_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_size_313_ = lean_ctor_get(v_l_300_, 0);
v_k_314_ = lean_ctor_get(v_l_300_, 1);
v_v_315_ = lean_ctor_get(v_l_300_, 2);
v_l_316_ = lean_ctor_get(v_l_300_, 3);
v_r_317_ = lean_ctor_get(v_l_300_, 4);
v_size_318_ = lean_ctor_get(v_r_301_, 0);
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = lean_nat_mul(v___x_319_, v_size_318_);
v___x_321_ = lean_nat_dec_lt(v_size_313_, v___x_320_);
lean_dec(v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_349_; 
lean_inc(v_r_317_);
lean_inc(v_l_316_);
lean_inc(v_v_315_);
lean_inc(v_k_314_);
v_isSharedCheck_349_ = !lean_is_exclusive(v_l_300_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_350_ = lean_ctor_get(v_l_300_, 4);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_l_300_, 3);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_l_300_, 2);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_l_300_, 1);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_l_300_, 0);
lean_dec(v_unused_354_);
v___x_323_ = v_l_300_;
v_isShared_324_ = v_isSharedCheck_349_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_l_300_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_349_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_339_; 
v___x_325_ = lean_nat_add(v___x_295_, v_size_296_);
v___x_326_ = lean_nat_add(v___x_325_, v_size_297_);
lean_dec(v_size_297_);
if (lean_obj_tag(v_l_316_) == 0)
{
lean_object* v_size_347_; 
v_size_347_ = lean_ctor_get(v_l_316_, 0);
lean_inc(v_size_347_);
v___y_339_ = v_size_347_;
goto v___jp_338_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___y_339_ = v___x_348_;
goto v___jp_338_;
}
v___jp_327_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_nat_add(v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec(v___y_329_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v_r_301_);
lean_ctor_set(v___x_323_, 3, v_r_317_);
lean_ctor_set(v___x_323_, 2, v_v_299_);
lean_ctor_set(v___x_323_, 1, v_k_298_);
lean_ctor_set(v___x_323_, 0, v___x_331_);
v___x_333_ = v___x_323_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_299_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_r_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_r_301_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v___x_333_);
lean_ctor_set(v___x_311_, 3, v___y_328_);
lean_ctor_set(v___x_311_, 2, v_v_315_);
lean_ctor_set(v___x_311_, 1, v_k_314_);
lean_ctor_set(v___x_311_, 0, v___x_326_);
v___x_335_ = v___x_311_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_k_314_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_v_315_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v___y_328_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
v___jp_338_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_nat_add(v___x_325_, v___y_339_);
lean_dec(v___y_339_);
lean_dec(v___x_325_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_l_316_);
lean_ctor_set(v___x_290_, 0, v___x_340_);
v___x_342_ = v___x_290_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_l_287_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_l_316_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; 
v___x_343_ = lean_nat_add(v___x_295_, v_size_318_);
if (lean_obj_tag(v_r_317_) == 0)
{
lean_object* v_size_344_; 
v_size_344_ = lean_ctor_get(v_r_317_, 0);
lean_inc(v_size_344_);
v___y_328_ = v___x_342_;
v___y_329_ = v___x_343_;
v___y_330_ = v_size_344_;
goto v___jp_327_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___y_328_ = v___x_342_;
v___y_329_ = v___x_343_;
v___y_330_ = v___x_345_;
goto v___jp_327_;
}
}
}
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
lean_del_object(v___x_290_);
v___x_355_ = lean_nat_add(v___x_295_, v_size_296_);
v___x_356_ = lean_nat_add(v___x_355_, v_size_297_);
lean_dec(v_size_297_);
v___x_357_ = lean_nat_add(v___x_355_, v_size_313_);
lean_dec(v___x_355_);
lean_inc_ref(v_l_287_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v_l_300_);
lean_ctor_set(v___x_311_, 3, v_l_287_);
lean_ctor_set(v___x_311_, 2, v_v_286_);
lean_ctor_set(v___x_311_, 1, v_k_285_);
lean_ctor_set(v___x_311_, 0, v___x_357_);
v___x_359_ = v___x_311_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_l_287_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_l_300_);
v___x_359_ = v_reuseFailAlloc_372_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_isSharedCheck_366_ = !lean_is_exclusive(v_l_287_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_367_ = lean_ctor_get(v_l_287_, 4);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_l_287_, 3);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_l_287_, 2);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_l_287_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_l_287_, 0);
lean_dec(v_unused_371_);
v___x_361_ = v_l_287_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_dec(v_l_287_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 4, v_r_301_);
lean_ctor_set(v___x_361_, 3, v___x_359_);
lean_ctor_set(v___x_361_, 2, v_v_299_);
lean_ctor_set(v___x_361_, 1, v_k_298_);
lean_ctor_set(v___x_361_, 0, v___x_356_);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_299_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_r_301_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_379_; 
v_l_379_ = lean_ctor_get(v_impl_294_, 3);
lean_inc(v_l_379_);
if (lean_obj_tag(v_l_379_) == 0)
{
lean_object* v_r_380_; lean_object* v_k_381_; lean_object* v_v_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_405_; 
v_r_380_ = lean_ctor_get(v_impl_294_, 4);
v_k_381_ = lean_ctor_get(v_impl_294_, 1);
v_v_382_ = lean_ctor_get(v_impl_294_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_impl_294_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_406_ = lean_ctor_get(v_impl_294_, 3);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_impl_294_, 0);
lean_dec(v_unused_407_);
v___x_384_ = v_impl_294_;
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_r_380_);
lean_inc(v_v_382_);
lean_inc(v_k_381_);
lean_dec(v_impl_294_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_k_386_; lean_object* v_v_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_401_; 
v_k_386_ = lean_ctor_get(v_l_379_, 1);
v_v_387_ = lean_ctor_get(v_l_379_, 2);
v_isSharedCheck_401_ = !lean_is_exclusive(v_l_379_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_402_ = lean_ctor_get(v_l_379_, 4);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_l_379_, 3);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_l_379_, 0);
lean_dec(v_unused_404_);
v___x_389_ = v_l_379_;
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_v_387_);
lean_inc(v_k_386_);
lean_dec(v_l_379_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_380_, 2);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 4, v_r_380_);
lean_ctor_set(v___x_389_, 3, v_r_380_);
lean_ctor_set(v___x_389_, 2, v_v_286_);
lean_ctor_set(v___x_389_, 1, v_k_285_);
lean_ctor_set(v___x_389_, 0, v___x_295_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_r_380_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_r_380_);
v___x_393_ = v_reuseFailAlloc_400_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
lean_inc(v_r_380_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 3, v_r_380_);
lean_ctor_set(v___x_384_, 0, v___x_295_);
v___x_395_ = v___x_384_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_k_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_v_382_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_r_380_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_r_380_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_395_);
lean_ctor_set(v___x_290_, 3, v___x_393_);
lean_ctor_set(v___x_290_, 2, v_v_387_);
lean_ctor_set(v___x_290_, 1, v_k_386_);
lean_ctor_set(v___x_290_, 0, v___x_391_);
v___x_397_ = v___x_290_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_387_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
else
{
lean_object* v_r_408_; 
v_r_408_ = lean_ctor_get(v_impl_294_, 4);
lean_inc(v_r_408_);
if (lean_obj_tag(v_r_408_) == 0)
{
lean_object* v_k_409_; lean_object* v_v_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_k_409_ = lean_ctor_get(v_impl_294_, 1);
v_v_410_ = lean_ctor_get(v_impl_294_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v_impl_294_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; lean_object* v_unused_423_; lean_object* v_unused_424_; 
v_unused_422_ = lean_ctor_get(v_impl_294_, 4);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_impl_294_, 3);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_impl_294_, 0);
lean_dec(v_unused_424_);
v___x_412_ = v_impl_294_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_v_410_);
lean_inc(v_k_409_);
lean_dec(v_impl_294_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(3u);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 4, v_l_379_);
lean_ctor_set(v___x_412_, 2, v_v_286_);
lean_ctor_set(v___x_412_, 1, v_k_285_);
lean_ctor_set(v___x_412_, 0, v___x_295_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_l_379_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_l_379_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_r_408_);
lean_ctor_set(v___x_290_, 3, v___x_416_);
lean_ctor_set(v___x_290_, 2, v_v_410_);
lean_ctor_set(v___x_290_, 1, v_k_409_);
lean_ctor_set(v___x_290_, 0, v___x_414_);
v___x_418_ = v___x_290_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_r_408_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_unsigned_to_nat(2u);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_impl_294_);
lean_ctor_set(v___x_290_, 3, v_r_408_);
lean_ctor_set(v___x_290_, 0, v___x_425_);
v___x_427_ = v___x_290_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_r_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_impl_294_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v_v_286_);
lean_dec(v_k_285_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 2, v_v_282_);
lean_ctor_set(v___x_290_, 1, v_k_281_);
v___x_430_ = v___x_290_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_size_284_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_k_281_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_v_282_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_l_287_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_r_288_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
else
{
lean_object* v_impl_432_; lean_object* v___x_433_; 
lean_dec(v_size_284_);
v_impl_432_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_k_281_, v_v_282_, v_l_287_);
v___x_433_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_288_) == 0)
{
lean_object* v_size_434_; lean_object* v_size_435_; lean_object* v_k_436_; lean_object* v_v_437_; lean_object* v_l_438_; lean_object* v_r_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_size_434_ = lean_ctor_get(v_r_288_, 0);
v_size_435_ = lean_ctor_get(v_impl_432_, 0);
v_k_436_ = lean_ctor_get(v_impl_432_, 1);
v_v_437_ = lean_ctor_get(v_impl_432_, 2);
v_l_438_ = lean_ctor_get(v_impl_432_, 3);
v_r_439_ = lean_ctor_get(v_impl_432_, 4);
lean_inc(v_r_439_);
v___x_440_ = lean_unsigned_to_nat(3u);
v___x_441_ = lean_nat_mul(v___x_440_, v_size_434_);
v___x_442_ = lean_nat_dec_lt(v___x_441_, v_size_435_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
lean_dec(v_r_439_);
v___x_443_ = lean_nat_add(v___x_433_, v_size_435_);
v___x_444_ = lean_nat_add(v___x_443_, v_size_434_);
lean_dec(v___x_443_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 3, v_impl_432_);
lean_ctor_set(v___x_290_, 0, v___x_444_);
v___x_446_ = v___x_290_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_impl_432_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_r_288_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_513_; 
lean_inc(v_l_438_);
lean_inc(v_v_437_);
lean_inc(v_k_436_);
lean_inc(v_size_435_);
v_isSharedCheck_513_ = !lean_is_exclusive(v_impl_432_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; lean_object* v_unused_518_; 
v_unused_514_ = lean_ctor_get(v_impl_432_, 4);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_impl_432_, 3);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_impl_432_, 2);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_impl_432_, 1);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_impl_432_, 0);
lean_dec(v_unused_518_);
v___x_449_ = v_impl_432_;
v_isShared_450_ = v_isSharedCheck_513_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_impl_432_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_513_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_size_451_; lean_object* v_size_452_; lean_object* v_k_453_; lean_object* v_v_454_; lean_object* v_l_455_; lean_object* v_r_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_size_451_ = lean_ctor_get(v_l_438_, 0);
v_size_452_ = lean_ctor_get(v_r_439_, 0);
v_k_453_ = lean_ctor_get(v_r_439_, 1);
v_v_454_ = lean_ctor_get(v_r_439_, 2);
v_l_455_ = lean_ctor_get(v_r_439_, 3);
v_r_456_ = lean_ctor_get(v_r_439_, 4);
v___x_457_ = lean_unsigned_to_nat(2u);
v___x_458_ = lean_nat_mul(v___x_457_, v_size_451_);
v___x_459_ = lean_nat_dec_lt(v_size_452_, v___x_458_);
lean_dec(v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_488_; 
lean_inc(v_r_456_);
lean_inc(v_l_455_);
lean_inc(v_v_454_);
lean_inc(v_k_453_);
v_isSharedCheck_488_ = !lean_is_exclusive(v_r_439_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; lean_object* v_unused_490_; lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_489_ = lean_ctor_get(v_r_439_, 4);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_r_439_, 3);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_r_439_, 2);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_r_439_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_r_439_, 0);
lean_dec(v_unused_493_);
v___x_461_ = v_r_439_;
v_isShared_462_ = v_isSharedCheck_488_;
goto v_resetjp_460_;
}
else
{
lean_dec(v_r_439_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_488_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___x_476_; lean_object* v___y_478_; 
v___x_463_ = lean_nat_add(v___x_433_, v_size_435_);
lean_dec(v_size_435_);
v___x_464_ = lean_nat_add(v___x_463_, v_size_434_);
lean_dec(v___x_463_);
v___x_476_ = lean_nat_add(v___x_433_, v_size_451_);
if (lean_obj_tag(v_l_455_) == 0)
{
lean_object* v_size_486_; 
v_size_486_ = lean_ctor_get(v_l_455_, 0);
lean_inc(v_size_486_);
v___y_478_ = v_size_486_;
goto v___jp_477_;
}
else
{
lean_object* v___x_487_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v___y_478_ = v___x_487_;
goto v___jp_477_;
}
v___jp_465_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_nat_add(v___y_466_, v___y_468_);
lean_dec(v___y_468_);
lean_dec(v___y_466_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 4, v_r_288_);
lean_ctor_set(v___x_461_, 3, v_r_456_);
lean_ctor_set(v___x_461_, 2, v_v_286_);
lean_ctor_set(v___x_461_, 1, v_k_285_);
lean_ctor_set(v___x_461_, 0, v___x_469_);
v___x_471_ = v___x_461_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_r_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_r_288_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 4, v___x_471_);
lean_ctor_set(v___x_449_, 3, v___y_467_);
lean_ctor_set(v___x_449_, 2, v_v_454_);
lean_ctor_set(v___x_449_, 1, v_k_453_);
lean_ctor_set(v___x_449_, 0, v___x_464_);
v___x_473_ = v___x_449_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_k_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_v_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v___y_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_nat_add(v___x_476_, v___y_478_);
lean_dec(v___y_478_);
lean_dec(v___x_476_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_l_455_);
lean_ctor_set(v___x_290_, 3, v_l_438_);
lean_ctor_set(v___x_290_, 2, v_v_437_);
lean_ctor_set(v___x_290_, 1, v_k_436_);
lean_ctor_set(v___x_290_, 0, v___x_479_);
v___x_481_ = v___x_290_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_k_436_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_v_437_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_l_438_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_l_455_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_nat_add(v___x_433_, v_size_434_);
if (lean_obj_tag(v_r_456_) == 0)
{
lean_object* v_size_483_; 
v_size_483_ = lean_ctor_get(v_r_456_, 0);
lean_inc(v_size_483_);
v___y_466_ = v___x_482_;
v___y_467_ = v___x_481_;
v___y_468_ = v_size_483_;
goto v___jp_465_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___y_466_ = v___x_482_;
v___y_467_ = v___x_481_;
v___y_468_ = v___x_484_;
goto v___jp_465_;
}
}
}
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_del_object(v___x_290_);
v___x_494_ = lean_nat_add(v___x_433_, v_size_435_);
lean_dec(v_size_435_);
v___x_495_ = lean_nat_add(v___x_494_, v_size_434_);
lean_dec(v___x_494_);
v___x_496_ = lean_nat_add(v___x_433_, v_size_434_);
v___x_497_ = lean_nat_add(v___x_496_, v_size_452_);
lean_dec(v___x_496_);
lean_inc_ref(v_r_288_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 4, v_r_288_);
lean_ctor_set(v___x_449_, 3, v_r_439_);
lean_ctor_set(v___x_449_, 2, v_v_286_);
lean_ctor_set(v___x_449_, 1, v_k_285_);
lean_ctor_set(v___x_449_, 0, v___x_497_);
v___x_499_ = v___x_449_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_r_439_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_r_288_);
v___x_499_ = v_reuseFailAlloc_512_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_isSharedCheck_506_ = !lean_is_exclusive(v_r_288_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; lean_object* v_unused_509_; lean_object* v_unused_510_; lean_object* v_unused_511_; 
v_unused_507_ = lean_ctor_get(v_r_288_, 4);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_r_288_, 3);
lean_dec(v_unused_508_);
v_unused_509_ = lean_ctor_get(v_r_288_, 2);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_r_288_, 1);
lean_dec(v_unused_510_);
v_unused_511_ = lean_ctor_get(v_r_288_, 0);
lean_dec(v_unused_511_);
v___x_501_ = v_r_288_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_dec(v_r_288_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v___x_499_);
lean_ctor_set(v___x_501_, 3, v_l_438_);
lean_ctor_set(v___x_501_, 2, v_v_437_);
lean_ctor_set(v___x_501_, 1, v_k_436_);
lean_ctor_set(v___x_501_, 0, v___x_495_);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_k_436_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_v_437_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_l_438_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v___x_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_519_; 
v_l_519_ = lean_ctor_get(v_impl_432_, 3);
if (lean_obj_tag(v_l_519_) == 0)
{
lean_object* v_r_520_; lean_object* v_k_521_; lean_object* v_v_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
lean_inc_ref(v_l_519_);
v_r_520_ = lean_ctor_get(v_impl_432_, 4);
v_k_521_ = lean_ctor_get(v_impl_432_, 1);
v_v_522_ = lean_ctor_get(v_impl_432_, 2);
v_isSharedCheck_533_ = !lean_is_exclusive(v_impl_432_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; lean_object* v_unused_535_; 
v_unused_534_ = lean_ctor_get(v_impl_432_, 3);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_impl_432_, 0);
lean_dec(v_unused_535_);
v___x_524_ = v_impl_432_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_r_520_);
lean_inc(v_v_522_);
lean_inc(v_k_521_);
lean_dec(v_impl_432_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_520_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v_r_520_);
lean_ctor_set(v___x_524_, 2, v_v_286_);
lean_ctor_set(v___x_524_, 1, v_k_285_);
lean_ctor_set(v___x_524_, 0, v___x_433_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_r_520_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_r_520_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_528_);
lean_ctor_set(v___x_290_, 3, v_l_519_);
lean_ctor_set(v___x_290_, 2, v_v_522_);
lean_ctor_set(v___x_290_, 1, v_k_521_);
lean_ctor_set(v___x_290_, 0, v___x_526_);
v___x_530_ = v___x_290_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_k_521_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_v_522_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_l_519_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_r_536_; 
v_r_536_ = lean_ctor_get(v_impl_432_, 4);
lean_inc(v_r_536_);
if (lean_obj_tag(v_r_536_) == 0)
{
lean_object* v_k_537_; lean_object* v_v_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_561_; 
lean_inc(v_l_519_);
v_k_537_ = lean_ctor_get(v_impl_432_, 1);
v_v_538_ = lean_ctor_get(v_impl_432_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v_impl_432_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; lean_object* v_unused_564_; 
v_unused_562_ = lean_ctor_get(v_impl_432_, 4);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_impl_432_, 3);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_impl_432_, 0);
lean_dec(v_unused_564_);
v___x_540_ = v_impl_432_;
v_isShared_541_ = v_isSharedCheck_561_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_v_538_);
lean_inc(v_k_537_);
lean_dec(v_impl_432_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_561_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_k_542_; lean_object* v_v_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_557_; 
v_k_542_ = lean_ctor_get(v_r_536_, 1);
v_v_543_ = lean_ctor_get(v_r_536_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_r_536_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_558_ = lean_ctor_get(v_r_536_, 4);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_r_536_, 3);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_r_536_, 0);
lean_dec(v_unused_560_);
v___x_545_ = v_r_536_;
v_isShared_546_ = v_isSharedCheck_557_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_v_543_);
lean_inc(v_k_542_);
lean_dec(v_r_536_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_557_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(3u);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 4, v_l_519_);
lean_ctor_set(v___x_545_, 3, v_l_519_);
lean_ctor_set(v___x_545_, 2, v_v_538_);
lean_ctor_set(v___x_545_, 1, v_k_537_);
lean_ctor_set(v___x_545_, 0, v___x_433_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_l_519_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_l_519_);
v___x_549_ = v_reuseFailAlloc_556_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 4, v_l_519_);
lean_ctor_set(v___x_540_, 2, v_v_286_);
lean_ctor_set(v___x_540_, 1, v_k_285_);
lean_ctor_set(v___x_540_, 0, v___x_433_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_l_519_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_l_519_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_551_);
lean_ctor_set(v___x_290_, 3, v___x_549_);
lean_ctor_set(v___x_290_, 2, v_v_543_);
lean_ctor_set(v___x_290_, 1, v_k_542_);
lean_ctor_set(v___x_290_, 0, v___x_547_);
v___x_553_ = v___x_290_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(2u);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_r_536_);
lean_ctor_set(v___x_290_, 3, v_impl_432_);
lean_ctor_set(v___x_290_, 0, v___x_565_);
v___x_567_ = v___x_290_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_k_285_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_v_286_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_impl_432_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_r_536_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_k_281_);
lean_ctor_set(v___x_571_, 2, v_v_282_);
lean_ctor_set(v___x_571_, 3, v_t_283_);
lean_ctor_set(v___x_571_, 4, v_t_283_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(lean_object* v_a_572_, lean_object* v_fallback_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
lean_inc(v_fallback_573_);
return v_fallback_573_;
}
else
{
lean_object* v_key_575_; lean_object* v_value_576_; lean_object* v_tail_577_; uint8_t v___x_578_; 
v_key_575_ = lean_ctor_get(v_x_574_, 0);
v_value_576_ = lean_ctor_get(v_x_574_, 1);
v_tail_577_ = lean_ctor_get(v_x_574_, 2);
v___x_578_ = lean_nat_dec_eq(v_key_575_, v_a_572_);
if (v___x_578_ == 0)
{
v_x_574_ = v_tail_577_;
goto _start;
}
else
{
lean_inc(v_value_576_);
return v_value_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg___boxed(lean_object* v_a_580_, lean_object* v_fallback_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_a_580_, v_fallback_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec(v_fallback_581_);
lean_dec(v_a_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(lean_object* v_m_584_, lean_object* v_a_585_, lean_object* v_fallback_586_){
_start:
{
lean_object* v_buckets_587_; lean_object* v___x_588_; uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v_fold_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_buckets_587_ = lean_ctor_get(v_m_584_, 1);
v___x_588_ = lean_array_get_size(v_buckets_587_);
v___x_589_ = lean_uint64_of_nat(v_a_585_);
v___x_590_ = 32ULL;
v___x_591_ = lean_uint64_shift_right(v___x_589_, v___x_590_);
v_fold_592_ = lean_uint64_xor(v___x_589_, v___x_591_);
v___x_593_ = 16ULL;
v___x_594_ = lean_uint64_shift_right(v_fold_592_, v___x_593_);
v___x_595_ = lean_uint64_xor(v_fold_592_, v___x_594_);
v___x_596_ = lean_uint64_to_usize(v___x_595_);
v___x_597_ = lean_usize_of_nat(v___x_588_);
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_sub(v___x_597_, v___x_598_);
v___x_600_ = lean_usize_land(v___x_596_, v___x_599_);
v___x_601_ = lean_array_uget_borrowed(v_buckets_587_, v___x_600_);
v___x_602_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_a_585_, v_fallback_586_, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg___boxed(lean_object* v_m_603_, lean_object* v_a_604_, lean_object* v_fallback_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(v_m_603_, v_a_604_, v_fallback_605_);
lean_dec(v_fallback_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_m_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
return v_x_607_;
}
else
{
lean_object* v_key_609_; lean_object* v_value_610_; lean_object* v_tail_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_634_; 
v_key_609_ = lean_ctor_get(v_x_608_, 0);
v_value_610_ = lean_ctor_get(v_x_608_, 1);
v_tail_611_ = lean_ctor_get(v_x_608_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_634_ == 0)
{
v___x_613_ = v_x_608_;
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_tail_611_);
lean_inc(v_value_610_);
lean_inc(v_key_609_);
lean_dec(v_x_608_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v___x_618_; uint64_t v_fold_619_; uint64_t v___x_620_; uint64_t v___x_621_; uint64_t v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_615_ = lean_array_get_size(v_x_607_);
v___x_616_ = lean_uint64_of_nat(v_key_609_);
v___x_617_ = 32ULL;
v___x_618_ = lean_uint64_shift_right(v___x_616_, v___x_617_);
v_fold_619_ = lean_uint64_xor(v___x_616_, v___x_618_);
v___x_620_ = 16ULL;
v___x_621_ = lean_uint64_shift_right(v_fold_619_, v___x_620_);
v___x_622_ = lean_uint64_xor(v_fold_619_, v___x_621_);
v___x_623_ = lean_uint64_to_usize(v___x_622_);
v___x_624_ = lean_usize_of_nat(v___x_615_);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_sub(v___x_624_, v___x_625_);
v___x_627_ = lean_usize_land(v___x_623_, v___x_626_);
v___x_628_ = lean_array_uget_borrowed(v_x_607_, v___x_627_);
lean_inc(v___x_628_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 2, v___x_628_);
v___x_630_ = v___x_613_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_key_609_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_value_610_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v___x_628_);
v___x_630_ = v_reuseFailAlloc_633_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; 
v___x_631_ = lean_array_uset(v_x_607_, v___x_627_, v___x_630_);
v_x_607_ = v___x_631_;
v_x_608_ = v_tail_611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(lean_object* v_i_635_, lean_object* v_source_636_, lean_object* v_target_637_){
_start:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_array_get_size(v_source_636_);
v___x_639_ = lean_nat_dec_lt(v_i_635_, v___x_638_);
if (v___x_639_ == 0)
{
lean_dec_ref(v_source_636_);
lean_dec(v_i_635_);
return v_target_637_;
}
else
{
lean_object* v_es_640_; lean_object* v___x_641_; lean_object* v_source_642_; lean_object* v_target_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_es_640_ = lean_array_fget(v_source_636_, v_i_635_);
v___x_641_ = lean_box(0);
v_source_642_ = lean_array_fset(v_source_636_, v_i_635_, v___x_641_);
v_target_643_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(v_target_637_, v_es_640_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_i_635_, v___x_644_);
lean_dec(v_i_635_);
v_i_635_ = v___x_645_;
v_source_636_ = v_source_642_;
v_target_637_ = v_target_643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(lean_object* v_data_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_nbuckets_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_648_ = lean_array_get_size(v_data_647_);
v___x_649_ = lean_unsigned_to_nat(2u);
v_nbuckets_650_ = lean_nat_mul(v___x_648_, v___x_649_);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_box(0);
v___x_653_ = lean_mk_array(v_nbuckets_650_, v___x_652_);
v___x_654_ = lean_array_propagate_mark(v_data_647_, v___x_653_);
v___x_655_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(v___x_651_, v_data_647_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(lean_object* v_a_656_, lean_object* v_b_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_dec(v_b_657_);
lean_dec(v_a_656_);
return v_x_658_;
}
else
{
lean_object* v_key_659_; lean_object* v_value_660_; lean_object* v_tail_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_673_; 
v_key_659_ = lean_ctor_get(v_x_658_, 0);
v_value_660_ = lean_ctor_get(v_x_658_, 1);
v_tail_661_ = lean_ctor_get(v_x_658_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_673_ == 0)
{
v___x_663_ = v_x_658_;
v_isShared_664_ = v_isSharedCheck_673_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_tail_661_);
lean_inc(v_value_660_);
lean_inc(v_key_659_);
lean_dec(v_x_658_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_673_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_eq(v_key_659_, v_a_656_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(v_a_656_, v_b_657_, v_tail_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 2, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_key_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_value_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v___x_671_; 
lean_dec(v_value_660_);
lean_dec(v_key_659_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_b_657_);
lean_ctor_set(v___x_663_, 0, v_a_656_);
v___x_671_ = v___x_663_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_656_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_b_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_tail_661_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(lean_object* v_m_674_, lean_object* v_a_675_, lean_object* v_b_676_){
_start:
{
lean_object* v_size_677_; lean_object* v_buckets_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_721_; 
v_size_677_ = lean_ctor_get(v_m_674_, 0);
v_buckets_678_ = lean_ctor_get(v_m_674_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_m_674_);
if (v_isSharedCheck_721_ == 0)
{
v___x_680_ = v_m_674_;
v_isShared_681_ = v_isSharedCheck_721_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_buckets_678_);
lean_inc(v_size_677_);
lean_dec(v_m_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_721_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v_fold_686_; uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; size_t v___x_694_; lean_object* v_bkt_695_; uint8_t v___x_696_; 
v___x_682_ = lean_array_get_size(v_buckets_678_);
v___x_683_ = lean_uint64_of_nat(v_a_675_);
v___x_684_ = 32ULL;
v___x_685_ = lean_uint64_shift_right(v___x_683_, v___x_684_);
v_fold_686_ = lean_uint64_xor(v___x_683_, v___x_685_);
v___x_687_ = 16ULL;
v___x_688_ = lean_uint64_shift_right(v_fold_686_, v___x_687_);
v___x_689_ = lean_uint64_xor(v_fold_686_, v___x_688_);
v___x_690_ = lean_uint64_to_usize(v___x_689_);
v___x_691_ = lean_usize_of_nat(v___x_682_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_sub(v___x_691_, v___x_692_);
v___x_694_ = lean_usize_land(v___x_690_, v___x_693_);
v_bkt_695_ = lean_array_uget_borrowed(v_buckets_678_, v___x_694_);
v___x_696_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_675_, v_bkt_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v_size_x27_698_; lean_object* v___x_699_; lean_object* v_buckets_x27_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v_size_x27_698_ = lean_nat_add(v_size_677_, v___x_697_);
lean_dec(v_size_677_);
lean_inc(v_bkt_695_);
v___x_699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_699_, 0, v_a_675_);
lean_ctor_set(v___x_699_, 1, v_b_676_);
lean_ctor_set(v___x_699_, 2, v_bkt_695_);
v_buckets_x27_700_ = lean_array_uset(v_buckets_678_, v___x_694_, v___x_699_);
v___x_701_ = lean_unsigned_to_nat(4u);
v___x_702_ = lean_nat_mul(v_size_x27_698_, v___x_701_);
v___x_703_ = lean_unsigned_to_nat(3u);
v___x_704_ = lean_nat_div(v___x_702_, v___x_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_array_get_size(v_buckets_x27_700_);
v___x_706_ = lean_nat_dec_le(v___x_704_, v___x_705_);
lean_dec(v___x_704_);
if (v___x_706_ == 0)
{
lean_object* v_val_707_; lean_object* v___x_709_; 
v_val_707_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(v_buckets_x27_700_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_val_707_);
lean_ctor_set(v___x_680_, 0, v_size_x27_698_);
v___x_709_ = v___x_680_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_size_x27_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_val_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v___x_712_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_buckets_x27_700_);
lean_ctor_set(v___x_680_, 0, v_size_x27_698_);
v___x_712_ = v___x_680_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_size_x27_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_buckets_x27_700_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v___x_714_; lean_object* v_buckets_x27_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
lean_inc(v_bkt_695_);
v___x_714_ = lean_box(0);
v_buckets_x27_715_ = lean_array_uset(v_buckets_678_, v___x_694_, v___x_714_);
v___x_716_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(v_a_675_, v_b_676_, v_bkt_695_);
v___x_717_ = lean_array_uset(v_buckets_x27_715_, v___x_694_, v___x_716_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_717_);
v___x_719_ = v___x_680_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_size_677_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(lean_object* v_assignment_722_, lean_object* v_as_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_b_726_){
_start:
{
lean_object* v_a_728_; uint8_t v___x_732_; 
v___x_732_ = lean_usize_dec_lt(v_i_725_, v_sz_724_);
if (v___x_732_ == 0)
{
return v_b_726_;
}
else
{
lean_object* v_a_733_; lean_object* v_fst_734_; 
v_a_733_ = lean_array_uget_borrowed(v_as_723_, v_i_725_);
v_fst_734_ = lean_ctor_get(v_a_733_, 0);
if (lean_obj_tag(v_fst_734_) == 1)
{
lean_object* v_snd_735_; lean_object* v_idx_736_; uint8_t v___y_738_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_snd_735_ = lean_ctor_get(v_a_733_, 1);
v_idx_736_ = lean_ctor_get(v_fst_734_, 0);
v___x_746_ = lean_array_get_size(v_assignment_722_);
v___x_747_ = lean_nat_dec_lt(v_snd_735_, v___x_746_);
if (v___x_747_ == 0)
{
v___y_738_ = v___x_732_;
goto v___jp_737_;
}
else
{
lean_object* v___x_748_; lean_object* v_fst_749_; uint8_t v___x_750_; 
v___x_748_ = lean_array_fget_borrowed(v_assignment_722_, v_snd_735_);
v_fst_749_ = lean_ctor_get(v___x_748_, 0);
v___x_750_ = lean_unbox(v_fst_749_);
v___y_738_ = v___x_750_;
goto v___jp_737_;
}
v___jp_737_:
{
lean_object* v_var_739_; lean_object* v_idx_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_var_739_ = lean_ctor_get(v_idx_736_, 0);
v_idx_740_ = lean_ctor_get(v_idx_736_, 2);
v___x_741_ = lean_box(1);
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(v_b_726_, v_var_739_, v___x_741_);
v___x_743_ = lean_box(v___y_738_);
lean_inc(v_idx_740_);
v___x_744_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_idx_740_, v___x_743_, v___x_742_);
lean_inc(v_var_739_);
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_b_726_, v_var_739_, v___x_744_);
v_a_728_ = v___x_745_;
goto v___jp_727_;
}
}
else
{
v_a_728_ = v_b_726_;
goto v___jp_727_;
}
}
v___jp_727_:
{
size_t v___x_729_; size_t v___x_730_; 
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_725_, v___x_729_);
v_i_725_ = v___x_730_;
v_b_726_ = v_a_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(lean_object* v_assignment_751_, lean_object* v_as_752_, lean_object* v_sz_753_, lean_object* v_i_754_, lean_object* v_b_755_){
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_753_);
lean_dec(v_sz_753_);
v_i_boxed_757_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_assignment_751_, v_as_752_, v_sz_boxed_756_, v_i_boxed_757_, v_b_755_);
lean_dec_ref(v_as_752_);
lean_dec_ref(v_assignment_751_);
return v_res_758_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_box(0);
v___x_760_ = lean_unsigned_to_nat(16u);
v___x_761_ = lean_mk_array(v___x_760_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_sparseMap_764_; 
v___x_762_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0);
v___x_763_ = lean_unsigned_to_nat(0u);
v_sparseMap_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_sparseMap_764_, 0, v___x_763_);
lean_ctor_set(v_sparseMap_764_, 1, v___x_762_);
return v_sparseMap_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object* v_aig_767_, lean_object* v_assignment_768_, lean_object* v_atomsAssignment_769_){
_start:
{
lean_object* v_decls_770_; lean_object* v___x_771_; lean_object* v_sparseMap_772_; lean_object* v___x_773_; size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; lean_object* v_buckets_777_; lean_object* v_buckets_778_; size_t v_sz_779_; lean_object* v___x_780_; lean_object* v___x_781_; size_t v_sz_782_; lean_object* v___x_783_; 
v_decls_770_ = lean_ctor_get(v_aig_767_, 0);
lean_inc_ref(v_decls_770_);
lean_dec_ref(v_aig_767_);
v___x_771_ = lean_unsigned_to_nat(0u);
v_sparseMap_772_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1, &l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1);
v___x_773_ = l_Array_zipIdx___redArg(v_decls_770_, v___x_771_);
v_sz_774_ = lean_array_size(v___x_773_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_assignment_768_, v___x_773_, v_sz_774_, v___x_775_, v_sparseMap_772_);
lean_dec_ref(v___x_773_);
v_buckets_777_ = lean_ctor_get(v___x_776_, 1);
v_buckets_778_ = lean_ctor_get(v_atomsAssignment_769_, 1);
v_sz_779_ = lean_array_size(v_buckets_777_);
v___x_780_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2));
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_atomsAssignment_769_, v_buckets_777_, v_sz_779_, v___x_775_, v___x_780_);
v_sz_782_ = lean_array_size(v_buckets_778_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v___x_776_, v_buckets_778_, v_sz_782_, v___x_775_, v___x_781_);
lean_dec_ref(v___x_776_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(lean_object* v_aig_784_, lean_object* v_assignment_785_, lean_object* v_atomsAssignment_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_784_, v_assignment_785_, v_atomsAssignment_786_);
lean_dec_ref(v_atomsAssignment_786_);
lean_dec_ref(v_assignment_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_m_789_, lean_object* v_a_790_, lean_object* v_fallback_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___redArg(v_m_789_, v_a_790_, v_fallback_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_fallback_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_00_u03b2_793_, v_m_794_, v_a_795_, v_fallback_796_);
lean_dec(v_fallback_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_m_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(lean_object* v_00_u03b2_798_, lean_object* v_k_799_, lean_object* v_v_800_, lean_object* v_t_801_, lean_object* v_hl_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___redArg(v_k_799_, v_v_800_, v_t_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(lean_object* v_00_u03b2_804_, lean_object* v_m_805_, lean_object* v_a_806_, lean_object* v_b_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_m_805_, v_a_806_, v_b_807_);
return v___x_808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(lean_object* v_00_u03b2_809_, lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___redArg(v_m_810_, v_a_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(lean_object* v_00_u03b2_813_, lean_object* v_m_814_, lean_object* v_a_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_00_u03b2_813_, v_m_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_m_814_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(lean_object* v_00_u03b2_818_, lean_object* v_a_819_, lean_object* v_fallback_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___redArg(v_a_819_, v_fallback_820_, v_x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(lean_object* v_00_u03b2_823_, lean_object* v_a_824_, lean_object* v_fallback_825_, lean_object* v_x_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_00_u03b2_823_, v_a_824_, v_fallback_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_fallback_825_);
lean_dec(v_a_824_);
return v_res_827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___redArg(v_a_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4___boxed(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__4(v_00_u03b2_832_, v_a_833_, v_x_834_);
lean_dec(v_x_834_);
lean_dec(v_a_833_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5(lean_object* v_00_u03b2_837_, lean_object* v_data_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5___redArg(v_data_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_b_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__6___redArg(v_a_841_, v_b_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_845_, lean_object* v_i_846_, lean_object* v_source_847_, lean_object* v_target_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6___redArg(v_i_846_, v_source_847_, v_target_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3_spec__5_spec__6_spec__15___redArg(v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(lean_object* v_mvarId_854_, lean_object* v_x_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_854_, v_x_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_861_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_861_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(lean_object* v_mvarId_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_878_, v_x_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(lean_object* v_00_u03b1_886_, lean_object* v_mvarId_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_887_, v_x_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(lean_object* v_00_u03b1_895_, lean_object* v_mvarId_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(v_00_u03b1_895_, v_mvarId_896_, v_x_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(lean_object* v___x_904_, lean_object* v_x_905_, lean_object* v_counterExample_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_st_mk_ref(v___x_904_);
lean_inc(v___x_912_);
v___x_913_ = lean_apply_7(v_x_905_, v_counterExample_906_, v___x_912_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, lean_box(0));
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_922_);
v___x_915_ = v___x_913_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___x_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_st_ref_get(v___x_912_);
lean_dec(v___x_912_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v___x_912_);
v_a_923_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_913_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(lean_object* v___x_931_, lean_object* v_x_932_, lean_object* v_counterExample_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_931_, v_x_932_, v_counterExample_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_box(0);
v___x_941_ = lean_unsigned_to_nat(16u);
v___x_942_ = lean_mk_array(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3));
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2));
v___x_952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1);
v___x_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v___x_951_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
lean_ctor_set(v___x_953_, 3, v___x_952_);
lean_ctor_set(v___x_953_, 4, v___x_950_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(lean_object* v_x_954_, lean_object* v_counterExample_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_goal_961_; lean_object* v___x_962_; lean_object* v___f_963_; lean_object* v___x_964_; 
v_goal_961_ = lean_ctor_get(v_counterExample_955_, 0);
lean_inc(v_goal_961_);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__4);
v___f_963_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed), 8, 3);
lean_closure_set(v___f_963_, 0, v___x_962_);
lean_closure_set(v___f_963_, 1, v_x_954_);
lean_closure_set(v___f_963_, 2, v_counterExample_955_);
v___x_964_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_goal_961_, v___f_963_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(lean_object* v_x_965_, lean_object* v_counterExample_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_965_, v_counterExample_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(lean_object* v_a_973_){
_start:
{
lean_object* v_unusedHypotheses_975_; lean_object* v___x_976_; 
v_unusedHypotheses_975_ = lean_ctor_get(v_a_973_, 1);
lean_inc_ref(v_unusedHypotheses_975_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_unusedHypotheses_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_977_);
lean_dec_ref(v_a_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_unusedHypotheses_987_; lean_object* v___x_988_; 
v_unusedHypotheses_987_ = lean_ctor_get(v_a_980_, 1);
lean_inc_ref(v_unusedHypotheses_987_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_unusedHypotheses_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(lean_object* v_a_997_){
_start:
{
lean_object* v_equations_999_; lean_object* v___x_1000_; 
v_equations_999_ = lean_ctor_get(v_a_997_, 2);
lean_inc_ref(v_equations_999_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_equations_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_1001_);
lean_dec_ref(v_a_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_equations_1011_; lean_object* v___x_1012_; 
v_equations_1011_ = lean_ctor_get(v_a_1004_, 2);
lean_inc_ref(v_equations_1011_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_equations_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(lean_object* v_e_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_uninterpretedSymbols_1029_; lean_object* v_functionSymbols_1030_; lean_object* v_functionSymbolSet_1031_; lean_object* v_unusedRelevantHypotheses_1032_; lean_object* v_derivedEquations_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1044_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1028_ = lean_st_ref_take(v_a_1024_);
v_uninterpretedSymbols_1029_ = lean_ctor_get(v___x_1028_, 0);
v_functionSymbols_1030_ = lean_ctor_get(v___x_1028_, 1);
v_functionSymbolSet_1031_ = lean_ctor_get(v___x_1028_, 2);
v_unusedRelevantHypotheses_1032_ = lean_ctor_get(v___x_1028_, 3);
v_derivedEquations_1033_ = lean_ctor_get(v___x_1028_, 4);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1035_ = v___x_1028_;
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_derivedEquations_1033_);
lean_inc(v_unusedRelevantHypotheses_1032_);
lean_inc(v_functionSymbolSet_1031_);
lean_inc(v_functionSymbols_1030_);
lean_inc(v_uninterpretedSymbols_1029_);
lean_dec(v___x_1028_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1026_, v___x_1027_, v_uninterpretedSymbols_1029_, v_e_1023_, v___x_1037_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1038_);
v___x_1040_ = v___x_1035_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_functionSymbols_1030_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_functionSymbolSet_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_unusedRelevantHypotheses_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_derivedEquations_1033_);
v___x_1040_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_st_ref_put(v_a_1024_, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1037_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object* v_e_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_1045_, v_a_1046_);
lean_dec(v_a_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(lean_object* v_e_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_uninterpretedSymbols_1060_; lean_object* v_functionSymbols_1061_; lean_object* v_functionSymbolSet_1062_; lean_object* v_unusedRelevantHypotheses_1063_; lean_object* v_derivedEquations_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1059_ = lean_st_ref_take(v_a_1051_);
v_uninterpretedSymbols_1060_ = lean_ctor_get(v___x_1059_, 0);
v_functionSymbols_1061_ = lean_ctor_get(v___x_1059_, 1);
v_functionSymbolSet_1062_ = lean_ctor_get(v___x_1059_, 2);
v_unusedRelevantHypotheses_1063_ = lean_ctor_get(v___x_1059_, 3);
v_derivedEquations_1064_ = lean_ctor_get(v___x_1059_, 4);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v___x_1059_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_derivedEquations_1064_);
lean_inc(v_unusedRelevantHypotheses_1063_);
lean_inc(v_functionSymbolSet_1062_);
lean_inc(v_functionSymbols_1061_);
lean_inc(v_uninterpretedSymbols_1060_);
lean_dec(v___x_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1057_, v___x_1058_, v_uninterpretedSymbols_1060_, v_e_1049_, v___x_1068_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1069_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_functionSymbols_1061_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_functionSymbolSet_1062_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_unusedRelevantHypotheses_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_derivedEquations_1064_);
v___x_1071_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_st_ref_put(v_a_1051_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1068_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(lean_object* v_e_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg(lean_object* v_e_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_uninterpretedSymbols_1091_; lean_object* v_functionSymbols_1092_; lean_object* v_functionSymbolSet_1093_; lean_object* v_unusedRelevantHypotheses_1094_; lean_object* v_derivedEquations_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1107_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1090_ = lean_st_ref_take(v_a_1086_);
v_uninterpretedSymbols_1091_ = lean_ctor_get(v___x_1090_, 0);
v_functionSymbols_1092_ = lean_ctor_get(v___x_1090_, 1);
v_functionSymbolSet_1093_ = lean_ctor_get(v___x_1090_, 2);
v_unusedRelevantHypotheses_1094_ = lean_ctor_get(v___x_1090_, 3);
v_derivedEquations_1095_ = lean_ctor_get(v___x_1090_, 4);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1097_ = v___x_1090_;
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_derivedEquations_1095_);
lean_inc(v_unusedRelevantHypotheses_1094_);
lean_inc(v_functionSymbolSet_1093_);
lean_inc(v_functionSymbols_1092_);
lean_inc(v_uninterpretedSymbols_1091_);
lean_dec(v___x_1090_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1099_ = lean_box(0);
lean_inc_ref(v_e_1085_);
v___x_1100_ = lean_array_push(v_functionSymbols_1092_, v_e_1085_);
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1088_, v___x_1089_, v_functionSymbolSet_1093_, v_e_1085_, v___x_1099_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 2, v___x_1101_);
lean_ctor_set(v___x_1097_, 1, v___x_1100_);
v___x_1103_ = v___x_1097_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_uninterpretedSymbols_1091_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_unusedRelevantHypotheses_1094_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_derivedEquations_1095_);
v___x_1103_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_st_ref_put(v_a_1086_, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1099_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg___boxed(lean_object* v_e_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___redArg(v_e_1108_, v_a_1109_);
lean_dec(v_a_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol(lean_object* v_e_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_uninterpretedSymbols_1123_; lean_object* v_functionSymbols_1124_; lean_object* v_functionSymbolSet_1125_; lean_object* v_unusedRelevantHypotheses_1126_; lean_object* v_derivedEquations_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1139_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1122_ = lean_st_ref_take(v_a_1114_);
v_uninterpretedSymbols_1123_ = lean_ctor_get(v___x_1122_, 0);
v_functionSymbols_1124_ = lean_ctor_get(v___x_1122_, 1);
v_functionSymbolSet_1125_ = lean_ctor_get(v___x_1122_, 2);
v_unusedRelevantHypotheses_1126_ = lean_ctor_get(v___x_1122_, 3);
v_derivedEquations_1127_ = lean_ctor_get(v___x_1122_, 4);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1129_ = v___x_1122_;
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_derivedEquations_1127_);
lean_inc(v_unusedRelevantHypotheses_1126_);
lean_inc(v_functionSymbolSet_1125_);
lean_inc(v_functionSymbols_1124_);
lean_inc(v_uninterpretedSymbols_1123_);
lean_dec(v___x_1122_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1131_ = lean_box(0);
lean_inc_ref(v_e_1112_);
v___x_1132_ = lean_array_push(v_functionSymbols_1124_, v_e_1112_);
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1120_, v___x_1121_, v_functionSymbolSet_1125_, v_e_1112_, v___x_1131_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 2, v___x_1133_);
lean_ctor_set(v___x_1129_, 1, v___x_1132_);
v___x_1135_ = v___x_1129_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_uninterpretedSymbols_1123_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_unusedRelevantHypotheses_1126_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_derivedEquations_1127_);
v___x_1135_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_st_ref_put(v_a_1114_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1131_);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol___boxed(lean_object* v_e_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addFunctionSymbol(v_e_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg(lean_object* v_e_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_functionSymbolSet_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1154_ = lean_st_ref_get(v_a_1150_);
v_functionSymbolSet_1155_ = lean_ctor_get(v___x_1154_, 2);
lean_inc_ref(v_functionSymbolSet_1155_);
lean_dec(v___x_1154_);
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1152_, v___x_1153_, v_functionSymbolSet_1155_, v_e_1149_);
lean_dec_ref(v_functionSymbolSet_1155_);
v___x_1157_ = lean_box(v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg___boxed(lean_object* v_e_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___redArg(v_e_1159_, v_a_1160_);
lean_dec(v_a_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol(lean_object* v_e_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_functionSymbolSet_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0));
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1));
v___x_1173_ = lean_st_ref_get(v_a_1165_);
v_functionSymbolSet_1174_ = lean_ctor_get(v___x_1173_, 2);
lean_inc_ref(v_functionSymbolSet_1174_);
lean_dec(v___x_1173_);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1171_, v___x_1172_, v_functionSymbolSet_1174_, v_e_1163_);
lean_dec_ref(v_functionSymbolSet_1174_);
v___x_1176_ = lean_box(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol___boxed(lean_object* v_e_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_isFunctionSymbol(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object* v_hyp_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v_uninterpretedSymbols_1195_; lean_object* v_functionSymbols_1196_; lean_object* v_functionSymbolSet_1197_; lean_object* v_unusedRelevantHypotheses_1198_; lean_object* v_derivedEquations_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1210_; 
v___f_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1194_ = lean_st_ref_take(v_a_1190_);
v_uninterpretedSymbols_1195_ = lean_ctor_get(v___x_1194_, 0);
v_functionSymbols_1196_ = lean_ctor_get(v___x_1194_, 1);
v_functionSymbolSet_1197_ = lean_ctor_get(v___x_1194_, 2);
v_unusedRelevantHypotheses_1198_ = lean_ctor_get(v___x_1194_, 3);
v_derivedEquations_1199_ = lean_ctor_get(v___x_1194_, 4);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1201_ = v___x_1194_;
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_derivedEquations_1199_);
lean_inc(v_unusedRelevantHypotheses_1198_);
lean_inc(v_functionSymbolSet_1197_);
lean_inc(v_functionSymbols_1196_);
lean_inc(v_uninterpretedSymbols_1195_);
lean_dec(v___x_1194_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1192_, v___f_1193_, v_unusedRelevantHypotheses_1198_, v_hyp_1189_, v___x_1203_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 3, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_uninterpretedSymbols_1195_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_functionSymbols_1196_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_functionSymbolSet_1197_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_derivedEquations_1199_);
v___x_1206_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_st_ref_put(v_a_1190_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1203_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object* v_hyp_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_hyp_1211_, v_a_1212_);
lean_dec(v_a_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(lean_object* v_hyp_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v_uninterpretedSymbols_1226_; lean_object* v_functionSymbols_1227_; lean_object* v_functionSymbolSet_1228_; lean_object* v_unusedRelevantHypotheses_1229_; lean_object* v_derivedEquations_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1241_; 
v___f_1223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0));
v___f_1224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1));
v___x_1225_ = lean_st_ref_take(v_a_1217_);
v_uninterpretedSymbols_1226_ = lean_ctor_get(v___x_1225_, 0);
v_functionSymbols_1227_ = lean_ctor_get(v___x_1225_, 1);
v_functionSymbolSet_1228_ = lean_ctor_get(v___x_1225_, 2);
v_unusedRelevantHypotheses_1229_ = lean_ctor_get(v___x_1225_, 3);
v_derivedEquations_1230_ = lean_ctor_get(v___x_1225_, 4);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1232_ = v___x_1225_;
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_derivedEquations_1230_);
lean_inc(v_unusedRelevantHypotheses_1229_);
lean_inc(v_functionSymbolSet_1228_);
lean_inc(v_functionSymbols_1227_);
lean_inc(v_uninterpretedSymbols_1226_);
lean_dec(v___x_1225_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1223_, v___f_1224_, v_unusedRelevantHypotheses_1229_, v_hyp_1215_, v___x_1234_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v___x_1235_);
v___x_1237_ = v___x_1232_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_uninterpretedSymbols_1226_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_functionSymbols_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_functionSymbolSet_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_derivedEquations_1230_);
v___x_1237_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_st_ref_put(v_a_1217_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1234_);
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object* v_hyp_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_hyp_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(lean_object* v_var_1251_, lean_object* v_value_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v_uninterpretedSymbols_1256_; lean_object* v_functionSymbols_1257_; lean_object* v_functionSymbolSet_1258_; lean_object* v_unusedRelevantHypotheses_1259_; lean_object* v_derivedEquations_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1272_; 
v___x_1255_ = lean_st_ref_take(v_a_1253_);
v_uninterpretedSymbols_1256_ = lean_ctor_get(v___x_1255_, 0);
v_functionSymbols_1257_ = lean_ctor_get(v___x_1255_, 1);
v_functionSymbolSet_1258_ = lean_ctor_get(v___x_1255_, 2);
v_unusedRelevantHypotheses_1259_ = lean_ctor_get(v___x_1255_, 3);
v_derivedEquations_1260_ = lean_ctor_get(v___x_1255_, 4);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1262_ = v___x_1255_;
v_isShared_1263_ = v_isSharedCheck_1272_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_derivedEquations_1260_);
lean_inc(v_unusedRelevantHypotheses_1259_);
lean_inc(v_functionSymbolSet_1258_);
lean_inc(v_functionSymbols_1257_);
lean_inc(v_uninterpretedSymbols_1256_);
lean_dec(v___x_1255_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1272_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_var_1251_);
lean_ctor_set(v___x_1265_, 1, v_value_1252_);
v___x_1266_ = lean_array_push(v_derivedEquations_1260_, v___x_1265_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v___x_1266_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_uninterpretedSymbols_1256_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_functionSymbols_1257_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_functionSymbolSet_1258_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_unusedRelevantHypotheses_1259_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_st_ref_put(v_a_1253_, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1264_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object* v_var_1273_, lean_object* v_value_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_1273_, v_value_1274_, v_a_1275_);
lean_dec(v_a_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(lean_object* v_var_1278_, lean_object* v_value_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_uninterpretedSymbols_1288_; lean_object* v_functionSymbols_1289_; lean_object* v_functionSymbolSet_1290_; lean_object* v_unusedRelevantHypotheses_1291_; lean_object* v_derivedEquations_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1304_; 
v___x_1287_ = lean_st_ref_take(v_a_1281_);
v_uninterpretedSymbols_1288_ = lean_ctor_get(v___x_1287_, 0);
v_functionSymbols_1289_ = lean_ctor_get(v___x_1287_, 1);
v_functionSymbolSet_1290_ = lean_ctor_get(v___x_1287_, 2);
v_unusedRelevantHypotheses_1291_ = lean_ctor_get(v___x_1287_, 3);
v_derivedEquations_1292_ = lean_ctor_get(v___x_1287_, 4);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1294_ = v___x_1287_;
v_isShared_1295_ = v_isSharedCheck_1304_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_derivedEquations_1292_);
lean_inc(v_unusedRelevantHypotheses_1291_);
lean_inc(v_functionSymbolSet_1290_);
lean_inc(v_functionSymbols_1289_);
lean_inc(v_uninterpretedSymbols_1288_);
lean_dec(v___x_1287_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1304_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_var_1278_);
lean_ctor_set(v___x_1297_, 1, v_value_1279_);
v___x_1298_ = lean_array_push(v_derivedEquations_1292_, v___x_1297_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 4, v___x_1298_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_uninterpretedSymbols_1288_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_functionSymbols_1289_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_functionSymbolSet_1290_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_unusedRelevantHypotheses_1291_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_st_ref_put(v_a_1281_, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1296_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(lean_object* v_var_1305_, lean_object* v_value_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_1305_, v_value_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1314_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(lean_object* v_a_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 0)
{
uint8_t v___x_1317_; 
v___x_1317_ = 0;
return v___x_1317_;
}
else
{
lean_object* v_key_1318_; lean_object* v_tail_1319_; lean_object* v_type_1320_; lean_object* v_type_1321_; uint8_t v___x_1322_; 
v_key_1318_ = lean_ctor_get(v_x_1316_, 0);
v_tail_1319_ = lean_ctor_get(v_x_1316_, 2);
v_type_1320_ = lean_ctor_get(v_key_1318_, 1);
v_type_1321_ = lean_ctor_get(v_a_1315_, 1);
v___x_1322_ = lean_expr_eqv(v_type_1320_, v_type_1321_);
if (v___x_1322_ == 0)
{
v_x_1316_ = v_tail_1319_;
goto _start;
}
else
{
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(lean_object* v_a_1324_, lean_object* v_x_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1324_, v_x_1325_);
lean_dec(v_x_1325_);
lean_dec_ref(v_a_1324_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
return v_x_1328_;
}
else
{
lean_object* v_key_1330_; lean_object* v_value_1331_; lean_object* v_tail_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1356_; 
v_key_1330_ = lean_ctor_get(v_x_1329_, 0);
v_value_1331_ = lean_ctor_get(v_x_1329_, 1);
v_tail_1332_ = lean_ctor_get(v_x_1329_, 2);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_x_1329_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1334_ = v_x_1329_;
v_isShared_1335_ = v_isSharedCheck_1356_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_tail_1332_);
lean_inc(v_value_1331_);
lean_inc(v_key_1330_);
lean_dec(v_x_1329_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1356_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_type_1336_; lean_object* v___x_1337_; uint64_t v___x_1338_; uint64_t v___x_1339_; uint64_t v___x_1340_; uint64_t v_fold_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v_type_1336_ = lean_ctor_get(v_key_1330_, 1);
v___x_1337_ = lean_array_get_size(v_x_1328_);
v___x_1338_ = l_Lean_Expr_hash(v_type_1336_);
v___x_1339_ = 32ULL;
v___x_1340_ = lean_uint64_shift_right(v___x_1338_, v___x_1339_);
v_fold_1341_ = lean_uint64_xor(v___x_1338_, v___x_1340_);
v___x_1342_ = 16ULL;
v___x_1343_ = lean_uint64_shift_right(v_fold_1341_, v___x_1342_);
v___x_1344_ = lean_uint64_xor(v_fold_1341_, v___x_1343_);
v___x_1345_ = lean_uint64_to_usize(v___x_1344_);
v___x_1346_ = lean_usize_of_nat(v___x_1337_);
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_sub(v___x_1346_, v___x_1347_);
v___x_1349_ = lean_usize_land(v___x_1345_, v___x_1348_);
v___x_1350_ = lean_array_uget_borrowed(v_x_1328_, v___x_1349_);
lean_inc(v___x_1350_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 2, v___x_1350_);
v___x_1352_ = v___x_1334_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_key_1330_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_value_1331_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_array_uset(v_x_1328_, v___x_1349_, v___x_1352_);
v_x_1328_ = v___x_1353_;
v_x_1329_ = v_tail_1332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1357_, lean_object* v_source_1358_, lean_object* v_target_1359_){
_start:
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_array_get_size(v_source_1358_);
v___x_1361_ = lean_nat_dec_lt(v_i_1357_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v_source_1358_);
lean_dec(v_i_1357_);
return v_target_1359_;
}
else
{
lean_object* v_es_1362_; lean_object* v___x_1363_; lean_object* v_source_1364_; lean_object* v_target_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_es_1362_ = lean_array_fget(v_source_1358_, v_i_1357_);
v___x_1363_ = lean_box(0);
v_source_1364_ = lean_array_fset(v_source_1358_, v_i_1357_, v___x_1363_);
v_target_1365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_target_1359_, v_es_1362_);
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_i_1357_, v___x_1366_);
lean_dec(v_i_1357_);
v_i_1357_ = v___x_1367_;
v_source_1358_ = v_source_1364_;
v_target_1359_ = v_target_1365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(lean_object* v_data_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_nbuckets_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1370_ = lean_array_get_size(v_data_1369_);
v___x_1371_ = lean_unsigned_to_nat(2u);
v_nbuckets_1372_ = lean_nat_mul(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_mk_array(v_nbuckets_1372_, v___x_1374_);
v___x_1376_ = lean_array_propagate_mark(v_data_1369_, v___x_1375_);
v___x_1377_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v___x_1373_, v_data_1369_, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object* v_m_1378_, lean_object* v_a_1379_, lean_object* v_b_1380_){
_start:
{
lean_object* v_size_1381_; lean_object* v_buckets_1382_; lean_object* v_type_1383_; lean_object* v___x_1384_; uint64_t v___x_1385_; uint64_t v___x_1386_; uint64_t v___x_1387_; uint64_t v_fold_1388_; uint64_t v___x_1389_; uint64_t v___x_1390_; uint64_t v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; size_t v___x_1396_; lean_object* v_bkt_1397_; uint8_t v___x_1398_; 
v_size_1381_ = lean_ctor_get(v_m_1378_, 0);
v_buckets_1382_ = lean_ctor_get(v_m_1378_, 1);
v_type_1383_ = lean_ctor_get(v_a_1379_, 1);
v___x_1384_ = lean_array_get_size(v_buckets_1382_);
v___x_1385_ = l_Lean_Expr_hash(v_type_1383_);
v___x_1386_ = 32ULL;
v___x_1387_ = lean_uint64_shift_right(v___x_1385_, v___x_1386_);
v_fold_1388_ = lean_uint64_xor(v___x_1385_, v___x_1387_);
v___x_1389_ = 16ULL;
v___x_1390_ = lean_uint64_shift_right(v_fold_1388_, v___x_1389_);
v___x_1391_ = lean_uint64_xor(v_fold_1388_, v___x_1390_);
v___x_1392_ = lean_uint64_to_usize(v___x_1391_);
v___x_1393_ = lean_usize_of_nat(v___x_1384_);
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_sub(v___x_1393_, v___x_1394_);
v___x_1396_ = lean_usize_land(v___x_1392_, v___x_1395_);
v_bkt_1397_ = lean_array_uget_borrowed(v_buckets_1382_, v___x_1396_);
v___x_1398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1379_, v_bkt_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1419_; 
lean_inc_ref(v_buckets_1382_);
lean_inc(v_size_1381_);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_m_1378_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; lean_object* v_unused_1421_; 
v_unused_1420_ = lean_ctor_get(v_m_1378_, 1);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_m_1378_, 0);
lean_dec(v_unused_1421_);
v___x_1400_ = v_m_1378_;
v_isShared_1401_ = v_isSharedCheck_1419_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_m_1378_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1419_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v_size_x27_1403_; lean_object* v___x_1404_; lean_object* v_buckets_x27_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1402_ = lean_unsigned_to_nat(1u);
v_size_x27_1403_ = lean_nat_add(v_size_1381_, v___x_1402_);
lean_dec(v_size_1381_);
lean_inc(v_bkt_1397_);
v___x_1404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1404_, 0, v_a_1379_);
lean_ctor_set(v___x_1404_, 1, v_b_1380_);
lean_ctor_set(v___x_1404_, 2, v_bkt_1397_);
v_buckets_x27_1405_ = lean_array_uset(v_buckets_1382_, v___x_1396_, v___x_1404_);
v___x_1406_ = lean_unsigned_to_nat(4u);
v___x_1407_ = lean_nat_mul(v_size_x27_1403_, v___x_1406_);
v___x_1408_ = lean_unsigned_to_nat(3u);
v___x_1409_ = lean_nat_div(v___x_1407_, v___x_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_array_get_size(v_buckets_x27_1405_);
v___x_1411_ = lean_nat_dec_le(v___x_1409_, v___x_1410_);
lean_dec(v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v_val_1412_; lean_object* v___x_1414_; 
v_val_1412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_buckets_x27_1405_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_val_1412_);
lean_ctor_set(v___x_1400_, 0, v_size_x27_1403_);
v___x_1414_ = v___x_1400_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_size_x27_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_val_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
lean_object* v___x_1417_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_buckets_x27_1405_);
lean_ctor_set(v___x_1400_, 0, v_size_x27_1403_);
v___x_1417_ = v___x_1400_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_size_x27_1403_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_buckets_x27_1405_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_dec(v_b_1380_);
lean_dec_ref(v_a_1379_);
return v_m_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(lean_object* v_fvar_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v___y_1425_){
_start:
{
if (lean_obj_tag(v_a_1423_) == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_a_1424_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
else
{
lean_object* v_key_1429_; lean_object* v_tail_1430_; lean_object* v_type_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_key_1429_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_key_1429_);
v_tail_1430_ = lean_ctor_get(v_a_1423_, 2);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_a_1423_, 3);
v_type_1431_ = lean_ctor_get(v_key_1429_, 1);
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Lean_Expr_containsFVar(v_type_1431_, v_fvar_1422_);
if (v___x_1433_ == 0)
{
lean_dec(v_key_1429_);
v_a_1423_ = v_tail_1430_;
v_a_1424_ = v___x_1432_;
goto _start;
}
else
{
lean_object* v___x_1435_; lean_object* v_uninterpretedSymbols_1436_; lean_object* v_functionSymbols_1437_; lean_object* v_functionSymbolSet_1438_; lean_object* v_unusedRelevantHypotheses_1439_; lean_object* v_derivedEquations_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1450_; 
v___x_1435_ = lean_st_ref_take(v___y_1425_);
v_uninterpretedSymbols_1436_ = lean_ctor_get(v___x_1435_, 0);
v_functionSymbols_1437_ = lean_ctor_get(v___x_1435_, 1);
v_functionSymbolSet_1438_ = lean_ctor_get(v___x_1435_, 2);
v_unusedRelevantHypotheses_1439_ = lean_ctor_get(v___x_1435_, 3);
v_derivedEquations_1440_ = lean_ctor_get(v___x_1435_, 4);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1442_ = v___x_1435_;
v_isShared_1443_ = v_isSharedCheck_1450_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_derivedEquations_1440_);
lean_inc(v_unusedRelevantHypotheses_1439_);
lean_inc(v_functionSymbolSet_1438_);
lean_inc(v_functionSymbols_1437_);
lean_inc(v_uninterpretedSymbols_1436_);
lean_dec(v___x_1435_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1450_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_unusedRelevantHypotheses_1439_, v_key_1429_, v___x_1432_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 3, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_uninterpretedSymbols_1436_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_functionSymbols_1437_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_functionSymbolSet_1438_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_derivedEquations_1440_);
v___x_1446_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_st_ref_put(v___y_1425_, v___x_1446_);
v_a_1423_ = v_tail_1430_;
v_a_1424_ = v___x_1432_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(lean_object* v_fvar_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1451_, v_a_1452_, v_a_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec(v_fvar_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(lean_object* v_fvar_1457_, lean_object* v_as_1458_, size_t v_sz_1459_, size_t v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_lt(v_i_1460_, v_sz_1459_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1461_);
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_array_uget_borrowed(v_as_1458_, v_i_1460_);
lean_inc(v_a_1471_);
v___x_1472_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1457_, v_a_1471_, v_b_1461_, v___y_1463_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1485_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1485_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1485_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
if (lean_obj_tag(v_a_1473_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v_a_1473_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v_a_1473_, 1);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_a_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v_a_1481_; size_t v___x_1482_; size_t v___x_1483_; 
lean_del_object(v___x_1475_);
v_a_1481_ = lean_ctor_get(v_a_1473_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v_a_1473_, 1);
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_add(v_i_1460_, v___x_1482_);
v_i_1460_ = v___x_1483_;
v_b_1461_ = v_a_1481_;
goto _start;
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1472_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1472_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(lean_object* v_fvar_1494_, lean_object* v_as_1495_, lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
size_t v_sz_boxed_1506_; size_t v_i_boxed_1507_; lean_object* v_res_1508_; 
v_sz_boxed_1506_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1507_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1494_, v_as_1495_, v_sz_boxed_1506_, v_i_boxed_1507_, v_b_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v_as_1495_);
lean_dec(v_fvar_1494_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(lean_object* v_fvar_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_unusedHypotheses_1517_; lean_object* v_buckets_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v_unusedHypotheses_1517_ = lean_ctor_get(v_a_1510_, 1);
v_buckets_1518_ = lean_ctor_get(v_unusedHypotheses_1517_, 1);
v___x_1519_ = lean_box(0);
v_sz_1520_ = lean_array_size(v_buckets_1518_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_1509_, v_buckets_1518_, v_sz_1520_, v___x_1521_, v___x_1519_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1522_, 0);
lean_dec(v_unused_1530_);
v___x_1524_ = v___x_1522_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_dec(v___x_1522_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1519_);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1519_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
else
{
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object* v_fvar_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_fvar_1531_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object* v_00_u03b2_1540_, lean_object* v_m_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_1541_, v_a_1542_, v_b_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object* v_fvar_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_1545_, v_a_1546_, v_a_1547_, v___y_1549_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object* v_fvar_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_fvar_1556_, v_a_1557_, v_a_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v_fvar_1556_);
return v_res_1566_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(lean_object* v_00_u03b2_1567_, lean_object* v_a_1568_, lean_object* v_x_1569_){
_start:
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_1568_, v_x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1571_, lean_object* v_a_1572_, lean_object* v_x_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(v_00_u03b2_1571_, v_a_1572_, v_x_1573_);
lean_dec(v_x_1573_);
lean_dec_ref(v_a_1572_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1(lean_object* v_00_u03b2_1576_, lean_object* v_data_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_data_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1579_, lean_object* v_i_1580_, lean_object* v_source_1581_, lean_object* v_target_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v_i_1580_, v_source_1581_, v_target_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_x_1585_, v_x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_instMonadEIO___redArg();
return v___x_1588_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = l_Lean_instInhabitedExpr;
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(lean_object* v_msg_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_toApplicative_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1668_; 
v___x_1603_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0);
v___x_1604_ = l_StateRefT_x27_instMonad___redArg(v___x_1603_);
v_toApplicative_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1604_, 1);
lean_dec(v_unused_1669_);
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1668_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_toApplicative_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1668_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_toFunctor_1609_; lean_object* v_toSeq_1610_; lean_object* v_toSeqLeft_1611_; lean_object* v_toSeqRight_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1666_; 
v_toFunctor_1609_ = lean_ctor_get(v_toApplicative_1605_, 0);
v_toSeq_1610_ = lean_ctor_get(v_toApplicative_1605_, 2);
v_toSeqLeft_1611_ = lean_ctor_get(v_toApplicative_1605_, 3);
v_toSeqRight_1612_ = lean_ctor_get(v_toApplicative_1605_, 4);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_toApplicative_1605_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v_toApplicative_1605_, 1);
lean_dec(v_unused_1667_);
v___x_1614_ = v_toApplicative_1605_;
v_isShared_1615_ = v_isSharedCheck_1666_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_toSeqRight_1612_);
lean_inc(v_toSeqLeft_1611_);
lean_inc(v_toSeq_1610_);
lean_inc(v_toFunctor_1609_);
lean_dec(v_toApplicative_1605_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1666_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___f_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___x_1625_; 
v___f_1616_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1));
v___f_1617_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1609_);
v___f_1618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1618_, 0, v_toFunctor_1609_);
v___f_1619_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1619_, 0, v_toFunctor_1609_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___f_1618_);
lean_ctor_set(v___x_1620_, 1, v___f_1619_);
v___f_1621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1621_, 0, v_toSeqRight_1612_);
v___f_1622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1622_, 0, v_toSeqLeft_1611_);
v___f_1623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1623_, 0, v_toSeq_1610_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 4, v___f_1621_);
lean_ctor_set(v___x_1614_, 3, v___f_1622_);
lean_ctor_set(v___x_1614_, 2, v___f_1623_);
lean_ctor_set(v___x_1614_, 1, v___f_1616_);
lean_ctor_set(v___x_1614_, 0, v___x_1620_);
v___x_1625_ = v___x_1614_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___f_1616_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v___f_1623_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v___f_1622_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___f_1621_);
v___x_1625_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 1, v___f_1617_);
lean_ctor_set(v___x_1607_, 0, v___x_1625_);
v___x_1627_ = v___x_1607_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___f_1617_);
v___x_1627_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v_toApplicative_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1662_; 
v___x_1628_ = l_StateRefT_x27_instMonad___redArg(v___x_1627_);
v_toApplicative_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1628_, 1);
lean_dec(v_unused_1663_);
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1662_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_toApplicative_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1662_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_toFunctor_1633_; lean_object* v_toSeq_1634_; lean_object* v_toSeqLeft_1635_; lean_object* v_toSeqRight_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1660_; 
v_toFunctor_1633_ = lean_ctor_get(v_toApplicative_1629_, 0);
v_toSeq_1634_ = lean_ctor_get(v_toApplicative_1629_, 2);
v_toSeqLeft_1635_ = lean_ctor_get(v_toApplicative_1629_, 3);
v_toSeqRight_1636_ = lean_ctor_get(v_toApplicative_1629_, 4);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_toApplicative_1629_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_toApplicative_1629_, 1);
lean_dec(v_unused_1661_);
v___x_1638_ = v_toApplicative_1629_;
v_isShared_1639_ = v_isSharedCheck_1660_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_toSeqRight_1636_);
lean_inc(v_toSeqLeft_1635_);
lean_inc(v_toSeq_1634_);
lean_inc(v_toFunctor_1633_);
lean_dec(v_toApplicative_1629_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1660_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___f_1643_; lean_object* v___x_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___x_1649_; 
v___f_1640_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3));
v___f_1641_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1633_);
v___f_1642_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1642_, 0, v_toFunctor_1633_);
v___f_1643_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1643_, 0, v_toFunctor_1633_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___f_1642_);
lean_ctor_set(v___x_1644_, 1, v___f_1643_);
v___f_1645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1645_, 0, v_toSeqRight_1636_);
v___f_1646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1646_, 0, v_toSeqLeft_1635_);
v___f_1647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1647_, 0, v_toSeq_1634_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v___f_1645_);
lean_ctor_set(v___x_1638_, 3, v___f_1646_);
lean_ctor_set(v___x_1638_, 2, v___f_1647_);
lean_ctor_set(v___x_1638_, 1, v___f_1640_);
lean_ctor_set(v___x_1638_, 0, v___x_1644_);
v___x_1649_ = v___x_1638_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___f_1640_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v___f_1647_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v___f_1646_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v___f_1645_);
v___x_1649_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___f_1641_);
lean_ctor_set(v___x_1631_, 0, v___x_1649_);
v___x_1651_ = v___x_1631_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___f_1641_);
v___x_1651_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___x_12394__overap_1656_; lean_object* v___x_1657_; 
v___x_1652_ = l_StateRefT_x27_instMonad___redArg(v___x_1651_);
v___x_1653_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5);
v___x_1654_ = l_instInhabitedOfMonad___redArg(v___x_1652_, v___x_1653_);
v___f_1655_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1655_, 0, v___x_1654_);
v___x_12394__overap_1656_ = lean_panic_fn_borrowed(v___f_1655_, v_msg_1595_);
lean_dec_ref(v___f_1655_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
lean_inc_ref(v___y_1598_);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1596_);
v___x_1657_ = lean_apply_7(v___x_12394__overap_1656_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, lean_box(0));
return v___x_1657_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(lean_object* v_msg_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(lean_object* v_msgData_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v_env_1686_; uint8_t v___x_1687_; lean_object* v_env_1688_; lean_object* v___x_1689_; lean_object* v_toCold_1690_; lean_object* v_mctx_1691_; lean_object* v_lctx_1692_; lean_object* v_options_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1685_ = lean_st_ref_get(v___y_1683_);
v_env_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_ref(v_env_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = 0;
v_env_1688_ = l_Lean_Environment_setRecordingDeps(v_env_1686_, v___x_1687_);
v___x_1689_ = lean_st_ref_get(v___y_1681_);
v_toCold_1690_ = lean_ctor_get(v___y_1682_, 0);
v_mctx_1691_ = lean_ctor_get(v___x_1689_, 0);
lean_inc_ref(v_mctx_1691_);
lean_dec(v___x_1689_);
v_lctx_1692_ = lean_ctor_get(v___y_1680_, 2);
v_options_1693_ = lean_ctor_get(v_toCold_1690_, 2);
lean_inc_ref(v_options_1693_);
lean_inc_ref(v_lctx_1692_);
v___x_1694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1694_, 0, v_env_1688_);
lean_ctor_set(v___x_1694_, 1, v_mctx_1691_);
lean_ctor_set(v___x_1694_, 2, v_lctx_1692_);
lean_ctor_set(v___x_1694_, 3, v_options_1693_);
v___x_1695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_msgData_1679_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(lean_object* v_msgData_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(lean_object* v_msg_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_ref_1710_; lean_object* v___x_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_ref_1710_ = lean_ctor_get(v___y_1707_, 2);
v___x_1711_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msg_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_inc(v_ref_1710_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_ref_1710_);
lean_ctor_set(v___x_1716_, 1, v_a_1712_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(lean_object* v_msg_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1728_, lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_toCold_1737_; lean_object* v_currRecDepth_1738_; lean_object* v_ref_1739_; uint16_t v_optionFlags_1740_; uint8_t v_suppressElabErrors_1741_; uint8_t v_isRecordingDeps_1742_; lean_object* v_ref_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_toCold_1737_ = lean_ctor_get(v___y_1734_, 0);
v_currRecDepth_1738_ = lean_ctor_get(v___y_1734_, 1);
v_ref_1739_ = lean_ctor_get(v___y_1734_, 2);
v_optionFlags_1740_ = lean_ctor_get_uint16(v___y_1734_, sizeof(void*)*3);
v_suppressElabErrors_1741_ = lean_ctor_get_uint8(v___y_1734_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1742_ = lean_ctor_get_uint8(v___y_1734_, sizeof(void*)*3 + 3);
v_ref_1743_ = l_Lean_replaceRef(v_ref_1728_, v_ref_1739_);
lean_inc(v_currRecDepth_1738_);
lean_inc_ref(v_toCold_1737_);
v___x_1744_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1744_, 0, v_toCold_1737_);
lean_ctor_set(v___x_1744_, 1, v_currRecDepth_1738_);
lean_ctor_set(v___x_1744_, 2, v_ref_1743_);
lean_ctor_set_uint16(v___x_1744_, sizeof(void*)*3, v_optionFlags_1740_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*3 + 2, v_suppressElabErrors_1741_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*3 + 3, v_isRecordingDeps_1742_);
v___x_1745_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_1729_, v___y_1732_, v___y_1733_, v___x_1744_, v___y_1735_);
lean_dec_ref_known(v___x_1744_, 3);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1746_, lean_object* v_msg_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1746_, v_msg_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v_ref_1746_);
return v_res_1755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1759_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
lean_ctor_set(v___x_1762_, 2, v___x_1761_);
lean_ctor_set(v___x_1762_, 3, v___x_1761_);
lean_ctor_set(v___x_1762_, 4, v___x_1760_);
lean_ctor_set(v___x_1762_, 5, v___x_1760_);
lean_ctor_set(v___x_1762_, 6, v___x_1760_);
lean_ctor_set(v___x_1762_, 7, v___x_1760_);
lean_ctor_set(v___x_1762_, 8, v___x_1760_);
lean_ctor_set(v___x_1762_, 9, v___x_1760_);
lean_ctor_set(v___x_1762_, 10, v___x_1760_);
lean_ctor_set(v___x_1762_, 11, v___x_1759_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_unsigned_to_nat(32u);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1766_ = ((size_t)5ULL);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_unsigned_to_nat(32u);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___x_1768_);
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1771_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
lean_ctor_set(v___x_1771_, 2, v___x_1767_);
lean_ctor_set(v___x_1771_, 3, v___x_1767_);
lean_ctor_set_usize(v___x_1771_, 4, v___x_1766_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = lean_box(1);
v___x_1773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_1774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v___x_1773_);
lean_ctor_set(v___x_1775_, 2, v___x_1772_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1797_, lean_object* v_declHint_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_env_1803_; uint8_t v___x_1804_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_st_ref_get(v___y_1799_);
v_env_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc_ref(v_env_1803_);
lean_dec(v___x_1802_);
v___x_1804_ = l_Lean_Name_isAnonymous(v_declHint_1798_);
if (v___x_1804_ == 0)
{
uint8_t v_isExporting_1805_; 
v_isExporting_1805_ = lean_ctor_get_uint8(v_env_1803_, sizeof(void*)*13);
if (v_isExporting_1805_ == 0)
{
lean_object* v___x_1806_; 
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1798_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_msg_1797_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_inc_ref(v_env_1803_);
v___x_1807_ = l_Lean_Environment_setExporting(v_env_1803_, v___x_1804_);
lean_inc(v_declHint_1798_);
lean_inc_ref(v___x_1807_);
v___x_1808_ = l_Lean_Environment_contains(v___x_1807_, v_declHint_1798_, v_isExporting_1805_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1798_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_msg_1797_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_c_1815_; lean_object* v___x_1816_; 
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1812_ = l_Lean_Options_empty;
v___x_1813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1810_);
lean_ctor_set(v___x_1813_, 2, v___x_1811_);
lean_ctor_set(v___x_1813_, 3, v___x_1812_);
lean_inc(v_declHint_1798_);
v___x_1814_ = l_Lean_MessageData_ofConstName(v_declHint_1798_, v___x_1804_);
v_c_1815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1815_, 0, v___x_1813_);
lean_ctor_set(v_c_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1803_, v_declHint_1798_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1798_);
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_c_1815_);
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_MessageData_note(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_msg_1797_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1858_; 
v_val_1824_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1826_ = v___x_1816_;
v_isShared_1827_ = v_isSharedCheck_1858_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_val_1824_);
lean_dec(v___x_1816_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1858_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_mod_1830_; uint8_t v___x_1831_; 
v___x_1828_ = l_Lean_Environment_header(v_env_1803_);
lean_dec_ref(v_env_1803_);
v___x_1829_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1828_);
v_mod_1830_ = lean_array_get(v___x_1801_, v___x_1829_, v_val_1824_);
lean_dec(v_val_1824_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = l_Lean_isPrivateName(v_declHint_1798_);
lean_dec(v_declHint_1798_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_c_1815_);
v___x_1834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_MessageData_ofName(v_mod_1830_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_MessageData_note(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_msg_1797_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1841_);
v___x_1843_ = v___x_1826_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_c_1815_);
v___x_1847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_MessageData_ofName(v_mod_1830_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_MessageData_note(v___x_1852_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_msg_1797_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1854_);
v___x_1856_ = v___x_1826_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1859_; 
lean_dec_ref(v_env_1803_);
lean_dec(v_declHint_1798_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_msg_1797_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1860_, lean_object* v_declHint_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1860_, v_declHint_1861_, v___y_1862_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_1865_, lean_object* v_declHint_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1884_; 
v___x_1874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1865_, v_declHint_1866_, v___y_1872_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = l_Lean_unknownIdentifierMessageTag;
v___x_1880_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v_a_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_1885_, lean_object* v_declHint_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1885_, v_declHint_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_1895_, lean_object* v_msg_1896_, lean_object* v_declHint_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v_a_1906_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1896_, v_declHint_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1895_, v_a_1906_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1908_, lean_object* v_msg_1909_, lean_object* v_declHint_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1908_, v_msg_1909_, v_declHint_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v_ref_1908_);
return v_res_1918_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1921_ = l_Lean_stringToMessageData(v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1924_ = l_Lean_stringToMessageData(v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1925_, lean_object* v_constName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1934_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1935_ = 0;
lean_inc(v_constName_1926_);
v___x_1936_ = l_Lean_MessageData_ofConstName(v_constName_1926_, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1934_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1925_, v___x_1939_, v_constName_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1941_, lean_object* v_constName_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1941_, v_constName_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_ref_1941_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object* v_constName_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_ref_1959_; lean_object* v___x_1960_; 
v_ref_1959_ = lean_ctor_get(v___y_1956_, 2);
v___x_1960_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_1959_, v_constName_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(lean_object* v_constName_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v_env_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_st_ref_get(v___y_1976_);
v_env_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc_ref(v_env_1979_);
lean_dec(v___x_1978_);
v___x_1980_ = 0;
lean_inc(v_constName_1970_);
v___x_1981_ = l_Lean_Environment_find_x3f(v_env_1979_, v_constName_1970_, v___x_1980_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1982_;
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_constName_1970_);
v_val_1983_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 0);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_val_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object* v_constName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2));
v___x_2007_ = l_Lean_Expr_const___override(v___x_2006_, v___x_2005_);
return v___x_2007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5));
v___x_2011_ = lean_unsigned_to_nat(61u);
v___x_2012_ = lean_unsigned_to_nat(243u);
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4));
v___x_2014_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0));
v___x_2015_ = l_mkPanicMessageWithDecl(v___x_2014_, v___x_2013_, v___x_2012_, v___x_2011_, v___x_2010_);
return v___x_2015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34));
v___x_2071_ = l_Lean_stringToMessageData(v___x_2070_);
return v___x_2071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36));
v___x_2074_ = l_Lean_stringToMessageData(v___x_2073_);
return v___x_2074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = l_Lean_Level_ofNat(v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
v___x_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39));
v___x_2086_ = l_Lean_Expr_const___override(v___x_2085_, v___x_2084_);
return v___x_2086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43));
v___x_2091_ = l_Lean_mkConst(v___x_2090_, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46));
v___x_2098_ = l_Lean_Expr_const___override(v___x_2097_, v___x_2096_);
return v___x_2098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
static size_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52(void){
_start:
{
lean_object* v___x_2105_; size_t v___x_2106_; 
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_isize_of_nat(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55));
v___x_2114_ = l_Lean_Expr_const___override(v___x_2113_, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_box(0);
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57));
v___x_2119_ = l_Lean_Expr_const___override(v___x_2118_, v___x_2117_);
return v___x_2119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_box(0);
v___x_2125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60));
v___x_2126_ = l_Lean_Expr_const___override(v___x_2125_, v___x_2124_);
return v___x_2126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62));
v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
return v___x_2129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66));
v___x_2137_ = l_Lean_mkConst(v___x_2136_, v___x_2135_);
return v___x_2137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69));
v___x_2144_ = l_Lean_mkConst(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73));
v___x_2152_ = l_Lean_mkConst(v___x_2151_, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_box(0);
v___x_2157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75));
v___x_2158_ = l_Lean_Expr_const___override(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77));
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_box(0);
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79));
v___x_2166_ = l_Lean_mkConst(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_box(0);
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81));
v___x_2172_ = l_Lean_Expr_const___override(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85));
v___x_2180_ = l_Lean_mkConst(v___x_2179_, v___x_2178_);
return v___x_2180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_box(0);
v___x_2185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87));
v___x_2186_ = l_Lean_Expr_const___override(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91));
v___x_2194_ = l_Lean_mkConst(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93));
v___x_2200_ = l_Lean_Expr_const___override(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97(void){
_start:
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_int8_of_nat(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__98));
v___x_2210_ = l_Lean_Expr_const___override(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__100));
v___x_2216_ = l_Lean_Expr_const___override(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__102));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static uint16_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104(void){
_start:
{
lean_object* v___x_2220_; uint16_t v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_int16_of_nat(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__105));
v___x_2226_ = l_Lean_Expr_const___override(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__107));
v___x_2232_ = l_Lean_Expr_const___override(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__109));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static uint32_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111(void){
_start:
{
lean_object* v___x_2236_; uint32_t v___x_2237_; 
v___x_2236_ = lean_unsigned_to_nat(0u);
v___x_2237_ = lean_int32_of_nat(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_box(0);
v___x_2241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__112));
v___x_2242_ = l_Lean_Expr_const___override(v___x_2241_, v___x_2240_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__114));
v___x_2248_ = l_Lean_Expr_const___override(v___x_2247_, v___x_2246_);
return v___x_2248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__116));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118(void){
_start:
{
lean_object* v___x_2252_; uint64_t v___x_2253_; 
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_int64_of_nat(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_box(0);
v___x_2257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__119));
v___x_2258_ = l_Lean_Expr_const___override(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_box(0);
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__121));
v___x_2264_ = l_Lean_Expr_const___override(v___x_2263_, v___x_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object* v_var_2265_, lean_object* v_value_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = l_Lean_Expr_isFVar(v_var_2265_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___x_2352_; 
v___x_2290_ = lean_box(0);
lean_inc_ref(v_var_2265_);
v___x_2352_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_2265_, v_a_2270_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2801_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2801_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2801_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = l_Lean_Expr_cleanupAnnotations(v_a_2353_);
v___x_2358_ = l_Lean_Expr_isApp(v___x_2357_);
if (v___x_2358_ == 0)
{
lean_dec_ref(v___x_2357_);
lean_del_object(v___x_2355_);
v___y_2292_ = v_a_2267_;
v___y_2293_ = v_a_2268_;
v___y_2294_ = v_a_2269_;
v___y_2295_ = v_a_2270_;
v___y_2296_ = v_a_2271_;
v___y_2297_ = v_a_2272_;
goto v___jp_2291_;
}
else
{
lean_object* v_arg_2359_; lean_object* v___y_2361_; lean_object* v___y_2367_; lean_object* v___y_2371_; lean_object* v___y_2375_; lean_object* v___y_2379_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_arg_2359_ = lean_ctor_get(v___x_2357_, 1);
lean_inc_ref(v_arg_2359_);
v___x_2382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2357_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9));
v___x_2384_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; uint8_t v___x_2386_; 
lean_del_object(v___x_2355_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11));
v___x_2386_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13));
v___x_2388_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15));
v___x_2390_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17));
v___x_2392_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19));
v___x_2394_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21));
v___x_2396_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23));
v___x_2398_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25));
v___x_2400_ = l_Lean_Expr_isConstOf(v___x_2382_, v___x_2399_);
if (v___x_2400_ == 0)
{
uint8_t v___x_2401_; 
lean_dec_ref(v_arg_2359_);
v___x_2401_ = l_Lean_Expr_isApp(v___x_2382_);
if (v___x_2401_ == 0)
{
lean_dec_ref(v___x_2382_);
v___y_2292_ = v_a_2267_;
v___y_2293_ = v_a_2268_;
v___y_2294_ = v_a_2269_;
v___y_2295_ = v_a_2270_;
v___y_2296_ = v_a_2271_;
v___y_2297_ = v_a_2272_;
goto v___jp_2291_;
}
else
{
lean_object* v_arg_2402_; lean_object* v___y_2404_; lean_object* v___y_2408_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_arg_2402_ = lean_ctor_get(v___x_2382_, 1);
lean_inc_ref(v_arg_2402_);
v___x_2411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2382_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28));
v___x_2413_ = l_Lean_Expr_isConstOf(v___x_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30));
v___x_2415_ = l_Lean_Expr_isConstOf(v___x_2411_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32));
v___x_2417_ = l_Lean_Expr_isConstOf(v___x_2411_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33));
v___x_2419_ = l_Lean_Expr_isConstOf(v___x_2411_, v___x_2418_);
lean_dec_ref(v___x_2411_);
if (v___x_2419_ == 0)
{
lean_dec_ref(v_arg_2402_);
v___y_2292_ = v_a_2267_;
v___y_2293_ = v_a_2268_;
v___y_2294_ = v_a_2269_;
v___y_2295_ = v_a_2270_;
v___y_2296_ = v_a_2271_;
v___y_2297_ = v_a_2272_;
goto v___jp_2291_;
}
else
{
lean_object* v_w_2420_; lean_object* v_bv_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v_var_2265_);
v_w_2420_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2421_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2423_ = v_value_2266_;
v_isShared_2424_ = v_isSharedCheck_2449_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_bv_2421_);
lean_inc(v_w_2420_);
lean_dec(v_value_2266_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2449_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(32u);
v___x_2426_ = lean_nat_dec_eq(v_w_2420_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
lean_dec(v_bv_2421_);
lean_dec_ref(v_arg_2402_);
v___x_2427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35);
v___x_2428_ = l_Nat_reprFast(v_w_2420_);
v___x_2429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
v___x_2430_ = l_Lean_MessageData_ofFormat(v___x_2429_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 7);
lean_ctor_set(v___x_2423_, 1, v___x_2430_);
lean_ctor_set(v___x_2423_, 0, v___x_2427_);
v___x_2432_ = v___x_2423_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2434_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2435_;
}
}
else
{
size_t v___x_2437_; lean_object* v___x_2438_; lean_object* v_r_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec(v_w_2420_);
v___x_2437_ = lean_usize_of_nat(v_bv_2421_);
lean_dec(v_bv_2421_);
v___x_2438_ = lean_usize_to_nat(v___x_2437_);
v_r_2439_ = l_Lean_mkRawNatLit(v___x_2438_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2439_);
v___x_2443_ = l_Lean_Expr_app___override(v___x_2442_, v_r_2439_);
v___x_2444_ = l_Lean_mkApp3(v___x_2440_, v___x_2441_, v_r_2439_, v___x_2443_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v___x_2444_);
lean_ctor_set(v___x_2423_, 0, v_arg_2402_);
v___x_2446_ = v___x_2423_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_arg_2402_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
}
}
}
else
{
lean_object* v_w_2450_; lean_object* v_bv_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v___x_2411_);
lean_dec_ref(v_var_2265_);
v_w_2450_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2451_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2453_ = v_value_2266_;
v_isShared_2454_ = v_isSharedCheck_2479_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_bv_2451_);
lean_inc(v_w_2450_);
lean_dec(v_value_2266_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2479_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2455_ = lean_unsigned_to_nat(64u);
v___x_2456_ = lean_nat_dec_eq(v_w_2450_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_dec(v_bv_2451_);
lean_dec_ref(v_arg_2402_);
v___x_2457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49);
v___x_2458_ = l_Nat_reprFast(v_w_2450_);
v___x_2459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
v___x_2460_ = l_Lean_MessageData_ofFormat(v___x_2459_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 7);
lean_ctor_set(v___x_2453_, 1, v___x_2460_);
lean_ctor_set(v___x_2453_, 0, v___x_2457_);
v___x_2462_ = v___x_2453_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2464_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2465_;
}
}
else
{
size_t v___x_2467_; lean_object* v___x_2468_; lean_object* v_r_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_dec(v_w_2450_);
v___x_2467_ = lean_usize_of_nat(v_bv_2451_);
lean_dec(v_bv_2451_);
v___x_2468_ = lean_usize_to_nat(v___x_2467_);
v_r_2469_ = l_Lean_mkRawNatLit(v___x_2468_);
v___x_2470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44);
v___x_2472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47);
lean_inc_ref(v_r_2469_);
v___x_2473_ = l_Lean_Expr_app___override(v___x_2472_, v_r_2469_);
v___x_2474_ = l_Lean_mkApp3(v___x_2470_, v___x_2471_, v_r_2469_, v___x_2473_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v___x_2474_);
lean_ctor_set(v___x_2453_, 0, v_arg_2402_);
v___x_2476_ = v___x_2453_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_arg_2402_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v_w_2480_; lean_object* v_bv_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v___x_2411_);
lean_dec_ref(v_var_2265_);
v_w_2480_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2481_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2483_ = v_value_2266_;
v_isShared_2484_ = v_isSharedCheck_2512_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_bv_2481_);
lean_inc(v_w_2480_);
lean_dec(v_value_2266_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2512_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = lean_unsigned_to_nat(32u);
v___x_2486_ = lean_nat_dec_eq(v_w_2480_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_dec(v_bv_2481_);
lean_dec_ref(v_arg_2402_);
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51);
v___x_2488_ = l_Nat_reprFast(v_w_2480_);
v___x_2489_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
v___x_2490_ = l_Lean_MessageData_ofFormat(v___x_2489_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 7);
lean_ctor_set(v___x_2483_, 1, v___x_2490_);
lean_ctor_set(v___x_2483_, 0, v___x_2487_);
v___x_2492_ = v___x_2483_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2494_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2495_;
}
}
else
{
lean_object* v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; uint8_t v___x_2500_; 
lean_del_object(v___x_2483_);
v___x_2497_ = l_BitVec_toInt(v_w_2480_, v_bv_2481_);
lean_dec(v_w_2480_);
v___x_2498_ = lean_isize_of_int(v___x_2497_);
lean_dec(v___x_2497_);
v___x_2499_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2500_ = lean_isize_dec_le(v___x_2499_, v___x_2498_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2504_ = lean_isize_to_int(v___x_2498_);
v___x_2505_ = lean_int_neg(v___x_2504_);
lean_dec(v___x_2504_);
v___x_2506_ = l_Int_toNat(v___x_2505_);
lean_dec(v___x_2505_);
v___x_2507_ = l_Lean_instToExprISize_mkNat(v___x_2506_);
v___x_2508_ = l_Lean_mkApp3(v___x_2501_, v___x_2502_, v___x_2503_, v___x_2507_);
v___y_2408_ = v___x_2508_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_isize_to_int(v___x_2498_);
v___x_2510_ = l_Int_toNat(v___x_2509_);
lean_dec(v___x_2509_);
v___x_2511_ = l_Lean_instToExprISize_mkNat(v___x_2510_);
v___y_2408_ = v___x_2511_;
goto v___jp_2407_;
}
}
}
}
}
else
{
lean_object* v_w_2513_; lean_object* v_bv_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v___x_2411_);
lean_dec_ref(v_var_2265_);
v_w_2513_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2514_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2516_ = v_value_2266_;
v_isShared_2517_ = v_isSharedCheck_2545_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_bv_2514_);
lean_inc(v_w_2513_);
lean_dec(v_value_2266_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2545_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = lean_unsigned_to_nat(64u);
v___x_2519_ = lean_nat_dec_eq(v_w_2513_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_dec(v_bv_2514_);
lean_dec_ref(v_arg_2402_);
v___x_2520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63);
v___x_2521_ = l_Nat_reprFast(v_w_2513_);
v___x_2522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
v___x_2523_ = l_Lean_MessageData_ofFormat(v___x_2522_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 7);
lean_ctor_set(v___x_2516_, 1, v___x_2523_);
lean_ctor_set(v___x_2516_, 0, v___x_2520_);
v___x_2525_ = v___x_2516_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2527_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2528_;
}
}
else
{
lean_object* v___x_2530_; size_t v___x_2531_; size_t v___x_2532_; uint8_t v___x_2533_; 
lean_del_object(v___x_2516_);
v___x_2530_ = l_BitVec_toInt(v_w_2513_, v_bv_2514_);
lean_dec(v_w_2513_);
v___x_2531_ = lean_isize_of_int(v___x_2530_);
lean_dec(v___x_2530_);
v___x_2532_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
v___x_2533_ = lean_isize_dec_le(v___x_2532_, v___x_2531_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
v___x_2536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61);
v___x_2537_ = lean_isize_to_int(v___x_2531_);
v___x_2538_ = lean_int_neg(v___x_2537_);
lean_dec(v___x_2537_);
v___x_2539_ = l_Int_toNat(v___x_2538_);
lean_dec(v___x_2538_);
v___x_2540_ = l_Lean_instToExprISize_mkNat(v___x_2539_);
v___x_2541_ = l_Lean_mkApp3(v___x_2534_, v___x_2535_, v___x_2536_, v___x_2540_);
v___y_2404_ = v___x_2541_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_isize_to_int(v___x_2531_);
v___x_2543_ = l_Int_toNat(v___x_2542_);
lean_dec(v___x_2542_);
v___x_2544_ = l_Lean_instToExprISize_mkNat(v___x_2543_);
v___y_2404_ = v___x_2544_;
goto v___jp_2403_;
}
}
}
}
v___jp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_arg_2402_);
lean_ctor_set(v___x_2405_, 1, v___y_2404_);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_arg_2402_);
lean_ctor_set(v___x_2409_, 1, v___y_2408_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
}
else
{
lean_object* v_w_2546_; lean_object* v_bv_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2546_ = lean_ctor_get(v_value_2266_, 0);
lean_inc(v_w_2546_);
v_bv_2547_ = lean_ctor_get(v_value_2266_, 1);
lean_inc(v_bv_2547_);
lean_dec_ref(v_value_2266_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = l_BitVec_ofNat(v_w_2546_, v___x_2548_);
lean_dec(v_w_2546_);
v___x_2550_ = lean_nat_dec_eq(v_bv_2547_, v___x_2549_);
lean_dec(v___x_2549_);
lean_dec(v_bv_2547_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67);
v___y_2379_ = v___x_2551_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70);
v___y_2379_ = v___x_2552_;
goto v___jp_2378_;
}
}
}
else
{
lean_object* v_w_2553_; lean_object* v_bv_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2553_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2554_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2556_ = v_value_2266_;
v_isShared_2557_ = v_isSharedCheck_2582_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_bv_2554_);
lean_inc(v_w_2553_);
lean_dec(v_value_2266_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2582_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_unsigned_to_nat(8u);
v___x_2559_ = lean_nat_dec_eq(v_w_2553_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_dec(v_bv_2554_);
lean_dec_ref(v_arg_2359_);
v___x_2560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72);
v___x_2561_ = l_Nat_reprFast(v_w_2553_);
v___x_2562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
v___x_2563_ = l_Lean_MessageData_ofFormat(v___x_2562_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set_tag(v___x_2556_, 7);
lean_ctor_set(v___x_2556_, 1, v___x_2563_);
lean_ctor_set(v___x_2556_, 0, v___x_2560_);
v___x_2565_ = v___x_2556_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2567_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2568_;
}
}
else
{
uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v_r_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_w_2553_);
v___x_2570_ = lean_uint8_of_nat_mk(v_bv_2554_);
v___x_2571_ = lean_uint8_to_nat(v___x_2570_);
v_r_2572_ = l_Lean_mkRawNatLit(v___x_2571_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74);
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76);
lean_inc_ref(v_r_2572_);
v___x_2576_ = l_Lean_Expr_app___override(v___x_2575_, v_r_2572_);
v___x_2577_ = l_Lean_mkApp3(v___x_2573_, v___x_2574_, v_r_2572_, v___x_2576_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v___x_2577_);
lean_ctor_set(v___x_2556_, 0, v_arg_2359_);
v___x_2579_ = v___x_2556_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_arg_2359_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
return v___x_2580_;
}
}
}
}
}
else
{
lean_object* v_w_2583_; lean_object* v_bv_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2583_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2584_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2586_ = v_value_2266_;
v_isShared_2587_ = v_isSharedCheck_2612_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_bv_2584_);
lean_inc(v_w_2583_);
lean_dec(v_value_2266_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2612_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_unsigned_to_nat(16u);
v___x_2589_ = lean_nat_dec_eq(v_w_2583_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_bv_2584_);
lean_dec_ref(v_arg_2359_);
v___x_2590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78);
v___x_2591_ = l_Nat_reprFast(v_w_2583_);
v___x_2592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v___x_2593_ = l_Lean_MessageData_ofFormat(v___x_2592_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set_tag(v___x_2586_, 7);
lean_ctor_set(v___x_2586_, 1, v___x_2593_);
lean_ctor_set(v___x_2586_, 0, v___x_2590_);
v___x_2595_ = v___x_2586_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2597_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2598_;
}
}
else
{
uint16_t v___x_2600_; lean_object* v___x_2601_; lean_object* v_r_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec(v_w_2583_);
v___x_2600_ = lean_uint16_of_nat_mk(v_bv_2584_);
v___x_2601_ = lean_uint16_to_nat(v___x_2600_);
v_r_2602_ = l_Lean_mkRawNatLit(v___x_2601_);
v___x_2603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80);
v___x_2605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82);
lean_inc_ref(v_r_2602_);
v___x_2606_ = l_Lean_Expr_app___override(v___x_2605_, v_r_2602_);
v___x_2607_ = l_Lean_mkApp3(v___x_2603_, v___x_2604_, v_r_2602_, v___x_2606_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 1, v___x_2607_);
lean_ctor_set(v___x_2586_, 0, v_arg_2359_);
v___x_2609_ = v___x_2586_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_arg_2359_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_w_2613_; lean_object* v_bv_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2613_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2614_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2616_ = v_value_2266_;
v_isShared_2617_ = v_isSharedCheck_2642_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_bv_2614_);
lean_inc(v_w_2613_);
lean_dec(v_value_2266_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2642_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = lean_unsigned_to_nat(32u);
v___x_2619_ = lean_nat_dec_eq(v_w_2613_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_dec(v_bv_2614_);
lean_dec_ref(v_arg_2359_);
v___x_2620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84);
v___x_2621_ = l_Nat_reprFast(v_w_2613_);
v___x_2622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
v___x_2623_ = l_Lean_MessageData_ofFormat(v___x_2622_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 7);
lean_ctor_set(v___x_2616_, 1, v___x_2623_);
lean_ctor_set(v___x_2616_, 0, v___x_2620_);
v___x_2625_ = v___x_2616_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2627_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2628_;
}
}
else
{
uint32_t v___x_2630_; lean_object* v___x_2631_; lean_object* v_r_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec(v_w_2613_);
v___x_2630_ = lean_uint32_of_nat_mk(v_bv_2614_);
v___x_2631_ = lean_uint32_to_nat(v___x_2630_);
v_r_2632_ = l_Lean_mkRawNatLit(v___x_2631_);
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86);
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88);
lean_inc_ref(v_r_2632_);
v___x_2636_ = l_Lean_Expr_app___override(v___x_2635_, v_r_2632_);
v___x_2637_ = l_Lean_mkApp3(v___x_2633_, v___x_2634_, v_r_2632_, v___x_2636_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v___x_2637_);
lean_ctor_set(v___x_2616_, 0, v_arg_2359_);
v___x_2639_ = v___x_2616_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_arg_2359_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
}
}
}
else
{
lean_object* v_w_2643_; lean_object* v_bv_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2672_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2643_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2644_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2646_ = v_value_2266_;
v_isShared_2647_ = v_isSharedCheck_2672_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_bv_2644_);
lean_inc(v_w_2643_);
lean_dec(v_value_2266_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2672_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = lean_unsigned_to_nat(64u);
v___x_2649_ = lean_nat_dec_eq(v_w_2643_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_dec(v_bv_2644_);
lean_dec_ref(v_arg_2359_);
v___x_2650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90);
v___x_2651_ = l_Nat_reprFast(v_w_2643_);
v___x_2652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
v___x_2653_ = l_Lean_MessageData_ofFormat(v___x_2652_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 7);
lean_ctor_set(v___x_2646_, 1, v___x_2653_);
lean_ctor_set(v___x_2646_, 0, v___x_2650_);
v___x_2655_ = v___x_2646_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2657_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2658_;
}
}
else
{
uint64_t v___x_2660_; lean_object* v___x_2661_; lean_object* v_r_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_dec(v_w_2643_);
v___x_2660_ = lean_uint64_of_nat_mk(v_bv_2644_);
v___x_2661_ = lean_uint64_to_nat(v___x_2660_);
v_r_2662_ = l_Lean_mkRawNatLit(v___x_2661_);
v___x_2663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42);
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92);
v___x_2665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94);
lean_inc_ref(v_r_2662_);
v___x_2666_ = l_Lean_Expr_app___override(v___x_2665_, v_r_2662_);
v___x_2667_ = l_Lean_mkApp3(v___x_2663_, v___x_2664_, v_r_2662_, v___x_2666_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2667_);
lean_ctor_set(v___x_2646_, 0, v_arg_2359_);
v___x_2669_ = v___x_2646_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_arg_2359_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
}
}
}
}
else
{
lean_object* v_w_2673_; lean_object* v_bv_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2673_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2674_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2676_ = v_value_2266_;
v_isShared_2677_ = v_isSharedCheck_2704_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_bv_2674_);
lean_inc(v_w_2673_);
lean_dec(v_value_2266_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2704_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = lean_unsigned_to_nat(8u);
v___x_2679_ = lean_nat_dec_eq(v_w_2673_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
lean_dec(v_bv_2674_);
lean_dec_ref(v_arg_2359_);
v___x_2680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96);
v___x_2681_ = l_Nat_reprFast(v_w_2673_);
v___x_2682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
v___x_2683_ = l_Lean_MessageData_ofFormat(v___x_2682_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 7);
lean_ctor_set(v___x_2676_, 1, v___x_2683_);
lean_ctor_set(v___x_2676_, 0, v___x_2680_);
v___x_2685_ = v___x_2676_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2687_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2688_;
}
}
else
{
uint8_t v___x_2690_; uint8_t v___x_2691_; uint8_t v___x_2692_; 
lean_del_object(v___x_2676_);
lean_dec(v_w_2673_);
v___x_2690_ = lean_uint8_of_nat_mk(v_bv_2674_);
v___x_2691_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97);
v___x_2692_ = lean_int8_dec_le(v___x_2691_, v___x_2690_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__99);
v___x_2695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__101);
v___x_2696_ = lean_int8_to_int(v___x_2690_);
v___x_2697_ = lean_int_neg(v___x_2696_);
v___x_2698_ = l_Int_toNat(v___x_2697_);
lean_dec(v___x_2697_);
v___x_2699_ = l_Lean_instToExprInt8_mkNat(v___x_2698_);
v___x_2700_ = l_Lean_mkApp3(v___x_2693_, v___x_2694_, v___x_2695_, v___x_2699_);
v___y_2375_ = v___x_2700_;
goto v___jp_2374_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_int8_to_int(v___x_2690_);
v___x_2702_ = l_Int_toNat(v___x_2701_);
v___x_2703_ = l_Lean_instToExprInt8_mkNat(v___x_2702_);
v___y_2375_ = v___x_2703_;
goto v___jp_2374_;
}
}
}
}
}
else
{
lean_object* v_w_2705_; lean_object* v_bv_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2705_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2706_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2708_ = v_value_2266_;
v_isShared_2709_ = v_isSharedCheck_2736_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_bv_2706_);
lean_inc(v_w_2705_);
lean_dec(v_value_2266_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2736_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = lean_unsigned_to_nat(16u);
v___x_2711_ = lean_nat_dec_eq(v_w_2705_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
lean_dec(v_bv_2706_);
lean_dec_ref(v_arg_2359_);
v___x_2712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__103);
v___x_2713_ = l_Nat_reprFast(v_w_2705_);
v___x_2714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
v___x_2715_ = l_Lean_MessageData_ofFormat(v___x_2714_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 7);
lean_ctor_set(v___x_2708_, 1, v___x_2715_);
lean_ctor_set(v___x_2708_, 0, v___x_2712_);
v___x_2717_ = v___x_2708_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2719_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2720_;
}
}
else
{
uint16_t v___x_2722_; uint16_t v___x_2723_; uint8_t v___x_2724_; 
lean_del_object(v___x_2708_);
lean_dec(v_w_2705_);
v___x_2722_ = lean_uint16_of_nat_mk(v_bv_2706_);
v___x_2723_ = lean_uint16_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__104);
v___x_2724_ = lean_int16_dec_le(v___x_2723_, v___x_2722_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__106);
v___x_2727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__108);
v___x_2728_ = lean_int16_to_int(v___x_2722_);
v___x_2729_ = lean_int_neg(v___x_2728_);
v___x_2730_ = l_Int_toNat(v___x_2729_);
lean_dec(v___x_2729_);
v___x_2731_ = l_Lean_instToExprInt16_mkNat(v___x_2730_);
v___x_2732_ = l_Lean_mkApp3(v___x_2725_, v___x_2726_, v___x_2727_, v___x_2731_);
v___y_2371_ = v___x_2732_;
goto v___jp_2370_;
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_int16_to_int(v___x_2722_);
v___x_2734_ = l_Int_toNat(v___x_2733_);
v___x_2735_ = l_Lean_instToExprInt16_mkNat(v___x_2734_);
v___y_2371_ = v___x_2735_;
goto v___jp_2370_;
}
}
}
}
}
else
{
lean_object* v_w_2737_; lean_object* v_bv_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2737_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2738_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2740_ = v_value_2266_;
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_bv_2738_);
lean_inc(v_w_2737_);
lean_dec(v_value_2266_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_unsigned_to_nat(32u);
v___x_2743_ = lean_nat_dec_eq(v_w_2737_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_dec(v_bv_2738_);
lean_dec_ref(v_arg_2359_);
v___x_2744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__110);
v___x_2745_ = l_Nat_reprFast(v_w_2737_);
v___x_2746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
v___x_2747_ = l_Lean_MessageData_ofFormat(v___x_2746_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 7);
lean_ctor_set(v___x_2740_, 1, v___x_2747_);
lean_ctor_set(v___x_2740_, 0, v___x_2744_);
v___x_2749_ = v___x_2740_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2751_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2752_;
}
}
else
{
uint32_t v___x_2754_; uint32_t v___x_2755_; uint8_t v___x_2756_; 
lean_del_object(v___x_2740_);
lean_dec(v_w_2737_);
v___x_2754_ = lean_uint32_of_nat_mk(v_bv_2738_);
v___x_2755_ = lean_uint32_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__111);
v___x_2756_ = lean_int32_dec_le(v___x_2755_, v___x_2754_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__113);
v___x_2759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__115);
v___x_2760_ = lean_int32_to_int(v___x_2754_);
v___x_2761_ = lean_int_neg(v___x_2760_);
lean_dec(v___x_2760_);
v___x_2762_ = l_Int_toNat(v___x_2761_);
lean_dec(v___x_2761_);
v___x_2763_ = l_Lean_instToExprInt32_mkNat(v___x_2762_);
v___x_2764_ = l_Lean_mkApp3(v___x_2757_, v___x_2758_, v___x_2759_, v___x_2763_);
v___y_2367_ = v___x_2764_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_int32_to_int(v___x_2754_);
v___x_2766_ = l_Int_toNat(v___x_2765_);
lean_dec(v___x_2765_);
v___x_2767_ = l_Lean_instToExprInt32_mkNat(v___x_2766_);
v___y_2367_ = v___x_2767_;
goto v___jp_2366_;
}
}
}
}
}
else
{
lean_object* v_w_2769_; lean_object* v_bv_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2800_; 
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_var_2265_);
v_w_2769_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2770_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2772_ = v_value_2266_;
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_bv_2770_);
lean_inc(v_w_2769_);
lean_dec(v_value_2266_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = lean_unsigned_to_nat(64u);
v___x_2775_ = lean_nat_dec_eq(v_w_2769_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec(v_bv_2770_);
lean_dec_ref(v_arg_2359_);
lean_del_object(v___x_2355_);
v___x_2776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__117);
v___x_2777_ = l_Nat_reprFast(v_w_2769_);
v___x_2778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
v___x_2779_ = l_Lean_MessageData_ofFormat(v___x_2778_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 7);
lean_ctor_set(v___x_2772_, 1, v___x_2779_);
lean_ctor_set(v___x_2772_, 0, v___x_2776_);
v___x_2781_ = v___x_2772_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_2783_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2784_;
}
}
else
{
uint64_t v___x_2786_; uint64_t v___x_2787_; uint8_t v___x_2788_; 
lean_del_object(v___x_2772_);
lean_dec(v_w_2769_);
v___x_2786_ = lean_uint64_of_nat_mk(v_bv_2770_);
v___x_2787_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__118);
v___x_2788_ = lean_int64_dec_le(v___x_2787_, v___x_2786_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
v___x_2790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__120);
v___x_2791_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__122);
v___x_2792_ = lean_int64_to_int_sint(v___x_2786_);
v___x_2793_ = lean_int_neg(v___x_2792_);
lean_dec(v___x_2792_);
v___x_2794_ = l_Int_toNat(v___x_2793_);
lean_dec(v___x_2793_);
v___x_2795_ = l_Lean_instToExprInt64_mkNat(v___x_2794_);
v___x_2796_ = l_Lean_mkApp3(v___x_2789_, v___x_2790_, v___x_2791_, v___x_2795_);
v___y_2361_ = v___x_2796_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_int64_to_int_sint(v___x_2786_);
v___x_2798_ = l_Int_toNat(v___x_2797_);
lean_dec(v___x_2797_);
v___x_2799_ = l_Lean_instToExprInt64_mkNat(v___x_2798_);
v___y_2361_ = v___x_2799_;
goto v___jp_2360_;
}
}
}
}
v___jp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_arg_2359_);
lean_ctor_set(v___x_2362_, 1, v___y_2361_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2362_);
v___x_2364_ = v___x_2355_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
v___jp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_arg_2359_);
lean_ctor_set(v___x_2368_, 1, v___y_2367_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
v___jp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_arg_2359_);
lean_ctor_set(v___x_2372_, 1, v___y_2371_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
v___jp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_arg_2359_);
lean_ctor_set(v___x_2376_, 1, v___y_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_inc_ref(v___y_2379_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_arg_2359_);
lean_ctor_set(v___x_2380_, 1, v___y_2379_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v_value_2266_);
lean_dec_ref(v_var_2265_);
v_a_2802_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2352_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2352_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
v___jp_2291_:
{
if (lean_obj_tag(v_var_2265_) == 5)
{
lean_object* v_fn_2298_; 
v_fn_2298_ = lean_ctor_get(v_var_2265_, 0);
if (lean_obj_tag(v_fn_2298_) == 4)
{
lean_object* v_arg_2299_; lean_object* v_declName_2300_; lean_object* v_us_2301_; lean_object* v___x_2302_; lean_object* v_env_2303_; lean_object* v___x_2304_; 
v_arg_2299_ = lean_ctor_get(v_var_2265_, 1);
v_declName_2300_ = lean_ctor_get(v_fn_2298_, 0);
v_us_2301_ = lean_ctor_get(v_fn_2298_, 1);
v___x_2302_ = lean_st_ref_get(v___y_2297_);
v_env_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc_ref(v_env_2303_);
lean_dec(v___x_2302_);
lean_inc(v_declName_2300_);
v___x_2304_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecType_x3f(v_env_2303_, v_declName_2300_);
if (lean_obj_tag(v___x_2304_) == 1)
{
lean_object* v_val_2305_; lean_object* v___x_2306_; 
lean_inc(v_us_2301_);
lean_inc_ref(v_arg_2299_);
lean_dec_ref_known(v_var_2265_, 2);
v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_val_2305_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2329_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2329_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2329_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
if (lean_obj_tag(v_a_2307_) == 5)
{
lean_object* v_val_2311_; lean_object* v_ctors_2312_; lean_object* v_bv_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2325_; 
v_val_2311_ = lean_ctor_get(v_a_2307_, 0);
lean_inc_ref(v_val_2311_);
lean_dec_ref_known(v_a_2307_, 1);
v_ctors_2312_ = lean_ctor_get(v_val_2311_, 4);
lean_inc(v_ctors_2312_);
lean_dec_ref(v_val_2311_);
v_bv_2313_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_value_2266_, 0);
lean_dec(v_unused_2326_);
v___x_2315_ = v_value_2266_;
v_isShared_2316_ = v_isSharedCheck_2325_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_bv_2313_);
lean_dec(v_value_2266_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2325_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = l_List_get_x21Internal___redArg(v___x_2290_, v_ctors_2312_, v_bv_2313_);
lean_dec(v_ctors_2312_);
v___x_2318_ = l_Lean_mkConst(v___x_2317_, v_us_2301_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2318_);
lean_ctor_set(v___x_2315_, 0, v_arg_2299_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_arg_2299_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2320_);
v___x_2322_ = v___x_2309_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_del_object(v___x_2309_);
lean_dec(v_a_2307_);
lean_dec(v_us_2301_);
lean_dec_ref(v_arg_2299_);
lean_dec_ref(v_value_2266_);
v___x_2327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6);
v___x_2328_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v___x_2327_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_us_2301_);
lean_dec_ref(v_arg_2299_);
lean_dec_ref(v_value_2266_);
v_a_2330_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2306_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2306_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_w_2338_; lean_object* v_bv_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v___x_2304_);
v_w_2338_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2339_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2341_ = v_value_2266_;
v_isShared_2342_ = v_isSharedCheck_2351_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_bv_2339_);
lean_inc(v_w_2338_);
lean_dec(v_value_2266_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2351_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2344_ = l_Lean_mkNatLit(v_w_2338_);
v___x_2345_ = l_Lean_mkNatLit(v_bv_2339_);
v___x_2346_ = l_Lean_mkAppB(v___x_2343_, v___x_2344_, v___x_2345_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2346_);
lean_ctor_set(v___x_2341_, 0, v_var_2265_);
v___x_2348_ = v___x_2341_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_var_2265_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
}
else
{
goto v___jp_2274_;
}
}
else
{
goto v___jp_2274_;
}
}
}
else
{
lean_object* v_w_2810_; lean_object* v_bv_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2823_; 
v_w_2810_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2811_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2813_ = v_value_2266_;
v_isShared_2814_ = v_isSharedCheck_2823_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_bv_2811_);
lean_inc(v_w_2810_);
lean_dec(v_value_2266_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2823_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2816_ = l_Lean_mkNatLit(v_w_2810_);
v___x_2817_ = l_Lean_mkNatLit(v_bv_2811_);
v___x_2818_ = l_Lean_mkAppB(v___x_2815_, v___x_2816_, v___x_2817_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 1, v___x_2818_);
lean_ctor_set(v___x_2813_, 0, v_var_2265_);
v___x_2820_ = v___x_2813_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_var_2265_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
return v___x_2821_;
}
}
}
v___jp_2274_:
{
lean_object* v_w_2275_; lean_object* v_bv_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2288_; 
v_w_2275_ = lean_ctor_get(v_value_2266_, 0);
v_bv_2276_ = lean_ctor_get(v_value_2266_, 1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_value_2266_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2278_ = v_value_2266_;
v_isShared_2279_ = v_isSharedCheck_2288_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_bv_2276_);
lean_inc(v_w_2275_);
lean_dec(v_value_2266_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2288_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
v___x_2281_ = l_Lean_mkNatLit(v_w_2275_);
v___x_2282_ = l_Lean_mkNatLit(v_bv_2276_);
v___x_2283_ = l_Lean_mkAppB(v___x_2280_, v___x_2281_, v___x_2282_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 1, v___x_2283_);
lean_ctor_set(v___x_2278_, 0, v_var_2265_);
v___x_2285_ = v___x_2278_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_var_2265_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object* v_var_2824_, lean_object* v_value_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_2824_, v_value_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(lean_object* v_00_u03b1_2834_, lean_object* v_msg_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_2835_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(lean_object* v_00_u03b1_2844_, lean_object* v_msg_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(v_00_u03b1_2844_, v_msg_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object* v_00_u03b1_2854_, lean_object* v_constName_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2864_, lean_object* v_constName_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(v_00_u03b1_2864_, v_constName_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2874_, lean_object* v_ref_2875_, lean_object* v_constName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_2875_, v_constName_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2885_, lean_object* v_ref_2886_, lean_object* v_constName_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(v_00_u03b1_2885_, v_ref_2886_, v_constName_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v_ref_2886_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_2896_, lean_object* v_ref_2897_, lean_object* v_msg_2898_, lean_object* v_declHint_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2897_, v_msg_2898_, v_declHint_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2908_, lean_object* v_ref_2909_, lean_object* v_msg_2910_, lean_object* v_declHint_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_2908_, v_ref_2909_, v_msg_2910_, v_declHint_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v_ref_2909_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_2920_, lean_object* v_declHint_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_2920_, v_declHint_2921_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2930_, lean_object* v_declHint_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_2930_, v_declHint_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2940_, lean_object* v_ref_2941_, lean_object* v_msg_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_2941_, v_msg_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2951_, lean_object* v_ref_2952_, lean_object* v_msg_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_2951_, v_ref_2952_, v_msg_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v_ref_2952_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_2962_, lean_object* v_x_2963_){
_start:
{
if (lean_obj_tag(v_x_2963_) == 0)
{
return v_x_2962_;
}
else
{
lean_object* v_key_2964_; lean_object* v_value_2965_; lean_object* v_tail_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2989_; 
v_key_2964_ = lean_ctor_get(v_x_2963_, 0);
v_value_2965_ = lean_ctor_get(v_x_2963_, 1);
v_tail_2966_ = lean_ctor_get(v_x_2963_, 2);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_x_2963_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2968_ = v_x_2963_;
v_isShared_2969_ = v_isSharedCheck_2989_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_tail_2966_);
lean_inc(v_value_2965_);
lean_inc(v_key_2964_);
lean_dec(v_x_2963_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2989_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; uint64_t v___x_2973_; uint64_t v_fold_2974_; uint64_t v___x_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; size_t v___x_2981_; size_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2970_ = lean_array_get_size(v_x_2962_);
v___x_2971_ = l_Lean_Expr_hash(v_key_2964_);
v___x_2972_ = 32ULL;
v___x_2973_ = lean_uint64_shift_right(v___x_2971_, v___x_2972_);
v_fold_2974_ = lean_uint64_xor(v___x_2971_, v___x_2973_);
v___x_2975_ = 16ULL;
v___x_2976_ = lean_uint64_shift_right(v_fold_2974_, v___x_2975_);
v___x_2977_ = lean_uint64_xor(v_fold_2974_, v___x_2976_);
v___x_2978_ = lean_uint64_to_usize(v___x_2977_);
v___x_2979_ = lean_usize_of_nat(v___x_2970_);
v___x_2980_ = ((size_t)1ULL);
v___x_2981_ = lean_usize_sub(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_usize_land(v___x_2978_, v___x_2981_);
v___x_2983_ = lean_array_uget_borrowed(v_x_2962_, v___x_2982_);
lean_inc(v___x_2983_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 2, v___x_2983_);
v___x_2985_ = v___x_2968_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_key_2964_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_value_2965_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_array_uset(v_x_2962_, v___x_2982_, v___x_2985_);
v_x_2962_ = v___x_2986_;
v_x_2963_ = v_tail_2966_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2990_, lean_object* v_source_2991_, lean_object* v_target_2992_){
_start:
{
lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = lean_array_get_size(v_source_2991_);
v___x_2994_ = lean_nat_dec_lt(v_i_2990_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_dec_ref(v_source_2991_);
lean_dec(v_i_2990_);
return v_target_2992_;
}
else
{
lean_object* v_es_2995_; lean_object* v___x_2996_; lean_object* v_source_2997_; lean_object* v_target_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_es_2995_ = lean_array_fget(v_source_2991_, v_i_2990_);
v___x_2996_ = lean_box(0);
v_source_2997_ = lean_array_fset(v_source_2991_, v_i_2990_, v___x_2996_);
v_target_2998_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(v_target_2992_, v_es_2995_);
v___x_2999_ = lean_unsigned_to_nat(1u);
v___x_3000_ = lean_nat_add(v_i_2990_, v___x_2999_);
lean_dec(v_i_2990_);
v_i_2990_ = v___x_3000_;
v_source_2991_ = v_source_2997_;
v_target_2992_ = v_target_2998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(lean_object* v_data_3002_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v_nbuckets_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3003_ = lean_array_get_size(v_data_3002_);
v___x_3004_ = lean_unsigned_to_nat(2u);
v_nbuckets_3005_ = lean_nat_mul(v___x_3003_, v___x_3004_);
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_mk_array(v_nbuckets_3005_, v___x_3007_);
v___x_3009_ = lean_array_propagate_mark(v_data_3002_, v___x_3008_);
v___x_3010_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v___x_3006_, v_data_3002_, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object* v_a_3011_, lean_object* v_x_3012_){
_start:
{
if (lean_obj_tag(v_x_3012_) == 0)
{
uint8_t v___x_3013_; 
v___x_3013_ = 0;
return v___x_3013_;
}
else
{
lean_object* v_key_3014_; lean_object* v_tail_3015_; uint8_t v___x_3016_; 
v_key_3014_ = lean_ctor_get(v_x_3012_, 0);
v_tail_3015_ = lean_ctor_get(v_x_3012_, 2);
v___x_3016_ = lean_expr_eqv(v_key_3014_, v_a_3011_);
if (v___x_3016_ == 0)
{
v_x_3012_ = v_tail_3015_;
goto _start;
}
else
{
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object* v_a_3018_, lean_object* v_x_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3018_, v_x_3019_);
lean_dec(v_x_3019_);
lean_dec_ref(v_a_3018_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(lean_object* v_m_3022_, lean_object* v_a_3023_, lean_object* v_b_3024_){
_start:
{
lean_object* v_size_3025_; lean_object* v_buckets_3026_; lean_object* v___x_3027_; uint64_t v___x_3028_; uint64_t v___x_3029_; uint64_t v___x_3030_; uint64_t v_fold_3031_; uint64_t v___x_3032_; uint64_t v___x_3033_; uint64_t v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; size_t v___x_3037_; size_t v___x_3038_; size_t v___x_3039_; lean_object* v_bkt_3040_; uint8_t v___x_3041_; 
v_size_3025_ = lean_ctor_get(v_m_3022_, 0);
v_buckets_3026_ = lean_ctor_get(v_m_3022_, 1);
v___x_3027_ = lean_array_get_size(v_buckets_3026_);
v___x_3028_ = l_Lean_Expr_hash(v_a_3023_);
v___x_3029_ = 32ULL;
v___x_3030_ = lean_uint64_shift_right(v___x_3028_, v___x_3029_);
v_fold_3031_ = lean_uint64_xor(v___x_3028_, v___x_3030_);
v___x_3032_ = 16ULL;
v___x_3033_ = lean_uint64_shift_right(v_fold_3031_, v___x_3032_);
v___x_3034_ = lean_uint64_xor(v_fold_3031_, v___x_3033_);
v___x_3035_ = lean_uint64_to_usize(v___x_3034_);
v___x_3036_ = lean_usize_of_nat(v___x_3027_);
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_sub(v___x_3036_, v___x_3037_);
v___x_3039_ = lean_usize_land(v___x_3035_, v___x_3038_);
v_bkt_3040_ = lean_array_uget_borrowed(v_buckets_3026_, v___x_3039_);
v___x_3041_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3023_, v_bkt_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3062_; 
lean_inc_ref(v_buckets_3026_);
lean_inc(v_size_3025_);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_m_3022_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; lean_object* v_unused_3064_; 
v_unused_3063_ = lean_ctor_get(v_m_3022_, 1);
lean_dec(v_unused_3063_);
v_unused_3064_ = lean_ctor_get(v_m_3022_, 0);
lean_dec(v_unused_3064_);
v___x_3043_ = v_m_3022_;
v_isShared_3044_ = v_isSharedCheck_3062_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v_m_3022_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3062_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v_size_x27_3046_; lean_object* v___x_3047_; lean_object* v_buckets_x27_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3045_ = lean_unsigned_to_nat(1u);
v_size_x27_3046_ = lean_nat_add(v_size_3025_, v___x_3045_);
lean_dec(v_size_3025_);
lean_inc(v_bkt_3040_);
v___x_3047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3047_, 0, v_a_3023_);
lean_ctor_set(v___x_3047_, 1, v_b_3024_);
lean_ctor_set(v___x_3047_, 2, v_bkt_3040_);
v_buckets_x27_3048_ = lean_array_uset(v_buckets_3026_, v___x_3039_, v___x_3047_);
v___x_3049_ = lean_unsigned_to_nat(4u);
v___x_3050_ = lean_nat_mul(v_size_x27_3046_, v___x_3049_);
v___x_3051_ = lean_unsigned_to_nat(3u);
v___x_3052_ = lean_nat_div(v___x_3050_, v___x_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_array_get_size(v_buckets_x27_3048_);
v___x_3054_ = lean_nat_dec_le(v___x_3052_, v___x_3053_);
lean_dec(v___x_3052_);
if (v___x_3054_ == 0)
{
lean_object* v_val_3055_; lean_object* v___x_3057_; 
v_val_3055_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_buckets_x27_3048_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v_val_3055_);
lean_ctor_set(v___x_3043_, 0, v_size_x27_3046_);
v___x_3057_ = v___x_3043_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_size_x27_3046_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_val_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
else
{
lean_object* v___x_3060_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v_buckets_x27_3048_);
lean_ctor_set(v___x_3043_, 0, v_size_x27_3046_);
v___x_3060_ = v___x_3043_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_size_x27_3046_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_buckets_x27_3048_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_dec(v_b_3024_);
lean_dec_ref(v_a_3023_);
return v_m_3022_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object* v_m_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_buckets_3067_; lean_object* v___x_3068_; uint64_t v___x_3069_; uint64_t v___x_3070_; uint64_t v___x_3071_; uint64_t v_fold_3072_; uint64_t v___x_3073_; uint64_t v___x_3074_; uint64_t v___x_3075_; size_t v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v_buckets_3067_ = lean_ctor_get(v_m_3065_, 1);
v___x_3068_ = lean_array_get_size(v_buckets_3067_);
v___x_3069_ = l_Lean_Expr_hash(v_a_3066_);
v___x_3070_ = 32ULL;
v___x_3071_ = lean_uint64_shift_right(v___x_3069_, v___x_3070_);
v_fold_3072_ = lean_uint64_xor(v___x_3069_, v___x_3071_);
v___x_3073_ = 16ULL;
v___x_3074_ = lean_uint64_shift_right(v_fold_3072_, v___x_3073_);
v___x_3075_ = lean_uint64_xor(v_fold_3072_, v___x_3074_);
v___x_3076_ = lean_uint64_to_usize(v___x_3075_);
v___x_3077_ = lean_usize_of_nat(v___x_3068_);
v___x_3078_ = ((size_t)1ULL);
v___x_3079_ = lean_usize_sub(v___x_3077_, v___x_3078_);
v___x_3080_ = lean_usize_land(v___x_3076_, v___x_3079_);
v___x_3081_ = lean_array_uget_borrowed(v_buckets_3067_, v___x_3080_);
v___x_3082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3066_, v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg___boxed(lean_object* v_m_3083_, lean_object* v_a_3084_){
_start:
{
uint8_t v_res_3085_; lean_object* v_r_3086_; 
v_res_3085_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3083_, v_a_3084_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_m_3083_);
v_r_3086_ = lean_box(v_res_3085_);
return v_r_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(lean_object* v_as_3087_, size_t v_sz_3088_, size_t v_i_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_a_3099_; uint8_t v___x_3103_; 
v___x_3103_ = lean_usize_dec_lt(v_i_3089_, v_sz_3088_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_b_3090_);
return v___x_3104_;
}
else
{
lean_object* v_a_3105_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3105_ = lean_array_uget_borrowed(v_as_3087_, v_i_3089_);
v_fst_3106_ = lean_ctor_get(v_a_3105_, 0);
v_snd_3107_ = lean_ctor_get(v_a_3105_, 1);
v___x_3108_ = lean_box(0);
lean_inc(v_snd_3107_);
lean_inc(v_fst_3106_);
v___x_3109_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_3106_, v_snd_3107_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_fst_3111_; lean_object* v___x_3112_; lean_object* v_uninterpretedSymbols_3113_; lean_object* v_functionSymbols_3114_; lean_object* v_functionSymbolSet_3115_; lean_object* v_unusedRelevantHypotheses_3116_; lean_object* v_derivedEquations_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3146_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v_fst_3111_ = lean_ctor_get(v_a_3110_, 0);
lean_inc(v_fst_3111_);
v___x_3112_ = lean_st_ref_take(v___y_3092_);
v_uninterpretedSymbols_3113_ = lean_ctor_get(v___x_3112_, 0);
v_functionSymbols_3114_ = lean_ctor_get(v___x_3112_, 1);
v_functionSymbolSet_3115_ = lean_ctor_get(v___x_3112_, 2);
v_unusedRelevantHypotheses_3116_ = lean_ctor_get(v___x_3112_, 3);
v_derivedEquations_3117_ = lean_ctor_get(v___x_3112_, 4);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3119_ = v___x_3112_;
v_isShared_3120_ = v_isSharedCheck_3146_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_derivedEquations_3117_);
lean_inc(v_unusedRelevantHypotheses_3116_);
lean_inc(v_functionSymbolSet_3115_);
lean_inc(v_functionSymbols_3114_);
lean_inc(v_uninterpretedSymbols_3113_);
lean_dec(v___x_3112_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3146_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_array_push(v_derivedEquations_3117_, v_a_3110_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 4, v___x_3121_);
v___x_3123_ = v___x_3119_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_uninterpretedSymbols_3113_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_functionSymbols_3114_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_functionSymbolSet_3115_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_unusedRelevantHypotheses_3116_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_st_ref_put(v___y_3092_, v___x_3123_);
if (lean_obj_tag(v_fst_3111_) == 1)
{
lean_object* v_fvarId_3125_; lean_object* v___x_3126_; 
v_fvarId_3125_ = lean_ctor_get(v_fst_3111_, 0);
lean_inc(v_fvarId_3125_);
lean_dec_ref_known(v_fst_3111_, 1);
v___x_3126_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvarId_3125_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v_fvarId_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_dec_ref_known(v___x_3126_, 1);
v_a_3099_ = v___x_3108_;
goto v___jp_3098_;
}
else
{
return v___x_3126_;
}
}
else
{
lean_object* v___x_3127_; lean_object* v_functionSymbolSet_3128_; uint8_t v___x_3129_; 
v___x_3127_ = lean_st_ref_get(v___y_3092_);
v_functionSymbolSet_3128_ = lean_ctor_get(v___x_3127_, 2);
lean_inc_ref(v_functionSymbolSet_3128_);
lean_dec(v___x_3127_);
v___x_3129_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_functionSymbolSet_3128_, v_fst_3111_);
lean_dec_ref(v_functionSymbolSet_3128_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v_uninterpretedSymbols_3131_; lean_object* v_functionSymbols_3132_; lean_object* v_functionSymbolSet_3133_; lean_object* v_unusedRelevantHypotheses_3134_; lean_object* v_derivedEquations_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3144_; 
v___x_3130_ = lean_st_ref_take(v___y_3092_);
v_uninterpretedSymbols_3131_ = lean_ctor_get(v___x_3130_, 0);
v_functionSymbols_3132_ = lean_ctor_get(v___x_3130_, 1);
v_functionSymbolSet_3133_ = lean_ctor_get(v___x_3130_, 2);
v_unusedRelevantHypotheses_3134_ = lean_ctor_get(v___x_3130_, 3);
v_derivedEquations_3135_ = lean_ctor_get(v___x_3130_, 4);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3137_ = v___x_3130_;
v_isShared_3138_ = v_isSharedCheck_3144_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_derivedEquations_3135_);
lean_inc(v_unusedRelevantHypotheses_3134_);
lean_inc(v_functionSymbolSet_3133_);
lean_inc(v_functionSymbols_3132_);
lean_inc(v_uninterpretedSymbols_3131_);
lean_dec(v___x_3130_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3144_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_uninterpretedSymbols_3131_, v_fst_3111_, v___x_3108_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_functionSymbols_3132_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_functionSymbolSet_3133_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_unusedRelevantHypotheses_3134_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_derivedEquations_3135_);
v___x_3141_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_st_ref_put(v___y_3092_, v___x_3141_);
v_a_3099_ = v___x_3108_;
goto v___jp_3098_;
}
}
}
else
{
lean_dec(v_fst_3111_);
v_a_3099_ = v___x_3108_;
goto v___jp_3098_;
}
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v_a_3147_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3109_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3109_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
v___jp_3098_:
{
size_t v___x_3100_; size_t v___x_3101_; 
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_i_3089_, v___x_3100_);
v_i_3089_ = v___x_3101_;
v_b_3090_ = v_a_3099_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3___boxed(lean_object* v_as_3155_, lean_object* v_sz_3156_, lean_object* v_i_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
size_t v_sz_boxed_3166_; size_t v_i_boxed_3167_; lean_object* v_res_3168_; 
v_sz_boxed_3166_ = lean_unbox_usize(v_sz_3156_);
lean_dec(v_sz_3156_);
v_i_boxed_3167_ = lean_unbox_usize(v_i_3157_);
lean_dec(v_i_3157_);
v_res_3168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_as_3155_, v_sz_boxed_3166_, v_i_boxed_3167_, v_b_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v_as_3155_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(lean_object* v_as_3169_, size_t v_sz_3170_, size_t v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_lt(v_i_3171_, v_sz_3170_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_b_3172_);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v_uninterpretedSymbols_3180_; lean_object* v_functionSymbols_3181_; lean_object* v_functionSymbolSet_3182_; lean_object* v_unusedRelevantHypotheses_3183_; lean_object* v_derivedEquations_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3197_; 
v___x_3177_ = lean_box(0);
v_a_3178_ = lean_array_uget_borrowed(v_as_3169_, v_i_3171_);
v___x_3179_ = lean_st_ref_take(v___y_3173_);
v_uninterpretedSymbols_3180_ = lean_ctor_get(v___x_3179_, 0);
v_functionSymbols_3181_ = lean_ctor_get(v___x_3179_, 1);
v_functionSymbolSet_3182_ = lean_ctor_get(v___x_3179_, 2);
v_unusedRelevantHypotheses_3183_ = lean_ctor_get(v___x_3179_, 3);
v_derivedEquations_3184_ = lean_ctor_get(v___x_3179_, 4);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3186_ = v___x_3179_;
v_isShared_3187_ = v_isSharedCheck_3197_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_derivedEquations_3184_);
lean_inc(v_unusedRelevantHypotheses_3183_);
lean_inc(v_functionSymbolSet_3182_);
lean_inc(v_functionSymbols_3181_);
lean_inc(v_uninterpretedSymbols_3180_);
lean_dec(v___x_3179_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3197_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
lean_inc_n(v_a_3178_, 2);
v___x_3188_ = lean_array_push(v_functionSymbols_3181_, v_a_3178_);
v___x_3189_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_functionSymbolSet_3182_, v_a_3178_, v___x_3177_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 2, v___x_3189_);
lean_ctor_set(v___x_3186_, 1, v___x_3188_);
v___x_3191_ = v___x_3186_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_uninterpretedSymbols_3180_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3196_, 2, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3196_, 3, v_unusedRelevantHypotheses_3183_);
lean_ctor_set(v_reuseFailAlloc_3196_, 4, v_derivedEquations_3184_);
v___x_3191_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; size_t v___x_3193_; size_t v___x_3194_; 
v___x_3192_ = lean_st_ref_put(v___y_3173_, v___x_3191_);
v___x_3193_ = ((size_t)1ULL);
v___x_3194_ = lean_usize_add(v_i_3171_, v___x_3193_);
v_i_3171_ = v___x_3194_;
v_b_3172_ = v___x_3177_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg___boxed(lean_object* v_as_3198_, lean_object* v_sz_3199_, lean_object* v_i_3200_, lean_object* v_b_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
size_t v_sz_boxed_3204_; size_t v_i_boxed_3205_; lean_object* v_res_3206_; 
v_sz_boxed_3204_ = lean_unbox_usize(v_sz_3199_);
lean_dec(v_sz_3199_);
v_i_boxed_3205_ = lean_unbox_usize(v_i_3200_);
lean_dec(v_i_3200_);
v_res_3206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3198_, v_sz_boxed_3204_, v_i_boxed_3205_, v_b_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v_as_3198_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_equations_3214_; lean_object* v_functionAtoms_3215_; lean_object* v___x_3216_; size_t v_sz_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v_equations_3214_ = lean_ctor_get(v_a_3207_, 2);
v_functionAtoms_3215_ = lean_ctor_get(v_a_3207_, 3);
v___x_3216_ = lean_box(0);
v_sz_3217_ = lean_array_size(v_functionAtoms_3215_);
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_functionAtoms_3215_, v_sz_3217_, v___x_3218_, v___x_3216_, v_a_3208_);
if (lean_obj_tag(v___x_3219_) == 0)
{
size_t v_sz_3220_; lean_object* v___x_3221_; 
lean_dec_ref_known(v___x_3219_, 1);
v_sz_3220_ = lean_array_size(v_equations_3214_);
v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_equations_3214_, v_sz_3220_, v___x_3218_, v___x_3216_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3221_, 0);
lean_dec(v_unused_3229_);
v___x_3223_ = v___x_3221_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v___x_3221_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3216_);
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3216_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
else
{
return v___x_3221_;
}
}
else
{
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
return v_res_3237_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object* v_00_u03b2_3238_, lean_object* v_m_3239_, lean_object* v_a_3240_){
_start:
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3239_, v_a_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___boxed(lean_object* v_00_u03b2_3242_, lean_object* v_m_3243_, lean_object* v_a_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(v_00_u03b2_3242_, v_m_3243_, v_a_3244_);
lean_dec_ref(v_a_3244_);
lean_dec_ref(v_m_3243_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object* v_00_u03b2_3247_, lean_object* v_m_3248_, lean_object* v_a_3249_, lean_object* v_b_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_m_3248_, v_a_3249_, v_b_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(lean_object* v_as_3252_, size_t v_sz_3253_, size_t v_i_3254_, lean_object* v_b_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3252_, v_sz_3253_, v_i_3254_, v_b_3255_, v___y_3257_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___boxed(lean_object* v_as_3264_, lean_object* v_sz_3265_, lean_object* v_i_3266_, lean_object* v_b_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
size_t v_sz_boxed_3275_; size_t v_i_boxed_3276_; lean_object* v_res_3277_; 
v_sz_boxed_3275_ = lean_unbox_usize(v_sz_3265_);
lean_dec(v_sz_3265_);
v_i_boxed_3276_ = lean_unbox_usize(v_i_3266_);
lean_dec(v_i_3266_);
v_res_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(v_as_3264_, v_sz_boxed_3275_, v_i_boxed_3276_, v_b_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_as_3264_);
return v_res_3277_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object* v_00_u03b2_3278_, lean_object* v_a_3279_, lean_object* v_x_3280_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3279_, v_x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_a_3283_, lean_object* v_x_3284_){
_start:
{
uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_res_3285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_3282_, v_a_3283_, v_x_3284_);
lean_dec(v_x_3284_);
lean_dec_ref(v_a_3283_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(lean_object* v_00_u03b2_3287_, lean_object* v_data_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_data_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3290_, lean_object* v_i_3291_, lean_object* v_source_3292_, lean_object* v_target_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v_i_3291_, v_source_3292_, v_target_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3296_, v_x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__0));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(lean_object* v_as_x27_3302_, lean_object* v_b_3303_){
_start:
{
if (lean_obj_tag(v_as_x27_3302_) == 0)
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_b_3303_);
return v___x_3304_;
}
else
{
lean_object* v_head_3305_; lean_object* v_tail_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_head_3305_ = lean_ctor_get(v_as_x27_3302_, 0);
v_tail_3306_ = lean_ctor_get(v_as_x27_3302_, 1);
v___x_3307_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1);
lean_inc(v_head_3305_);
v___x_3308_ = l_Lean_MessageData_ofExpr(v_head_3305_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_b_3303_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v_as_x27_3302_ = v_tail_3306_;
v_b_3303_ = v___x_3310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3312_, lean_object* v_b_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v_as_x27_3312_, v_b_3313_);
lean_dec(v_as_x27_3312_);
return v_res_3314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__0));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer(lean_object* v_d_3318_){
_start:
{
lean_object* v_functionSymbols_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v_functionSymbols_3319_ = lean_ctor_get(v_d_3318_, 1);
lean_inc_ref(v_functionSymbols_3319_);
lean_dec_ref(v_d_3318_);
v___x_3320_ = lean_array_get_size(v_functionSymbols_3319_);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_nat_dec_eq(v___x_3320_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_array_to_list(v_functionSymbols_3319_);
v___x_3324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1);
v___x_3325_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v___x_3323_, v___x_3324_);
lean_dec(v___x_3323_);
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; 
lean_dec_ref(v_functionSymbols_3319_);
v___x_3326_ = lean_box(0);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(lean_object* v_as_3327_, lean_object* v_as_x27_3328_, lean_object* v_b_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v_as_x27_3328_, v_b_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___boxed(lean_object* v_as_3332_, lean_object* v_as_x27_3333_, lean_object* v_b_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(v_as_3332_, v_as_x27_3333_, v_b_3334_, v_a_3335_);
lean_dec(v_as_x27_3333_);
lean_dec(v_as_3332_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object* v_x_3342_, lean_object* v_x_3343_){
_start:
{
if (lean_obj_tag(v_x_3343_) == 0)
{
lean_inc(v_x_3342_);
return v_x_3342_;
}
else
{
lean_object* v_key_3344_; lean_object* v_tail_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_key_3344_ = lean_ctor_get(v_x_3343_, 0);
v_tail_3345_ = lean_ctor_get(v_x_3343_, 2);
v___x_3346_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_x_3342_, v_tail_3345_);
lean_inc(v_key_3344_);
v___x_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_key_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object* v_x_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_x_3348_, v_x_3349_);
lean_dec(v_x_3349_);
lean_dec(v_x_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object* v_as_3351_, size_t v_i_3352_, size_t v_stop_3353_, lean_object* v_b_3354_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_usize_dec_eq(v_i_3352_, v_stop_3353_);
if (v___x_3355_ == 0)
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3356_ = ((size_t)1ULL);
v___x_3357_ = lean_usize_sub(v_i_3352_, v___x_3356_);
v___x_3358_ = lean_array_uget_borrowed(v_as_3351_, v___x_3357_);
v___x_3359_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_b_3354_, v___x_3358_);
lean_dec(v_b_3354_);
v_i_3352_ = v___x_3357_;
v_b_3354_ = v___x_3359_;
goto _start;
}
else
{
return v_b_3354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object* v_as_3361_, lean_object* v_i_3362_, lean_object* v_stop_3363_, lean_object* v_b_3364_){
_start:
{
size_t v_i_boxed_3365_; size_t v_stop_boxed_3366_; lean_object* v_res_3367_; 
v_i_boxed_3365_ = lean_unbox_usize(v_i_3362_);
lean_dec(v_i_3362_);
v_stop_boxed_3366_ = lean_unbox_usize(v_stop_3363_);
lean_dec(v_stop_3363_);
v_res_3367_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_as_3361_, v_i_boxed_3365_, v_stop_boxed_3366_, v_b_3364_);
lean_dec_ref(v_as_3361_);
return v_res_3367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object* v_d_3371_){
_start:
{
lean_object* v___y_3373_; lean_object* v_uninterpretedSymbols_3376_; lean_object* v_size_3377_; lean_object* v_buckets_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v_uninterpretedSymbols_3376_ = lean_ctor_get(v_d_3371_, 0);
v_size_3377_ = lean_ctor_get(v_uninterpretedSymbols_3376_, 0);
v_buckets_3378_ = lean_ctor_get(v_uninterpretedSymbols_3376_, 1);
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = lean_nat_dec_eq(v_size_3377_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_array_get_size(v_buckets_3378_);
v___x_3383_ = lean_nat_dec_lt(v___x_3379_, v___x_3382_);
if (v___x_3383_ == 0)
{
v___y_3373_ = v___x_3381_;
goto v___jp_3372_;
}
else
{
size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = lean_usize_of_nat(v___x_3382_);
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_buckets_3378_, v___x_3384_, v___x_3385_, v___x_3381_);
v___y_3373_ = v___x_3386_;
goto v___jp_3372_;
}
}
else
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_box(0);
return v___x_3387_;
}
v___jp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
v___x_3375_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v___y_3373_, v___x_3374_);
lean_dec(v___y_3373_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object* v_d_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_3388_);
lean_dec_ref(v_d_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object* v_x_3390_, lean_object* v_x_3391_){
_start:
{
if (lean_obj_tag(v_x_3391_) == 0)
{
lean_inc(v_x_3390_);
return v_x_3390_;
}
else
{
lean_object* v_key_3392_; lean_object* v_tail_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_key_3392_ = lean_ctor_get(v_x_3391_, 0);
v_tail_3393_ = lean_ctor_get(v_x_3391_, 2);
v___x_3394_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3390_, v_tail_3393_);
lean_inc(v_key_3392_);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_key_3392_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* v_x_3396_, lean_object* v_x_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3396_, v_x_3397_);
lean_dec(v_x_3397_);
lean_dec(v_x_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object* v_as_3399_, size_t v_i_3400_, size_t v_stop_3401_, lean_object* v_b_3402_){
_start:
{
uint8_t v___x_3403_; 
v___x_3403_ = lean_usize_dec_eq(v_i_3400_, v_stop_3401_);
if (v___x_3403_ == 0)
{
size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3404_ = ((size_t)1ULL);
v___x_3405_ = lean_usize_sub(v_i_3400_, v___x_3404_);
v___x_3406_ = lean_array_uget_borrowed(v_as_3399_, v___x_3405_);
v___x_3407_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_b_3402_, v___x_3406_);
lean_dec(v_b_3402_);
v_i_3400_ = v___x_3405_;
v_b_3402_ = v___x_3407_;
goto _start;
}
else
{
return v_b_3402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object* v_as_3409_, lean_object* v_i_3410_, lean_object* v_stop_3411_, lean_object* v_b_3412_){
_start:
{
size_t v_i_boxed_3413_; size_t v_stop_boxed_3414_; lean_object* v_res_3415_; 
v_i_boxed_3413_ = lean_unbox_usize(v_i_3410_);
lean_dec(v_i_3410_);
v_stop_boxed_3414_ = lean_unbox_usize(v_stop_3411_);
lean_dec(v_stop_3411_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_3409_, v_i_boxed_3413_, v_stop_boxed_3414_, v_b_3412_);
lean_dec_ref(v_as_3409_);
return v_res_3415_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0));
v___x_3418_ = l_Lean_stringToMessageData(v___x_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(lean_object* v_as_x27_3419_, lean_object* v_b_3420_){
_start:
{
if (lean_obj_tag(v_as_x27_3419_) == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3420_);
return v___x_3421_;
}
else
{
lean_object* v_head_3422_; lean_object* v_tail_3423_; lean_object* v_type_3424_; lean_object* v_source_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_head_3422_ = lean_ctor_get(v_as_x27_3419_, 0);
v_tail_3423_ = lean_ctor_get(v_as_x27_3419_, 1);
v_type_3424_ = lean_ctor_get(v_head_3422_, 1);
v_source_3425_ = lean_ctor_get(v_head_3422_, 3);
v___x_3426_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1);
lean_inc_ref(v_type_3424_);
v___x_3427_ = l_Lean_MessageData_ofExpr(v_type_3424_);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
lean_inc(v_source_3425_);
v___x_3431_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v_source_3425_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_b_3420_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v_as_x27_3419_ = v_tail_3423_;
v_b_3420_ = v___x_3433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3435_, lean_object* v_b_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3435_, v_b_3436_);
lean_dec(v_as_x27_3435_);
return v_res_3437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object* v_d_3441_){
_start:
{
lean_object* v___y_3443_; lean_object* v_unusedRelevantHypotheses_3446_; lean_object* v_size_3447_; lean_object* v_buckets_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v_unusedRelevantHypotheses_3446_ = lean_ctor_get(v_d_3441_, 3);
v_size_3447_ = lean_ctor_get(v_unusedRelevantHypotheses_3446_, 0);
v_buckets_3448_ = lean_ctor_get(v_unusedRelevantHypotheses_3446_, 1);
v___x_3449_ = lean_unsigned_to_nat(0u);
v___x_3450_ = lean_nat_dec_eq(v_size_3447_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_array_get_size(v_buckets_3448_);
v___x_3453_ = lean_nat_dec_lt(v___x_3449_, v___x_3452_);
if (v___x_3453_ == 0)
{
v___y_3443_ = v___x_3451_;
goto v___jp_3442_;
}
else
{
size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = lean_usize_of_nat(v___x_3452_);
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_buckets_3448_, v___x_3454_, v___x_3455_, v___x_3451_);
v___y_3443_ = v___x_3456_;
goto v___jp_3442_;
}
}
else
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_box(0);
return v___x_3457_;
}
v___jp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
v___x_3445_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v___y_3443_, v___x_3444_);
lean_dec(v___y_3443_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object* v_d_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_3458_);
lean_dec_ref(v_d_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object* v_as_3460_, lean_object* v_as_x27_3461_, lean_object* v_b_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3461_, v_b_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object* v_as_3465_, lean_object* v_as_x27_3466_, lean_object* v_b_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_as_3465_, v_as_x27_3466_, v_b_3467_, v_a_3468_);
lean_dec(v_as_x27_3466_);
lean_dec(v_as_3465_);
return v_res_3469_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0));
v___x_3481_ = l_Lean_stringToMessageData(v___x_3480_);
return v___x_3481_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2));
v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object* v_as_3485_, size_t v_i_3486_, size_t v_stop_3487_, lean_object* v_b_3488_){
_start:
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_usize_dec_eq(v_i_3486_, v_stop_3487_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; size_t v___x_3496_; size_t v___x_3497_; 
v___x_3490_ = lean_array_uget_borrowed(v_as_3485_, v_i_3486_);
v___x_3491_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_b_3488_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
lean_inc(v___x_3490_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3490_);
v___x_3494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = ((size_t)1ULL);
v___x_3497_ = lean_usize_add(v_i_3486_, v___x_3496_);
v_i_3486_ = v___x_3497_;
v_b_3488_ = v___x_3495_;
goto _start;
}
else
{
return v_b_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object* v_as_3499_, lean_object* v_i_3500_, lean_object* v_stop_3501_, lean_object* v_b_3502_){
_start:
{
size_t v_i_boxed_3503_; size_t v_stop_boxed_3504_; lean_object* v_res_3505_; 
v_i_boxed_3503_ = lean_unbox_usize(v_i_3500_);
lean_dec(v_i_3500_);
v_stop_boxed_3504_ = lean_unbox_usize(v_stop_3501_);
lean_dec(v_stop_3501_);
v_res_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_3499_, v_i_boxed_3503_, v_stop_boxed_3504_, v_b_3502_);
lean_dec_ref(v_as_3499_);
return v_res_3505_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object* v_as_3509_, size_t v_i_3510_, size_t v_stop_3511_, lean_object* v_b_3512_){
_start:
{
uint8_t v___x_3513_; 
v___x_3513_ = lean_usize_dec_eq(v_i_3510_, v_stop_3511_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v_fst_3515_; lean_object* v_snd_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3533_; 
v___x_3514_ = lean_array_uget(v_as_3509_, v_i_3510_);
v_fst_3515_ = lean_ctor_get(v___x_3514_, 0);
v_snd_3516_ = lean_ctor_get(v___x_3514_, 1);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3518_ = v___x_3514_;
v_isShared_3519_ = v_isSharedCheck_3533_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_snd_3516_);
lean_inc(v_fst_3515_);
lean_dec(v___x_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3533_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3520_ = l_Lean_MessageData_ofExpr(v_fst_3515_);
v___x_3521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
if (v_isShared_3519_ == 0)
{
lean_ctor_set_tag(v___x_3518_, 7);
lean_ctor_set(v___x_3518_, 1, v___x_3521_);
lean_ctor_set(v___x_3518_, 0, v___x_3520_);
v___x_3523_ = v___x_3518_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; size_t v___x_3529_; size_t v___x_3530_; 
v___x_3524_ = l_Lean_MessageData_ofExpr(v_snd_3516_);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_b_3512_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = ((size_t)1ULL);
v___x_3530_ = lean_usize_add(v_i_3510_, v___x_3529_);
v_i_3510_ = v___x_3530_;
v_b_3512_ = v___x_3528_;
goto _start;
}
}
}
else
{
return v_b_3512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object* v_as_3534_, lean_object* v_i_3535_, lean_object* v_stop_3536_, lean_object* v_b_3537_){
_start:
{
size_t v_i_boxed_3538_; size_t v_stop_boxed_3539_; lean_object* v_res_3540_; 
v_i_boxed_3538_ = lean_unbox_usize(v_i_3535_);
lean_dec(v_i_3535_);
v_stop_boxed_3539_ = lean_unbox_usize(v_stop_3536_);
lean_dec(v_stop_3536_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_3534_, v_i_boxed_3538_, v_stop_boxed_3539_, v_b_3537_);
lean_dec_ref(v_as_3534_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object* v_a_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_){
_start:
{
if (lean_obj_tag(v_x_3543_) == 0)
{
lean_dec_ref(v_a_3541_);
return v_x_3542_;
}
else
{
lean_object* v_head_3544_; lean_object* v_tail_3545_; lean_object* v___x_3546_; 
v_head_3544_ = lean_ctor_get(v_x_3543_, 0);
lean_inc(v_head_3544_);
v_tail_3545_ = lean_ctor_get(v_x_3543_, 1);
lean_inc(v_tail_3545_);
lean_dec_ref_known(v_x_3543_, 2);
lean_inc_ref(v_a_3541_);
v___x_3546_ = lean_apply_1(v_head_3544_, v_a_3541_);
if (lean_obj_tag(v___x_3546_) == 1)
{
lean_object* v_val_3547_; lean_object* v___x_3548_; 
v_val_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_val_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = lean_array_push(v_x_3542_, v_val_3547_);
v_x_3542_ = v___x_3548_;
v_x_3543_ = v_tail_3545_;
goto _start;
}
else
{
lean_dec(v___x_3546_);
v_x_3543_ = v_tail_3545_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0));
v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object* v_counterExample_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed), 7, 0);
v___x_3572_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_3571_, v_counterExample_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3644_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3644_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3644_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v_err_3578_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v_err_3616_; lean_object* v___y_3632_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3608_ = lean_unsigned_to_nat(0u);
v___x_3609_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2));
v___x_3610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers));
lean_inc_n(v_a_3573_, 2);
v___x_3611_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3573_, v___x_3609_, v___x_3610_);
v___x_3612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers));
v___x_3613_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_3573_, v___x_3609_, v___x_3612_);
v___x_3614_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4);
v___x_3634_ = lean_array_get_size(v___x_3611_);
v___x_3635_ = lean_nat_dec_eq(v___x_3634_, v___x_3608_);
if (v___x_3635_ == 0)
{
uint8_t v___x_3636_; 
v___x_3636_ = lean_nat_dec_lt(v___x_3608_, v___x_3634_);
if (v___x_3636_ == 0)
{
lean_dec_ref(v___x_3611_);
v___y_3632_ = v___x_3614_;
goto v___jp_3631_;
}
else
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_nat_dec_le(v___x_3634_, v___x_3634_);
if (v___x_3637_ == 0)
{
if (v___x_3636_ == 0)
{
lean_dec_ref(v___x_3611_);
v___y_3632_ = v___x_3614_;
goto v___jp_3631_;
}
else
{
size_t v___x_3638_; size_t v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = ((size_t)0ULL);
v___x_3639_ = lean_usize_of_nat(v___x_3634_);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3611_, v___x_3638_, v___x_3639_, v___x_3614_);
lean_dec_ref(v___x_3611_);
v___y_3632_ = v___x_3640_;
goto v___jp_3631_;
}
}
else
{
size_t v___x_3641_; size_t v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((size_t)0ULL);
v___x_3642_ = lean_usize_of_nat(v___x_3634_);
v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3611_, v___x_3641_, v___x_3642_, v___x_3614_);
lean_dec_ref(v___x_3611_);
v___y_3632_ = v___x_3643_;
goto v___jp_3631_;
}
}
}
else
{
lean_dec_ref(v___x_3611_);
v_err_3616_ = v___x_3614_;
goto v___jp_3615_;
}
v___jp_3577_:
{
lean_object* v_derivedEquations_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v_derivedEquations_3579_ = lean_ctor_get(v_a_3573_, 4);
lean_inc_ref(v_derivedEquations_3579_);
lean_dec(v_a_3573_);
v___x_3580_ = lean_unsigned_to_nat(0u);
v___x_3581_ = lean_array_get_size(v_derivedEquations_3579_);
v___x_3582_ = lean_nat_dec_lt(v___x_3580_, v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3584_; 
lean_dec_ref(v_derivedEquations_3579_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v_err_3578_);
v___x_3584_ = v___x_3575_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_err_3578_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
else
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_nat_dec_le(v___x_3581_, v___x_3581_);
if (v___x_3586_ == 0)
{
if (v___x_3582_ == 0)
{
lean_object* v___x_3588_; 
lean_dec_ref(v_derivedEquations_3579_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v_err_3578_);
v___x_3588_ = v___x_3575_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_err_3578_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
else
{
size_t v___x_3590_; size_t v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3590_ = ((size_t)0ULL);
v___x_3591_ = lean_usize_of_nat(v___x_3581_);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3579_, v___x_3590_, v___x_3591_, v_err_3578_);
lean_dec_ref(v_derivedEquations_3579_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3592_);
v___x_3594_ = v___x_3575_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
else
{
size_t v___x_3596_; size_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3596_ = ((size_t)0ULL);
v___x_3597_ = lean_usize_of_nat(v___x_3581_);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_3579_, v___x_3596_, v___x_3597_, v_err_3578_);
lean_dec_ref(v_derivedEquations_3579_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3598_);
v___x_3600_ = v___x_3575_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
v___jp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___y_3603_);
lean_ctor_set(v___x_3605_, 1, v___y_3604_);
v___x_3606_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v_err_3578_ = v___x_3607_;
goto v___jp_3577_;
}
v___jp_3615_:
{
lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3617_ = lean_array_get_size(v___x_3613_);
v___x_3618_ = lean_nat_dec_eq(v___x_3617_, v___x_3608_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3619_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v_err_3616_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_nat_dec_lt(v___x_3608_, v___x_3617_);
if (v___x_3621_ == 0)
{
lean_dec_ref(v___x_3613_);
v___y_3603_ = v___x_3620_;
v___y_3604_ = v___x_3614_;
goto v___jp_3602_;
}
else
{
uint8_t v___x_3622_; 
v___x_3622_ = lean_nat_dec_le(v___x_3617_, v___x_3617_);
if (v___x_3622_ == 0)
{
if (v___x_3621_ == 0)
{
lean_dec_ref(v___x_3613_);
v___y_3603_ = v___x_3620_;
v___y_3604_ = v___x_3614_;
goto v___jp_3602_;
}
else
{
size_t v___x_3623_; size_t v___x_3624_; lean_object* v___x_3625_; 
v___x_3623_ = ((size_t)0ULL);
v___x_3624_ = lean_usize_of_nat(v___x_3617_);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3613_, v___x_3623_, v___x_3624_, v___x_3614_);
lean_dec_ref(v___x_3613_);
v___y_3603_ = v___x_3620_;
v___y_3604_ = v___x_3625_;
goto v___jp_3602_;
}
}
else
{
size_t v___x_3626_; size_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = lean_usize_of_nat(v___x_3617_);
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_3613_, v___x_3626_, v___x_3627_, v___x_3614_);
lean_dec_ref(v___x_3613_);
v___y_3603_ = v___x_3620_;
v___y_3604_ = v___x_3628_;
goto v___jp_3602_;
}
}
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_dec_ref(v___x_3613_);
v___x_3629_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v_err_3616_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v_err_3578_ = v___x_3630_;
goto v___jp_3577_;
}
}
v___jp_3631_:
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3614_);
lean_ctor_set(v___x_3633_, 1, v___y_3632_);
v_err_3616_ = v___x_3633_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
v_a_3645_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3572_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3572_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object* v_counterExample_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
lean_dec(v_a_3657_);
lean_dec_ref(v_a_3656_);
lean_dec(v_a_3655_);
lean_dec_ref(v_a_3654_);
return v_res_3659_;
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

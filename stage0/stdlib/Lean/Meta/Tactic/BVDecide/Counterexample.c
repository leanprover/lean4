// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Counterexample
// Imports: import Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical import Std.Tactic.BVDecide.EPR.BitVec import Std.Tactic.BVDecide.Normalize.Prop public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Internal.Sat.AIG.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredPropArity;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredBoolArity;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_toSubscriptString(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecType_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__4_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__5;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "_private.Lean.Meta.Tactic.BVDecide.Counterexample.0.Lean.Meta.Tactic.BVDecide.DiagnosisM.diagnose.transformBitVecEquation"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 57, 165, 14, 135, 135, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(231, 54, 185, 195, 30, 183, 107, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(44, 210, 78, 221, 232, 52, 28, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 114, 73, 21, 161, 185, 192, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 144, 45, 221, 65, 48, 204, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(95, 106, 42, 185, 61, 138, 17, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(83, 21, 175, 117, 0, 32, 88, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__22_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 247, 174, 117, 226, 108, 136, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__24_value),LEAN_SCALAR_PTR_LITERAL(121, 35, 113, 77, 117, 41, 40, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toBitVec64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__27_value),LEAN_SCALAR_PTR_LITERAL(51, 79, 88, 119, 92, 132, 69, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toBitVec32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__29_value),LEAN_SCALAR_PTR_LITERAL(40, 3, 162, 24, 208, 1, 22, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__27_value),LEAN_SCALAR_PTR_LITERAL(116, 153, 59, 255, 117, 164, 81, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__29_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 16, 185, 133, 236, 22, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for USize was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__35;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " bits"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__38_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__39_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__40;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(43, 155, 189, 13, 93, 69, 82, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for USize was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__48_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__49;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for ISize was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__50_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__51;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__53_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__54_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__55_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__57_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__26_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(185, 56, 140, 35, 97, 137, 251, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__60_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for ISize was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__62_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__63;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__65_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__67 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__67_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__68 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__68_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__64_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__65_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__66_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__67_value),LEAN_SCALAR_PTR_LITERAL(189, 0, 62, 153, 37, 253, 54, 88)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__68_value),LEAN_SCALAR_PTR_LITERAL(153, 71, 30, 209, 57, 12, 129, 48)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__70 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__70_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__67_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__70_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__72;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__73 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__67_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__73_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__75;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__76 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__76_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__76_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__77 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__77_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__78 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__78_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__78_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__79 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__79_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Value for UInt8 was not 8 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__80 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__80_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__81;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__22_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__82 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__82_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__83;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__22_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__84_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(106, 22, 191, 22, 91, 53, 63, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__84 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__84_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__85;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Value for UInt16 was not 16 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__86 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__86_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__87;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__88 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__88_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__89;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__90_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(100, 85, 82, 103, 43, 170, 82, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__90 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__90_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__91;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Value for UInt32 was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__92 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__92_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__93;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__94 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__94_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__95;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__18_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__96_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(112, 78, 205, 187, 174, 188, 116, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__96 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__96_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__97;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Value for UInt64 was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__98 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__98_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__99;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__100 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__100_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__101;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__16_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__102_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(8, 204, 85, 89, 36, 115, 101, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__102 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__102_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__103;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Value for Int8 was not 8 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__104 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__104_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__105;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__106;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__107 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__107_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__108;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__14_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__109_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 113, 74, 244, 2, 252, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__109 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__109_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__110_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__110;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for Int16 was not 16 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__111 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__111_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__112;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__113;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__114 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__114_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__115;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__12_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__116_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(62, 21, 130, 152, 152, 188, 226, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__116 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__116_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__117_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__117;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for Int32 was not 32 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__118 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__118_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__119;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__120;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__121 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__121_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__122;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__123_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(133, 86, 165, 75, 15, 11, 161, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__123 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__123_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__124;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Value for Int64 was not 64 bits but "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__125 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__125_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__126;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__127;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__128 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__128_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__129;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__130_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__59_value),LEAN_SCALAR_PTR_LITERAL(24, 152, 19, 102, 101, 167, 71, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__130 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__130_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__131_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__131;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "EPR"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toBvAux"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__64_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__65_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__66_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 44, 27, 80, 162, 73, 229, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "EPR sort is not an FVarId"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_121_ = lean_unsigned_to_nat(63u);
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
v___x_331_ = lean_nat_add(v___y_328_, v___y_330_);
lean_dec(v___y_330_);
lean_dec(v___y_328_);
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
lean_ctor_set(v___x_311_, 3, v___y_329_);
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
lean_ctor_set(v_reuseFailAlloc_336_, 3, v___y_329_);
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
v___y_328_ = v___x_343_;
v___y_329_ = v___x_342_;
v___y_330_ = v_size_344_;
goto v___jp_327_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___y_328_ = v___x_343_;
v___y_329_ = v___x_342_;
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
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_instMonadEIO___redArg();
return v___x_1588_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__5(void){
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1(lean_object* v_msg_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_toApplicative_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1668_; 
v___x_1603_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__0);
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
v___f_1616_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__1));
v___f_1617_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__2));
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
v___f_1640_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__3));
v___f_1641_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__4));
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
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___x_12849__overap_1656_; lean_object* v___x_1657_; 
v___x_1652_ = l_StateRefT_x27_instMonad___redArg(v___x_1651_);
v___x_1653_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__5, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__5_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___closed__5);
v___x_1654_ = l_instInhabitedOfMonad___redArg(v___x_1652_, v___x_1653_);
v___f_1655_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1655_, 0, v___x_1654_);
v___x_12849__overap_1656_ = lean_panic_fn_borrowed(v___f_1655_, v_msg_1595_);
lean_dec_ref(v___f_1655_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
lean_inc_ref(v___y_1598_);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1596_);
v___x_1657_ = lean_apply_7(v___x_12849__overap_1656_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, lean_box(0));
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1___boxed(lean_object* v_msg_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1(v_msg_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
lean_ctor_set(v___x_1684_, 2, v___x_1683_);
lean_ctor_set(v___x_1684_, 3, v___x_1683_);
lean_ctor_set(v___x_1684_, 4, v___x_1682_);
lean_ctor_set(v___x_1684_, 5, v___x_1682_);
lean_ctor_set(v___x_1684_, 6, v___x_1682_);
lean_ctor_set(v___x_1684_, 7, v___x_1682_);
lean_ctor_set(v___x_1684_, 8, v___x_1682_);
lean_ctor_set(v___x_1684_, 9, v___x_1682_);
lean_ctor_set(v___x_1684_, 10, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_unsigned_to_nat(32u);
v___x_1686_ = lean_mk_empty_array_with_capacity(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = ((size_t)5ULL);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = lean_unsigned_to_nat(32u);
v___x_1691_ = lean_mk_empty_array_with_capacity(v___x_1690_);
v___x_1692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1693_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v___x_1689_);
lean_ctor_set(v___x_1693_, 3, v___x_1689_);
lean_ctor_set_usize(v___x_1693_, 4, v___x_1688_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = lean_box(1);
v___x_1695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_1696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v___x_1694_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_1718_ = l_Lean_stringToMessageData(v___x_1717_);
return v___x_1718_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__20));
v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__22));
v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__24));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__26));
v___x_1730_ = l_Lean_stringToMessageData(v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1731_, lean_object* v_declHint_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_env_1737_; uint8_t v___x_1738_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_st_ref_get(v___y_1733_);
v_env_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_ref(v_env_1737_);
lean_dec(v___x_1736_);
v___x_1738_ = l_Lean_Name_isAnonymous(v_declHint_1732_);
if (v___x_1738_ == 0)
{
uint8_t v_isExporting_1739_; 
v_isExporting_1739_ = lean_ctor_get_uint8(v_env_1737_, sizeof(void*)*13);
if (v_isExporting_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v_env_1737_);
lean_dec(v_declHint_1732_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_msg_1731_);
return v___x_1740_;
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
lean_inc_ref(v_env_1737_);
v___x_1741_ = l_Lean_Environment_setExporting(v_env_1737_, v___x_1738_);
lean_inc(v_declHint_1732_);
lean_inc_ref(v___x_1741_);
v___x_1742_ = l_Lean_Environment_contains(v___x_1741_, v_declHint_1732_, v_isExporting_1739_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref(v___x_1741_);
lean_dec_ref(v_env_1737_);
lean_dec(v_declHint_1732_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_msg_1731_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_c_1749_; lean_object* v___x_1750_; 
v___x_1744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_1745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1746_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1741_);
v___x_1747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1741_);
lean_ctor_set(v___x_1747_, 1, v___x_1744_);
lean_ctor_set(v___x_1747_, 2, v___x_1745_);
lean_ctor_set(v___x_1747_, 3, v___x_1746_);
lean_inc(v_declHint_1732_);
v___x_1748_ = l_Lean_MessageData_ofConstName(v_declHint_1732_, v___x_1738_);
v_c_1749_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1749_, 0, v___x_1747_);
lean_ctor_set(v_c_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1741_, v_declHint_1732_);
lean_dec_ref(v___x_1741_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v_env_1737_);
lean_dec(v_declHint_1732_);
v___x_1751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v_c_1749_);
v___x_1753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_MessageData_note(v___x_1754_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_msg_1731_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1811_; 
v_val_1758_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1760_ = v___x_1750_;
v_isShared_1761_ = v_isSharedCheck_1811_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v___x_1750_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1811_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v_modules_1763_; lean_object* v_moduleNames_1764_; lean_object* v_mod_1765_; uint8_t v___x_1780_; 
v___x_1762_ = l_Lean_Environment_header(v_env_1737_);
lean_dec_ref(v_env_1737_);
v_modules_1763_ = lean_ctor_get(v___x_1762_, 3);
lean_inc_ref(v_modules_1763_);
v_moduleNames_1764_ = lean_ctor_get(v___x_1762_, 4);
lean_inc_ref(v_moduleNames_1764_);
lean_dec_ref(v___x_1762_);
v_mod_1765_ = lean_array_get(v___x_1735_, v_moduleNames_1764_, v_val_1758_);
lean_dec_ref(v_moduleNames_1764_);
v___x_1780_ = l_Lean_isPrivateName(v_declHint_1732_);
lean_dec(v_declHint_1732_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = lean_array_get_size(v_modules_1763_);
v___x_1782_ = lean_nat_dec_lt(v_val_1758_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v_modules_1763_);
lean_dec(v_val_1758_);
goto v___jp_1766_;
}
else
{
lean_object* v___x_1783_; lean_object* v_toImport_1784_; uint8_t v_isExported_1785_; 
v___x_1783_ = lean_array_fget(v_modules_1763_, v_val_1758_);
lean_dec(v_val_1758_);
lean_dec_ref(v_modules_1763_);
v_toImport_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc_ref(v_toImport_1784_);
lean_dec(v___x_1783_);
v_isExported_1785_ = lean_ctor_get_uint8(v_toImport_1784_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1784_);
if (v_isExported_1785_ == 0)
{
goto v___jp_1766_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_del_object(v___x_1760_);
v___x_1786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v_c_1749_);
v___x_1788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_MessageData_ofName(v_mod_1765_);
lean_inc_ref(v___x_1790_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__21);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v___x_1790_);
v___x_1795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__23);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_MessageData_note(v___x_1796_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_msg_1731_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec_ref(v_modules_1763_);
lean_del_object(v___x_1760_);
lean_dec(v_val_1758_);
v___x_1800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_c_1749_);
v___x_1802_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__25);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_MessageData_ofName(v_mod_1765_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__27);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_MessageData_note(v___x_1807_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_msg_1731_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
v___jp_1766_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v_c_1749_);
v___x_1769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_MessageData_ofName(v_mod_1765_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_MessageData_note(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_msg_1731_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1776_);
v___x_1778_ = v___x_1760_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1812_; 
lean_dec_ref(v_env_1737_);
lean_dec(v_declHint_1732_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_msg_1731_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1813_, lean_object* v_declHint_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1813_, v_declHint_1814_, v___y_1815_);
lean_dec(v___y_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_msg_1818_, lean_object* v_declHint_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1837_; 
v___x_1827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_1818_, v_declHint_1819_, v___y_1825_);
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1837_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1837_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1832_ = l_Lean_unknownIdentifierMessageTag;
v___x_1833_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_a_1828_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1833_);
v___x_1835_ = v___x_1830_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_msg_1838_, lean_object* v_declHint_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1838_, v_declHint_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2_spec__3(lean_object* v_msgData_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v_env_1855_; uint8_t v___x_1856_; lean_object* v_env_1857_; lean_object* v___x_1858_; lean_object* v_toCold_1859_; lean_object* v_mctx_1860_; lean_object* v_lctx_1861_; lean_object* v_options_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1854_ = lean_st_ref_get(v___y_1852_);
v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc_ref(v_env_1855_);
lean_dec(v___x_1854_);
v___x_1856_ = 0;
v_env_1857_ = l_Lean_Environment_setRecordingDeps(v_env_1855_, v___x_1856_);
v___x_1858_ = lean_st_ref_get(v___y_1850_);
v_toCold_1859_ = lean_ctor_get(v___y_1851_, 0);
v_mctx_1860_ = lean_ctor_get(v___x_1858_, 0);
lean_inc_ref(v_mctx_1860_);
lean_dec(v___x_1858_);
v_lctx_1861_ = lean_ctor_get(v___y_1849_, 2);
v_options_1862_ = lean_ctor_get(v_toCold_1859_, 2);
lean_inc_ref(v_options_1862_);
lean_inc_ref(v_lctx_1861_);
v___x_1863_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1863_, 0, v_env_1857_);
lean_ctor_set(v___x_1863_, 1, v_mctx_1860_);
lean_ctor_set(v___x_1863_, 2, v_lctx_1861_);
lean_ctor_set(v___x_1863_, 3, v_options_1862_);
v___x_1864_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_msgData_1848_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2_spec__3___boxed(lean_object* v_msgData_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2_spec__3(v_msgData_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(lean_object* v_msg_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_ref_1879_; lean_object* v___x_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_ref_1879_ = lean_ctor_get(v___y_1876_, 2);
v___x_1880_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2_spec__3(v_msg_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_inc(v_ref_1879_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_ref_1879_);
lean_ctor_set(v___x_1885_, 1, v_a_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 1);
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg___boxed(lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v_msg_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1897_, lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_toCold_1906_; lean_object* v_currRecDepth_1907_; lean_object* v_ref_1908_; uint16_t v_optionFlags_1909_; uint8_t v_suppressElabErrors_1910_; uint8_t v_checkDeprecated_1911_; uint8_t v_isRecordingDeps_1912_; lean_object* v_ref_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_toCold_1906_ = lean_ctor_get(v___y_1903_, 0);
v_currRecDepth_1907_ = lean_ctor_get(v___y_1903_, 1);
v_ref_1908_ = lean_ctor_get(v___y_1903_, 2);
v_optionFlags_1909_ = lean_ctor_get_uint16(v___y_1903_, sizeof(void*)*3);
v_suppressElabErrors_1910_ = lean_ctor_get_uint8(v___y_1903_, sizeof(void*)*3 + 2);
v_checkDeprecated_1911_ = lean_ctor_get_uint8(v___y_1903_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1912_ = lean_ctor_get_uint8(v___y_1903_, sizeof(void*)*3 + 4);
v_ref_1913_ = l_Lean_replaceRef(v_ref_1897_, v_ref_1908_);
lean_inc(v_currRecDepth_1907_);
lean_inc_ref(v_toCold_1906_);
v___x_1914_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1914_, 0, v_toCold_1906_);
lean_ctor_set(v___x_1914_, 1, v_currRecDepth_1907_);
lean_ctor_set(v___x_1914_, 2, v_ref_1913_);
lean_ctor_set_uint16(v___x_1914_, sizeof(void*)*3, v_optionFlags_1909_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*3 + 2, v_suppressElabErrors_1910_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*3 + 3, v_checkDeprecated_1911_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*3 + 4, v_isRecordingDeps_1912_);
v___x_1915_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v_msg_1898_, v___y_1901_, v___y_1902_, v___x_1914_, v___y_1904_);
lean_dec_ref_known(v___x_1914_, 3);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1916_, lean_object* v_msg_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1916_, v_msg_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v_ref_1916_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_ref_1926_, lean_object* v_msg_1927_, lean_object* v_declHint_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_a_1937_; lean_object* v___x_1938_; 
v___x_1936_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_1927_, v_declHint_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_1926_, v_a_1937_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1939_, lean_object* v_msg_1940_, lean_object* v_declHint_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1939_, v_msg_1940_, v_declHint_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v_ref_1939_);
return v_res_1949_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1952_ = l_Lean_stringToMessageData(v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1955_ = l_Lean_stringToMessageData(v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1956_, lean_object* v_constName_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1965_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1966_ = 0;
lean_inc(v_constName_1957_);
v___x_1967_ = l_Lean_MessageData_ofConstName(v_constName_1957_, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1965_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_1956_, v___x_1970_, v_constName_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1972_, lean_object* v_constName_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg(v_ref_1972_, v_constName_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v_ref_1972_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg(lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_ref_1990_; lean_object* v___x_1991_; 
v_ref_1990_ = lean_ctor_get(v___y_1987_, 2);
v___x_1991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg(v_ref_1990_, v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg(v_constName_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0(lean_object* v_constName_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v_env_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2009_ = lean_st_ref_get(v___y_2007_);
v_env_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc_ref(v_env_2010_);
lean_dec(v___x_2009_);
v___x_2011_ = 0;
lean_inc(v_constName_2001_);
v___x_2012_ = l_Lean_Environment_find_x3f(v_env_2010_, v_constName_2001_, v___x_2011_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg(v_constName_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
return v___x_2013_;
}
else
{
lean_object* v_val_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_constName_2001_);
v_val_2014_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2012_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_val_2014_);
lean_dec(v___x_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 0);
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_val_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0___boxed(lean_object* v_constName_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0(v_constName_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__2));
v___x_2038_ = l_Lean_Expr_const___override(v___x_2037_, v___x_2036_);
return v___x_2038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__6(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__5));
v___x_2042_ = lean_unsigned_to_nat(61u);
v___x_2043_ = lean_unsigned_to_nat(257u);
v___x_2044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__4));
v___x_2045_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___closed__0));
v___x_2046_ = l_mkPanicMessageWithDecl(v___x_2045_, v___x_2044_, v___x_2043_, v___x_2042_, v___x_2041_);
return v___x_2046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__35(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__34));
v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
return v___x_2102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__36));
v___x_2105_ = l_Lean_stringToMessageData(v___x_2104_);
return v___x_2105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__40(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = l_Lean_Level_ofNat(v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_box(0);
v___x_2113_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__40, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__40_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__40);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41);
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__39));
v___x_2117_ = l_Lean_Expr_const___override(v___x_2116_, v___x_2115_);
return v___x_2117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = lean_box(0);
v___x_2121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__43));
v___x_2122_ = l_Lean_mkConst(v___x_2121_, v___x_2120_);
return v___x_2122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__46));
v___x_2129_ = l_Lean_Expr_const___override(v___x_2128_, v___x_2127_);
return v___x_2129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__49(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__48));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__51(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__50));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static size_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52(void){
_start:
{
lean_object* v___x_2136_; size_t v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_isize_of_nat(v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__41);
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__55));
v___x_2145_ = l_Lean_Expr_const___override(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__57));
v___x_2150_ = l_Lean_Expr_const___override(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__60));
v___x_2157_ = l_Lean_Expr_const___override(v___x_2156_, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__63(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__62));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__72(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_box(0);
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71));
v___x_2178_ = l_Lean_mkConst(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__75(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_box(0);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74));
v___x_2185_ = l_Lean_mkConst(v___x_2184_, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__81(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__80));
v___x_2194_ = l_Lean_stringToMessageData(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__83(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_box(0);
v___x_2198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__82));
v___x_2199_ = l_Lean_mkConst(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__85(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_box(0);
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__84));
v___x_2205_ = l_Lean_Expr_const___override(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__87(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__86));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__89(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__88));
v___x_2213_ = l_Lean_mkConst(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__91(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__90));
v___x_2219_ = l_Lean_Expr_const___override(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__93(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__92));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__95(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__94));
v___x_2227_ = l_Lean_mkConst(v___x_2226_, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__97(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__96));
v___x_2233_ = l_Lean_Expr_const___override(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__99(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__98));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__101(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__100));
v___x_2241_ = l_Lean_mkConst(v___x_2240_, v___x_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__103(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__102));
v___x_2247_ = l_Lean_Expr_const___override(v___x_2246_, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__105(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__104));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__106(void){
_start:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = lean_int8_of_nat(v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__108(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__107));
v___x_2257_ = l_Lean_Expr_const___override(v___x_2256_, v___x_2255_);
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__110(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__109));
v___x_2263_ = l_Lean_Expr_const___override(v___x_2262_, v___x_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__112(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__111));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static uint16_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__113(void){
_start:
{
lean_object* v___x_2267_; uint16_t v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = lean_int16_of_nat(v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__115(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__114));
v___x_2273_ = l_Lean_Expr_const___override(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__117(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__116));
v___x_2279_ = l_Lean_Expr_const___override(v___x_2278_, v___x_2277_);
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__119(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__118));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
static uint32_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__120(void){
_start:
{
lean_object* v___x_2283_; uint32_t v___x_2284_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = lean_int32_of_nat(v___x_2283_);
return v___x_2284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__122(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__121));
v___x_2289_ = l_Lean_Expr_const___override(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__124(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__123));
v___x_2295_ = l_Lean_Expr_const___override(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__126(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__125));
v___x_2298_ = l_Lean_stringToMessageData(v___x_2297_);
return v___x_2298_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__127(void){
_start:
{
lean_object* v___x_2299_; uint64_t v___x_2300_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = lean_int64_of_nat(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__129(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_box(0);
v___x_2304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__128));
v___x_2305_ = l_Lean_Expr_const___override(v___x_2304_, v___x_2303_);
return v___x_2305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__131(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__130));
v___x_2311_ = l_Lean_Expr_const___override(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation(lean_object* v_var_2312_, lean_object* v_value_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v___x_2336_; 
v___x_2336_ = l_Lean_Expr_isFVar(v_var_2312_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___x_2399_; 
v___x_2337_ = lean_box(0);
lean_inc_ref(v_var_2312_);
v___x_2399_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_2312_, v_a_2317_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2869_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2869_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2869_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = l_Lean_Expr_cleanupAnnotations(v_a_2400_);
lean_dec(v_a_2400_);
v___x_2405_ = l_Lean_Expr_isApp(v___x_2404_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v___x_2404_);
lean_del_object(v___x_2402_);
v___y_2339_ = v_a_2314_;
v___y_2340_ = v_a_2315_;
v___y_2341_ = v_a_2316_;
v___y_2342_ = v_a_2317_;
v___y_2343_ = v_a_2318_;
v___y_2344_ = v_a_2319_;
goto v___jp_2338_;
}
else
{
lean_object* v_arg_2406_; lean_object* v___y_2408_; lean_object* v___y_2414_; lean_object* v___y_2418_; lean_object* v___y_2422_; lean_object* v___y_2426_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v_arg_2406_ = lean_ctor_get(v___x_2404_, 1);
lean_inc_ref(v_arg_2406_);
v___x_2429_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2404_);
lean_dec_ref(v___x_2404_);
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__9));
v___x_2431_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
lean_del_object(v___x_2402_);
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__11));
v___x_2433_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__13));
v___x_2435_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__15));
v___x_2437_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__17));
v___x_2439_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__19));
v___x_2441_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__21));
v___x_2443_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__23));
v___x_2445_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25));
v___x_2447_ = l_Lean_Expr_isConstOf(v___x_2429_, v___x_2446_);
if (v___x_2447_ == 0)
{
uint8_t v___x_2448_; 
lean_dec_ref(v_arg_2406_);
v___x_2448_ = l_Lean_Expr_isApp(v___x_2429_);
if (v___x_2448_ == 0)
{
lean_dec_ref(v___x_2429_);
v___y_2339_ = v_a_2314_;
v___y_2340_ = v_a_2315_;
v___y_2341_ = v_a_2316_;
v___y_2342_ = v_a_2317_;
v___y_2343_ = v_a_2318_;
v___y_2344_ = v_a_2319_;
goto v___jp_2338_;
}
else
{
lean_object* v_arg_2449_; lean_object* v___y_2451_; lean_object* v___y_2455_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_arg_2449_ = lean_ctor_get(v___x_2429_, 1);
lean_inc_ref(v_arg_2449_);
v___x_2458_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2429_);
lean_dec_ref(v___x_2429_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__28));
v___x_2460_ = l_Lean_Expr_isConstOf(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__30));
v___x_2462_ = l_Lean_Expr_isConstOf(v___x_2458_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__32));
v___x_2464_ = l_Lean_Expr_isConstOf(v___x_2458_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__33));
v___x_2466_ = l_Lean_Expr_isConstOf(v___x_2458_, v___x_2465_);
lean_dec_ref(v___x_2458_);
if (v___x_2466_ == 0)
{
lean_dec_ref(v_arg_2449_);
v___y_2339_ = v_a_2314_;
v___y_2340_ = v_a_2315_;
v___y_2341_ = v_a_2316_;
v___y_2342_ = v_a_2317_;
v___y_2343_ = v_a_2318_;
v___y_2344_ = v_a_2319_;
goto v___jp_2338_;
}
else
{
lean_object* v_w_2467_; lean_object* v_bv_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v_var_2312_);
v_w_2467_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2468_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2470_ = v_value_2313_;
v_isShared_2471_ = v_isSharedCheck_2496_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_bv_2468_);
lean_inc(v_w_2467_);
lean_dec(v_value_2313_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2496_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = lean_unsigned_to_nat(32u);
v___x_2473_ = lean_nat_dec_eq(v_w_2467_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_dec(v_bv_2468_);
lean_dec_ref(v_arg_2449_);
v___x_2474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__35, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__35_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__35);
v___x_2475_ = l_Nat_reprFast(v_w_2467_);
v___x_2476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
v___x_2477_ = l_Lean_MessageData_ofFormat(v___x_2476_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 7);
lean_ctor_set(v___x_2470_, 1, v___x_2477_);
lean_ctor_set(v___x_2470_, 0, v___x_2474_);
v___x_2479_ = v___x_2470_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2481_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2482_;
}
}
else
{
size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v_r_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v_w_2467_);
v___x_2484_ = lean_usize_of_nat(v_bv_2468_);
lean_dec(v_bv_2468_);
v___x_2485_ = lean_usize_to_nat(v___x_2484_);
v_r_2486_ = l_Lean_mkRawNatLit(v___x_2485_);
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42);
v___x_2488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44);
v___x_2489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47);
lean_inc_ref(v_r_2486_);
v___x_2490_ = l_Lean_Expr_app___override(v___x_2489_, v_r_2486_);
v___x_2491_ = l_Lean_mkApp3(v___x_2487_, v___x_2488_, v_r_2486_, v___x_2490_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2491_);
lean_ctor_set(v___x_2470_, 0, v_arg_2449_);
v___x_2493_ = v___x_2470_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_arg_2449_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
}
}
}
else
{
lean_object* v_w_2497_; lean_object* v_bv_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___x_2458_);
lean_dec_ref(v_var_2312_);
v_w_2497_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2498_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2500_ = v_value_2313_;
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_bv_2498_);
lean_inc(v_w_2497_);
lean_dec(v_value_2313_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2526_;
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
lean_dec_ref(v_arg_2449_);
v___x_2504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__49, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__49_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__49);
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
v___x_2510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2511_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2512_;
}
}
else
{
size_t v___x_2514_; lean_object* v___x_2515_; lean_object* v_r_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec(v_w_2497_);
v___x_2514_ = lean_usize_of_nat(v_bv_2498_);
lean_dec(v_bv_2498_);
v___x_2515_ = lean_usize_to_nat(v___x_2514_);
v_r_2516_ = l_Lean_mkRawNatLit(v___x_2515_);
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42);
v___x_2518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__44);
v___x_2519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__47);
lean_inc_ref(v_r_2516_);
v___x_2520_ = l_Lean_Expr_app___override(v___x_2519_, v_r_2516_);
v___x_2521_ = l_Lean_mkApp3(v___x_2517_, v___x_2518_, v_r_2516_, v___x_2520_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v___x_2521_);
lean_ctor_set(v___x_2500_, 0, v_arg_2449_);
v___x_2523_ = v___x_2500_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_arg_2449_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
}
}
}
else
{
lean_object* v_w_2527_; lean_object* v_bv_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v___x_2458_);
lean_dec_ref(v_var_2312_);
v_w_2527_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2528_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2530_ = v_value_2313_;
v_isShared_2531_ = v_isSharedCheck_2559_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_bv_2528_);
lean_inc(v_w_2527_);
lean_dec(v_value_2313_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2559_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2532_ = lean_unsigned_to_nat(32u);
v___x_2533_ = lean_nat_dec_eq(v_w_2527_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
lean_dec(v_bv_2528_);
lean_dec_ref(v_arg_2449_);
v___x_2534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__51, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__51_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__51);
v___x_2535_ = l_Nat_reprFast(v_w_2527_);
v___x_2536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
v___x_2537_ = l_Lean_MessageData_ofFormat(v___x_2536_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set_tag(v___x_2530_, 7);
lean_ctor_set(v___x_2530_, 1, v___x_2537_);
lean_ctor_set(v___x_2530_, 0, v___x_2534_);
v___x_2539_ = v___x_2530_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2541_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2542_;
}
}
else
{
lean_object* v___x_2544_; size_t v___x_2545_; size_t v___x_2546_; uint8_t v___x_2547_; 
lean_del_object(v___x_2530_);
v___x_2544_ = l_BitVec_toInt(v_w_2527_, v_bv_2528_);
lean_dec(v_w_2527_);
v___x_2545_ = lean_isize_of_int(v___x_2544_);
lean_dec(v___x_2544_);
v___x_2546_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52);
v___x_2547_ = lean_isize_dec_le(v___x_2546_, v___x_2545_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56);
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58);
v___x_2550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61);
v___x_2551_ = lean_isize_to_int(v___x_2545_);
v___x_2552_ = lean_int_neg(v___x_2551_);
lean_dec(v___x_2551_);
v___x_2553_ = l_Int_toNat(v___x_2552_);
lean_dec(v___x_2552_);
v___x_2554_ = l_Lean_instToExprISize_mkNat(v___x_2553_);
v___x_2555_ = l_Lean_mkApp3(v___x_2548_, v___x_2549_, v___x_2550_, v___x_2554_);
v___y_2455_ = v___x_2555_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = lean_isize_to_int(v___x_2545_);
v___x_2557_ = l_Int_toNat(v___x_2556_);
lean_dec(v___x_2556_);
v___x_2558_ = l_Lean_instToExprISize_mkNat(v___x_2557_);
v___y_2455_ = v___x_2558_;
goto v___jp_2454_;
}
}
}
}
}
else
{
lean_object* v_w_2560_; lean_object* v_bv_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v___x_2458_);
lean_dec_ref(v_var_2312_);
v_w_2560_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2561_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2563_ = v_value_2313_;
v_isShared_2564_ = v_isSharedCheck_2592_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_bv_2561_);
lean_inc(v_w_2560_);
lean_dec(v_value_2313_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2592_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2565_ = lean_unsigned_to_nat(64u);
v___x_2566_ = lean_nat_dec_eq(v_w_2560_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_dec(v_bv_2561_);
lean_dec_ref(v_arg_2449_);
v___x_2567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__63, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__63_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__63);
v___x_2568_ = l_Nat_reprFast(v_w_2560_);
v___x_2569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
v___x_2570_ = l_Lean_MessageData_ofFormat(v___x_2569_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 7);
lean_ctor_set(v___x_2563_, 1, v___x_2570_);
lean_ctor_set(v___x_2563_, 0, v___x_2567_);
v___x_2572_ = v___x_2563_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2574_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2575_;
}
}
else
{
lean_object* v___x_2577_; size_t v___x_2578_; size_t v___x_2579_; uint8_t v___x_2580_; 
lean_del_object(v___x_2563_);
v___x_2577_ = l_BitVec_toInt(v_w_2560_, v_bv_2561_);
lean_dec(v_w_2560_);
v___x_2578_ = lean_isize_of_int(v___x_2577_);
lean_dec(v___x_2577_);
v___x_2579_ = lean_usize_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__52);
v___x_2580_ = lean_isize_dec_le(v___x_2579_, v___x_2578_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2581_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56);
v___x_2582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__58);
v___x_2583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__61);
v___x_2584_ = lean_isize_to_int(v___x_2578_);
v___x_2585_ = lean_int_neg(v___x_2584_);
lean_dec(v___x_2584_);
v___x_2586_ = l_Int_toNat(v___x_2585_);
lean_dec(v___x_2585_);
v___x_2587_ = l_Lean_instToExprISize_mkNat(v___x_2586_);
v___x_2588_ = l_Lean_mkApp3(v___x_2581_, v___x_2582_, v___x_2583_, v___x_2587_);
v___y_2451_ = v___x_2588_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_isize_to_int(v___x_2578_);
v___x_2590_ = l_Int_toNat(v___x_2589_);
lean_dec(v___x_2589_);
v___x_2591_ = l_Lean_instToExprISize_mkNat(v___x_2590_);
v___y_2451_ = v___x_2591_;
goto v___jp_2450_;
}
}
}
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_arg_2449_);
lean_ctor_set(v___x_2452_, 1, v___y_2451_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_arg_2449_);
lean_ctor_set(v___x_2456_, 1, v___y_2455_);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
}
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v___x_2593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__69));
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = l_Lean_Expr_isAppOfArity(v_arg_2406_, v___x_2593_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v_w_2596_; lean_object* v_bv_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v_w_2596_ = lean_ctor_get(v_value_2313_, 0);
lean_inc(v_w_2596_);
v_bv_2597_ = lean_ctor_get(v_value_2313_, 1);
lean_inc(v_bv_2597_);
lean_dec_ref(v_value_2313_);
v___x_2598_ = l_BitVec_ofNat(v_w_2596_, v___x_2594_);
lean_dec(v_w_2596_);
v___x_2599_ = lean_nat_dec_eq(v_bv_2597_, v___x_2598_);
lean_dec(v___x_2598_);
lean_dec(v_bv_2597_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__72);
v___y_2426_ = v___x_2600_;
goto v___jp_2425_;
}
else
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__75, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__75_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__75);
v___y_2426_ = v___x_2601_;
goto v___jp_2425_;
}
}
else
{
lean_object* v_w_2602_; lean_object* v_bv_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2620_; 
v_w_2602_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2603_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2605_ = v_value_2313_;
v_isShared_2606_ = v_isSharedCheck_2620_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_bv_2603_);
lean_inc(v_w_2602_);
lean_dec(v_value_2313_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2620_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___y_2609_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2607_ = l_Lean_Expr_appArg_x21(v_arg_2406_);
lean_dec_ref(v_arg_2406_);
v___x_2616_ = l_BitVec_ofNat(v_w_2602_, v___x_2594_);
lean_dec(v_w_2602_);
v___x_2617_ = lean_nat_dec_eq(v_bv_2603_, v___x_2616_);
lean_dec(v___x_2616_);
lean_dec(v_bv_2603_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__77));
v___y_2609_ = v___x_2618_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__79));
v___y_2609_ = v___x_2619_;
goto v___jp_2608_;
}
v___jp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2610_ = lean_box(0);
lean_inc(v___y_2609_);
v___x_2611_ = l_Lean_mkConst(v___y_2609_, v___x_2610_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 1, v___x_2611_);
lean_ctor_set(v___x_2605_, 0, v___x_2607_);
v___x_2613_ = v___x_2605_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
}
}
}
}
else
{
lean_object* v_w_2621_; lean_object* v_bv_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2621_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2622_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2624_ = v_value_2313_;
v_isShared_2625_ = v_isSharedCheck_2650_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_bv_2622_);
lean_inc(v_w_2621_);
lean_dec(v_value_2313_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2650_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_unsigned_to_nat(8u);
v___x_2627_ = lean_nat_dec_eq(v_w_2621_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_dec(v_bv_2622_);
lean_dec_ref(v_arg_2406_);
v___x_2628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__81, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__81_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__81);
v___x_2629_ = l_Nat_reprFast(v_w_2621_);
v___x_2630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = l_Lean_MessageData_ofFormat(v___x_2630_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 7);
lean_ctor_set(v___x_2624_, 1, v___x_2631_);
lean_ctor_set(v___x_2624_, 0, v___x_2628_);
v___x_2633_ = v___x_2624_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2635_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2636_;
}
}
else
{
uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v_r_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec(v_w_2621_);
v___x_2638_ = lean_uint8_of_nat_mk(v_bv_2622_);
v___x_2639_ = lean_uint8_to_nat(v___x_2638_);
v_r_2640_ = l_Lean_mkRawNatLit(v___x_2639_);
v___x_2641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42);
v___x_2642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__83, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__83_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__83);
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__85, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__85_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__85);
lean_inc_ref(v_r_2640_);
v___x_2644_ = l_Lean_Expr_app___override(v___x_2643_, v_r_2640_);
v___x_2645_ = l_Lean_mkApp3(v___x_2641_, v___x_2642_, v_r_2640_, v___x_2644_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v___x_2645_);
lean_ctor_set(v___x_2624_, 0, v_arg_2406_);
v___x_2647_ = v___x_2624_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_arg_2406_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
}
}
}
}
else
{
lean_object* v_w_2651_; lean_object* v_bv_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2651_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2652_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2654_ = v_value_2313_;
v_isShared_2655_ = v_isSharedCheck_2680_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_bv_2652_);
lean_inc(v_w_2651_);
lean_dec(v_value_2313_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2680_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = lean_unsigned_to_nat(16u);
v___x_2657_ = lean_nat_dec_eq(v_w_2651_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
lean_dec(v_bv_2652_);
lean_dec_ref(v_arg_2406_);
v___x_2658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__87, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__87_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__87);
v___x_2659_ = l_Nat_reprFast(v_w_2651_);
v___x_2660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
v___x_2661_ = l_Lean_MessageData_ofFormat(v___x_2660_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 7);
lean_ctor_set(v___x_2654_, 1, v___x_2661_);
lean_ctor_set(v___x_2654_, 0, v___x_2658_);
v___x_2663_ = v___x_2654_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2665_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2666_;
}
}
else
{
uint16_t v___x_2668_; lean_object* v___x_2669_; lean_object* v_r_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
lean_dec(v_w_2651_);
v___x_2668_ = lean_uint16_of_nat_mk(v_bv_2652_);
v___x_2669_ = lean_uint16_to_nat(v___x_2668_);
v_r_2670_ = l_Lean_mkRawNatLit(v___x_2669_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42);
v___x_2672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__89, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__89_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__89);
v___x_2673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__91, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__91_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__91);
lean_inc_ref(v_r_2670_);
v___x_2674_ = l_Lean_Expr_app___override(v___x_2673_, v_r_2670_);
v___x_2675_ = l_Lean_mkApp3(v___x_2671_, v___x_2672_, v_r_2670_, v___x_2674_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v___x_2675_);
lean_ctor_set(v___x_2654_, 0, v_arg_2406_);
v___x_2677_ = v___x_2654_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_arg_2406_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
}
}
}
else
{
lean_object* v_w_2681_; lean_object* v_bv_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2681_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2682_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2684_ = v_value_2313_;
v_isShared_2685_ = v_isSharedCheck_2710_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_bv_2682_);
lean_inc(v_w_2681_);
lean_dec(v_value_2313_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2710_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = lean_unsigned_to_nat(32u);
v___x_2687_ = lean_nat_dec_eq(v_w_2681_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
lean_dec(v_bv_2682_);
lean_dec_ref(v_arg_2406_);
v___x_2688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__93, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__93_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__93);
v___x_2689_ = l_Nat_reprFast(v_w_2681_);
v___x_2690_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
v___x_2691_ = l_Lean_MessageData_ofFormat(v___x_2690_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 7);
lean_ctor_set(v___x_2684_, 1, v___x_2691_);
lean_ctor_set(v___x_2684_, 0, v___x_2688_);
v___x_2693_ = v___x_2684_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2695_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2696_;
}
}
else
{
uint32_t v___x_2698_; lean_object* v___x_2699_; lean_object* v_r_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
lean_dec(v_w_2681_);
v___x_2698_ = lean_uint32_of_nat_mk(v_bv_2682_);
v___x_2699_ = lean_uint32_to_nat(v___x_2698_);
v_r_2700_ = l_Lean_mkRawNatLit(v___x_2699_);
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42);
v___x_2702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__95, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__95_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__95);
v___x_2703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__97, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__97_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__97);
lean_inc_ref(v_r_2700_);
v___x_2704_ = l_Lean_Expr_app___override(v___x_2703_, v_r_2700_);
v___x_2705_ = l_Lean_mkApp3(v___x_2701_, v___x_2702_, v_r_2700_, v___x_2704_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 1, v___x_2705_);
lean_ctor_set(v___x_2684_, 0, v_arg_2406_);
v___x_2707_ = v___x_2684_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_arg_2406_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
}
}
else
{
lean_object* v_w_2711_; lean_object* v_bv_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2711_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2712_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2714_ = v_value_2313_;
v_isShared_2715_ = v_isSharedCheck_2740_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_bv_2712_);
lean_inc(v_w_2711_);
lean_dec(v_value_2313_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2740_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = lean_unsigned_to_nat(64u);
v___x_2717_ = lean_nat_dec_eq(v_w_2711_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
lean_dec(v_bv_2712_);
lean_dec_ref(v_arg_2406_);
v___x_2718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__99, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__99_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__99);
v___x_2719_ = l_Nat_reprFast(v_w_2711_);
v___x_2720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
v___x_2721_ = l_Lean_MessageData_ofFormat(v___x_2720_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 7);
lean_ctor_set(v___x_2714_, 1, v___x_2721_);
lean_ctor_set(v___x_2714_, 0, v___x_2718_);
v___x_2723_ = v___x_2714_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2725_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2726_;
}
}
else
{
uint64_t v___x_2728_; lean_object* v___x_2729_; lean_object* v_r_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_dec(v_w_2711_);
v___x_2728_ = lean_uint64_of_nat_mk(v_bv_2712_);
v___x_2729_ = lean_uint64_to_nat(v___x_2728_);
v_r_2730_ = l_Lean_mkRawNatLit(v___x_2729_);
v___x_2731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__42);
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__101, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__101_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__101);
v___x_2733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__103, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__103_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__103);
lean_inc_ref(v_r_2730_);
v___x_2734_ = l_Lean_Expr_app___override(v___x_2733_, v_r_2730_);
v___x_2735_ = l_Lean_mkApp3(v___x_2731_, v___x_2732_, v_r_2730_, v___x_2734_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v___x_2735_);
lean_ctor_set(v___x_2714_, 0, v_arg_2406_);
v___x_2737_ = v___x_2714_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_arg_2406_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
return v___x_2738_;
}
}
}
}
}
else
{
lean_object* v_w_2741_; lean_object* v_bv_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2741_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2742_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2744_ = v_value_2313_;
v_isShared_2745_ = v_isSharedCheck_2772_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_bv_2742_);
lean_inc(v_w_2741_);
lean_dec(v_value_2313_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2772_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = lean_unsigned_to_nat(8u);
v___x_2747_ = lean_nat_dec_eq(v_w_2741_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
lean_dec(v_bv_2742_);
lean_dec_ref(v_arg_2406_);
v___x_2748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__105, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__105_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__105);
v___x_2749_ = l_Nat_reprFast(v_w_2741_);
v___x_2750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
v___x_2751_ = l_Lean_MessageData_ofFormat(v___x_2750_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 7);
lean_ctor_set(v___x_2744_, 1, v___x_2751_);
lean_ctor_set(v___x_2744_, 0, v___x_2748_);
v___x_2753_ = v___x_2744_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2755_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2756_;
}
}
else
{
uint8_t v___x_2758_; uint8_t v___x_2759_; uint8_t v___x_2760_; 
lean_del_object(v___x_2744_);
lean_dec(v_w_2741_);
v___x_2758_ = lean_uint8_of_nat_mk(v_bv_2742_);
v___x_2759_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__106, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__106_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__106);
v___x_2760_ = lean_int8_dec_le(v___x_2759_, v___x_2758_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56);
v___x_2762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__108, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__108_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__108);
v___x_2763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__110, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__110_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__110);
v___x_2764_ = lean_int8_to_int(v___x_2758_);
v___x_2765_ = lean_int_neg(v___x_2764_);
v___x_2766_ = l_Int_toNat(v___x_2765_);
lean_dec(v___x_2765_);
v___x_2767_ = l_Lean_instToExprInt8_mkNat(v___x_2766_);
v___x_2768_ = l_Lean_mkApp3(v___x_2761_, v___x_2762_, v___x_2763_, v___x_2767_);
v___y_2422_ = v___x_2768_;
goto v___jp_2421_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = lean_int8_to_int(v___x_2758_);
v___x_2770_ = l_Int_toNat(v___x_2769_);
v___x_2771_ = l_Lean_instToExprInt8_mkNat(v___x_2770_);
v___y_2422_ = v___x_2771_;
goto v___jp_2421_;
}
}
}
}
}
else
{
lean_object* v_w_2773_; lean_object* v_bv_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2804_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2773_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2774_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2776_ = v_value_2313_;
v_isShared_2777_ = v_isSharedCheck_2804_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_bv_2774_);
lean_inc(v_w_2773_);
lean_dec(v_value_2313_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2804_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = lean_unsigned_to_nat(16u);
v___x_2779_ = lean_nat_dec_eq(v_w_2773_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_dec(v_bv_2774_);
lean_dec_ref(v_arg_2406_);
v___x_2780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__112, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__112_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__112);
v___x_2781_ = l_Nat_reprFast(v_w_2773_);
v___x_2782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
v___x_2783_ = l_Lean_MessageData_ofFormat(v___x_2782_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 7);
lean_ctor_set(v___x_2776_, 1, v___x_2783_);
lean_ctor_set(v___x_2776_, 0, v___x_2780_);
v___x_2785_ = v___x_2776_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2787_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2788_;
}
}
else
{
uint16_t v___x_2790_; uint16_t v___x_2791_; uint8_t v___x_2792_; 
lean_del_object(v___x_2776_);
lean_dec(v_w_2773_);
v___x_2790_ = lean_uint16_of_nat_mk(v_bv_2774_);
v___x_2791_ = lean_uint16_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__113, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__113_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__113);
v___x_2792_ = lean_int16_dec_le(v___x_2791_, v___x_2790_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56);
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__115, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__115_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__115);
v___x_2795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__117, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__117_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__117);
v___x_2796_ = lean_int16_to_int(v___x_2790_);
v___x_2797_ = lean_int_neg(v___x_2796_);
v___x_2798_ = l_Int_toNat(v___x_2797_);
lean_dec(v___x_2797_);
v___x_2799_ = l_Lean_instToExprInt16_mkNat(v___x_2798_);
v___x_2800_ = l_Lean_mkApp3(v___x_2793_, v___x_2794_, v___x_2795_, v___x_2799_);
v___y_2418_ = v___x_2800_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_int16_to_int(v___x_2790_);
v___x_2802_ = l_Int_toNat(v___x_2801_);
v___x_2803_ = l_Lean_instToExprInt16_mkNat(v___x_2802_);
v___y_2418_ = v___x_2803_;
goto v___jp_2417_;
}
}
}
}
}
else
{
lean_object* v_w_2805_; lean_object* v_bv_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2805_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2806_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2808_ = v_value_2313_;
v_isShared_2809_ = v_isSharedCheck_2836_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_bv_2806_);
lean_inc(v_w_2805_);
lean_dec(v_value_2313_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2836_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = lean_unsigned_to_nat(32u);
v___x_2811_ = lean_nat_dec_eq(v_w_2805_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec(v_bv_2806_);
lean_dec_ref(v_arg_2406_);
v___x_2812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__119, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__119_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__119);
v___x_2813_ = l_Nat_reprFast(v_w_2805_);
v___x_2814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
v___x_2815_ = l_Lean_MessageData_ofFormat(v___x_2814_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 7);
lean_ctor_set(v___x_2808_, 1, v___x_2815_);
lean_ctor_set(v___x_2808_, 0, v___x_2812_);
v___x_2817_ = v___x_2808_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2819_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2820_;
}
}
else
{
uint32_t v___x_2822_; uint32_t v___x_2823_; uint8_t v___x_2824_; 
lean_del_object(v___x_2808_);
lean_dec(v_w_2805_);
v___x_2822_ = lean_uint32_of_nat_mk(v_bv_2806_);
v___x_2823_ = lean_uint32_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__120, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__120_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__120);
v___x_2824_ = lean_int32_dec_le(v___x_2823_, v___x_2822_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56);
v___x_2826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__122, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__122_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__122);
v___x_2827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__124, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__124_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__124);
v___x_2828_ = lean_int32_to_int(v___x_2822_);
v___x_2829_ = lean_int_neg(v___x_2828_);
lean_dec(v___x_2828_);
v___x_2830_ = l_Int_toNat(v___x_2829_);
lean_dec(v___x_2829_);
v___x_2831_ = l_Lean_instToExprInt32_mkNat(v___x_2830_);
v___x_2832_ = l_Lean_mkApp3(v___x_2825_, v___x_2826_, v___x_2827_, v___x_2831_);
v___y_2414_ = v___x_2832_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = lean_int32_to_int(v___x_2822_);
v___x_2834_ = l_Int_toNat(v___x_2833_);
lean_dec(v___x_2833_);
v___x_2835_ = l_Lean_instToExprInt32_mkNat(v___x_2834_);
v___y_2414_ = v___x_2835_;
goto v___jp_2413_;
}
}
}
}
}
else
{
lean_object* v_w_2837_; lean_object* v_bv_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_var_2312_);
v_w_2837_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2838_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2840_ = v_value_2313_;
v_isShared_2841_ = v_isSharedCheck_2868_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_bv_2838_);
lean_inc(v_w_2837_);
lean_dec(v_value_2313_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2868_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = lean_unsigned_to_nat(64u);
v___x_2843_ = lean_nat_dec_eq(v_w_2837_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
lean_dec(v_bv_2838_);
lean_dec_ref(v_arg_2406_);
lean_del_object(v___x_2402_);
v___x_2844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__126, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__126_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__126);
v___x_2845_ = l_Nat_reprFast(v_w_2837_);
v___x_2846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
v___x_2847_ = l_Lean_MessageData_ofFormat(v___x_2846_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 7);
lean_ctor_set(v___x_2840_, 1, v___x_2847_);
lean_ctor_set(v___x_2840_, 0, v___x_2844_);
v___x_2849_ = v___x_2840_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__37);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_2851_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2852_;
}
}
else
{
uint64_t v___x_2854_; uint64_t v___x_2855_; uint8_t v___x_2856_; 
lean_del_object(v___x_2840_);
lean_dec(v_w_2837_);
v___x_2854_ = lean_uint64_of_nat_mk(v_bv_2838_);
v___x_2855_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__127, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__127_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__127);
v___x_2856_ = lean_int64_dec_le(v___x_2855_, v___x_2854_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__56);
v___x_2858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__129, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__129_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__129);
v___x_2859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__131, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__131_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__131);
v___x_2860_ = lean_int64_to_int_sint(v___x_2854_);
v___x_2861_ = lean_int_neg(v___x_2860_);
lean_dec(v___x_2860_);
v___x_2862_ = l_Int_toNat(v___x_2861_);
lean_dec(v___x_2861_);
v___x_2863_ = l_Lean_instToExprInt64_mkNat(v___x_2862_);
v___x_2864_ = l_Lean_mkApp3(v___x_2857_, v___x_2858_, v___x_2859_, v___x_2863_);
v___y_2408_ = v___x_2864_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_int64_to_int_sint(v___x_2854_);
v___x_2866_ = l_Int_toNat(v___x_2865_);
lean_dec(v___x_2865_);
v___x_2867_ = l_Lean_instToExprInt64_mkNat(v___x_2866_);
v___y_2408_ = v___x_2867_;
goto v___jp_2407_;
}
}
}
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_arg_2406_);
lean_ctor_set(v___x_2409_, 1, v___y_2408_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2409_);
v___x_2411_ = v___x_2402_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
v___jp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_arg_2406_);
lean_ctor_set(v___x_2415_, 1, v___y_2414_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
v___jp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_arg_2406_);
lean_ctor_set(v___x_2419_, 1, v___y_2418_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
v___jp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_arg_2406_);
lean_ctor_set(v___x_2423_, 1, v___y_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
v___jp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_inc_ref(v___y_2426_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_arg_2406_);
lean_ctor_set(v___x_2427_, 1, v___y_2426_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v_value_2313_);
lean_dec_ref(v_var_2312_);
v_a_2870_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2399_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2399_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
v___jp_2338_:
{
if (lean_obj_tag(v_var_2312_) == 5)
{
lean_object* v_fn_2345_; 
v_fn_2345_ = lean_ctor_get(v_var_2312_, 0);
if (lean_obj_tag(v_fn_2345_) == 4)
{
lean_object* v_arg_2346_; lean_object* v_declName_2347_; lean_object* v_us_2348_; lean_object* v___x_2349_; lean_object* v_env_2350_; lean_object* v___x_2351_; 
v_arg_2346_ = lean_ctor_get(v_var_2312_, 1);
v_declName_2347_ = lean_ctor_get(v_fn_2345_, 0);
v_us_2348_ = lean_ctor_get(v_fn_2345_, 1);
v___x_2349_ = lean_st_ref_get(v___y_2344_);
v_env_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc_ref(v_env_2350_);
lean_dec(v___x_2349_);
lean_inc(v_declName_2347_);
v___x_2351_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecType_x3f(v_env_2350_, v_declName_2347_);
if (lean_obj_tag(v___x_2351_) == 1)
{
lean_object* v_val_2352_; lean_object* v___x_2353_; 
lean_inc(v_us_2348_);
lean_inc_ref(v_arg_2346_);
lean_dec_ref_known(v_var_2312_, 2);
v_val_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0(v_val_2352_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2376_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2376_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2376_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
if (lean_obj_tag(v_a_2354_) == 5)
{
lean_object* v_val_2358_; lean_object* v_ctors_2359_; lean_object* v_bv_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2372_; 
v_val_2358_ = lean_ctor_get(v_a_2354_, 0);
lean_inc_ref(v_val_2358_);
lean_dec_ref_known(v_a_2354_, 1);
v_ctors_2359_ = lean_ctor_get(v_val_2358_, 4);
lean_inc(v_ctors_2359_);
lean_dec_ref(v_val_2358_);
v_bv_2360_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v_value_2313_, 0);
lean_dec(v_unused_2373_);
v___x_2362_ = v_value_2313_;
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_bv_2360_);
lean_dec(v_value_2313_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2364_ = l_List_get_x21Internal___redArg(v___x_2337_, v_ctors_2359_, v_bv_2360_);
lean_dec(v_ctors_2359_);
v___x_2365_ = l_Lean_mkConst(v___x_2364_, v_us_2348_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2365_);
lean_ctor_set(v___x_2362_, 0, v_arg_2346_);
v___x_2367_ = v___x_2362_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_arg_2346_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2367_);
v___x_2369_ = v___x_2356_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_del_object(v___x_2356_);
lean_dec(v_a_2354_);
lean_dec(v_us_2348_);
lean_dec_ref(v_arg_2346_);
lean_dec_ref(v_value_2313_);
v___x_2374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__6);
v___x_2375_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__1(v___x_2374_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_us_2348_);
lean_dec_ref(v_arg_2346_);
lean_dec_ref(v_value_2313_);
v_a_2377_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2353_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2353_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_w_2385_; lean_object* v_bv_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v___x_2351_);
v_w_2385_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2386_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2388_ = v_value_2313_;
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_bv_2386_);
lean_inc(v_w_2385_);
lean_dec(v_value_2313_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3);
v___x_2391_ = l_Lean_mkNatLit(v_w_2385_);
v___x_2392_ = l_Lean_mkNatLit(v_bv_2386_);
v___x_2393_ = l_Lean_mkAppB(v___x_2390_, v___x_2391_, v___x_2392_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_2393_);
lean_ctor_set(v___x_2388_, 0, v_var_2312_);
v___x_2395_ = v___x_2388_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_var_2312_);
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
else
{
goto v___jp_2321_;
}
}
else
{
goto v___jp_2321_;
}
}
}
else
{
lean_object* v_w_2878_; lean_object* v_bv_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2891_; 
v_w_2878_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2879_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2881_ = v_value_2313_;
v_isShared_2882_ = v_isSharedCheck_2891_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_bv_2879_);
lean_inc(v_w_2878_);
lean_dec(v_value_2313_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2891_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3);
v___x_2884_ = l_Lean_mkNatLit(v_w_2878_);
v___x_2885_ = l_Lean_mkNatLit(v_bv_2879_);
v___x_2886_ = l_Lean_mkAppB(v___x_2883_, v___x_2884_, v___x_2885_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2886_);
lean_ctor_set(v___x_2881_, 0, v_var_2312_);
v___x_2888_ = v___x_2881_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_var_2312_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
}
v___jp_2321_:
{
lean_object* v_w_2322_; lean_object* v_bv_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2335_; 
v_w_2322_ = lean_ctor_get(v_value_2313_, 0);
v_bv_2323_ = lean_ctor_get(v_value_2313_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_value_2313_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2325_ = v_value_2313_;
v_isShared_2326_ = v_isSharedCheck_2335_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_bv_2323_);
lean_inc(v_w_2322_);
lean_dec(v_value_2313_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2335_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__3);
v___x_2328_ = l_Lean_mkNatLit(v_w_2322_);
v___x_2329_ = l_Lean_mkNatLit(v_bv_2323_);
v___x_2330_ = l_Lean_mkAppB(v___x_2327_, v___x_2328_, v___x_2329_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v___x_2330_);
lean_ctor_set(v___x_2325_, 0, v_var_2312_);
v___x_2332_ = v___x_2325_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_var_2312_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___boxed(lean_object* v_var_2892_, lean_object* v_value_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation(v_var_2892_, v_value_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2(lean_object* v_00_u03b1_2902_, lean_object* v_msg_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v_msg_2903_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___boxed(lean_object* v_00_u03b1_2912_, lean_object* v_msg_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2(v_00_u03b1_2912_, v_msg_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0(lean_object* v_00_u03b1_2922_, lean_object* v_constName_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___redArg(v_constName_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_constName_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0(v_00_u03b1_2932_, v_constName_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2942_, lean_object* v_ref_2943_, lean_object* v_constName_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___redArg(v_ref_2943_, v_constName_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2953_, lean_object* v_ref_2954_, lean_object* v_constName_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2(v_00_u03b1_2953_, v_ref_2954_, v_constName_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_ref_2954_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_2964_, lean_object* v_ref_2965_, lean_object* v_msg_2966_, lean_object* v_declHint_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_2965_, v_msg_2966_, v_declHint_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2976_, lean_object* v_ref_2977_, lean_object* v_msg_2978_, lean_object* v_declHint_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_2976_, v_ref_2977_, v_msg_2978_, v_declHint_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v_ref_2977_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(lean_object* v_msg_2988_, lean_object* v_declHint_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_2988_, v_declHint_2989_, v___y_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2998_, lean_object* v_declHint_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_2998_, v_declHint_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_3008_, lean_object* v_ref_3009_, lean_object* v_msg_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_3009_, v_msg_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3019_, lean_object* v_ref_3020_, lean_object* v_msg_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_3019_, v_ref_3020_, v_msg_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v_ref_3020_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f(lean_object* v_e_3039_){
_start:
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = l_Lean_Expr_cleanupAnnotations(v_e_3039_);
v___x_3041_ = l_Lean_Expr_isApp(v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
lean_dec_ref(v___x_3040_);
v___x_3042_ = lean_box(0);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3040_);
v___x_3044_ = l_Lean_Expr_isApp(v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
lean_dec_ref(v___x_3043_);
lean_dec_ref(v___x_3040_);
v___x_3045_ = lean_box(0);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3043_);
lean_dec_ref(v___x_3043_);
v___x_3047_ = l_Lean_Expr_isApp(v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
lean_dec_ref(v___x_3046_);
lean_dec_ref(v___x_3040_);
v___x_3048_ = lean_box(0);
return v___x_3048_;
}
else
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3046_);
lean_dec_ref(v___x_3046_);
v___x_3050_ = l_Lean_Expr_isApp(v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec_ref(v___x_3049_);
lean_dec_ref(v___x_3040_);
v___x_3051_ = lean_box(0);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3049_);
lean_dec_ref(v___x_3049_);
v___x_3053_ = l_Lean_Expr_isApp(v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3040_);
v___x_3054_ = lean_box(0);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3052_);
v___x_3056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___closed__2));
v___x_3057_ = l_Lean_Expr_isConstOf(v___x_3055_, v___x_3056_);
lean_dec_ref(v___x_3055_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3040_);
v___x_3058_ = lean_box(0);
return v___x_3058_;
}
else
{
lean_object* v_arg_3059_; lean_object* v_arg_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_arg_3059_ = lean_ctor_get(v___x_3040_, 1);
lean_inc_ref(v_arg_3059_);
lean_dec_ref(v___x_3040_);
v_arg_3060_ = lean_ctor_get(v___x_3052_, 1);
lean_inc_ref(v_arg_3060_);
lean_dec_ref(v___x_3052_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_arg_3060_);
lean_ctor_set(v___x_3061_, 1, v_arg_3059_);
v___x_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f___boxed(lean_object* v_e_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f(v_e_3063_);
lean_dec_ref(v_e_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__0___redArg(lean_object* v_a_3065_, lean_object* v_b_3066_){
_start:
{
lean_object* v_array_3067_; lean_object* v_start_3068_; lean_object* v_stop_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3082_; 
v_array_3067_ = lean_ctor_get(v_a_3065_, 0);
v_start_3068_ = lean_ctor_get(v_a_3065_, 1);
v_stop_3069_ = lean_ctor_get(v_a_3065_, 2);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_a_3065_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3071_ = v_a_3065_;
v_isShared_3072_ = v_isSharedCheck_3082_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_stop_3069_);
lean_inc(v_start_3068_);
lean_inc(v_array_3067_);
lean_dec(v_a_3065_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3082_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_nat_dec_lt(v_start_3068_, v_stop_3069_);
if (v___x_3073_ == 0)
{
lean_del_object(v___x_3071_);
lean_dec(v_stop_3069_);
lean_dec(v_start_3068_);
lean_dec_ref(v_array_3067_);
return v_b_3066_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_nat_add(v_start_3068_, v___x_3074_);
lean_inc_ref(v_array_3067_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v___x_3075_);
v___x_3077_ = v___x_3071_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_array_3067_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_stop_3069_);
v___x_3077_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_array_fget(v_array_3067_, v_start_3068_);
lean_dec(v_start_3068_);
lean_dec_ref(v_array_3067_);
v___x_3079_ = lean_array_push(v_b_3066_, v___x_3078_);
v_a_3065_ = v___x_3077_;
v_b_3066_ = v___x_3079_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg(lean_object* v_a_3083_, lean_object* v_x_3084_){
_start:
{
if (lean_obj_tag(v_x_3084_) == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_box(0);
return v___x_3085_;
}
else
{
lean_object* v_key_3086_; lean_object* v_value_3087_; lean_object* v_tail_3088_; uint8_t v___x_3089_; 
v_key_3086_ = lean_ctor_get(v_x_3084_, 0);
v_value_3087_ = lean_ctor_get(v_x_3084_, 1);
v_tail_3088_ = lean_ctor_get(v_x_3084_, 2);
v___x_3089_ = lean_name_eq(v_key_3086_, v_a_3083_);
if (v___x_3089_ == 0)
{
v_x_3084_ = v_tail_3088_;
goto _start;
}
else
{
lean_object* v___x_3091_; 
lean_inc(v_value_3087_);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_value_3087_);
return v___x_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_a_3092_, lean_object* v_x_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg(v_a_3092_, v_x_3093_);
lean_dec(v_x_3093_);
lean_dec(v_a_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg(lean_object* v_m_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_buckets_3097_; lean_object* v___x_3098_; uint64_t v___y_3100_; 
v_buckets_3097_ = lean_ctor_get(v_m_3095_, 1);
v___x_3098_ = lean_array_get_size(v_buckets_3097_);
if (lean_obj_tag(v_a_3096_) == 0)
{
uint64_t v___x_3114_; 
v___x_3114_ = 1723ULL;
v___y_3100_ = v___x_3114_;
goto v___jp_3099_;
}
else
{
uint64_t v_hash_3115_; 
v_hash_3115_ = lean_ctor_get_uint64(v_a_3096_, sizeof(void*)*2);
v___y_3100_ = v_hash_3115_;
goto v___jp_3099_;
}
v___jp_3099_:
{
uint64_t v___x_3101_; uint64_t v___x_3102_; uint64_t v_fold_3103_; uint64_t v___x_3104_; uint64_t v___x_3105_; uint64_t v___x_3106_; size_t v___x_3107_; size_t v___x_3108_; size_t v___x_3109_; size_t v___x_3110_; size_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3101_ = 32ULL;
v___x_3102_ = lean_uint64_shift_right(v___y_3100_, v___x_3101_);
v_fold_3103_ = lean_uint64_xor(v___y_3100_, v___x_3102_);
v___x_3104_ = 16ULL;
v___x_3105_ = lean_uint64_shift_right(v_fold_3103_, v___x_3104_);
v___x_3106_ = lean_uint64_xor(v_fold_3103_, v___x_3105_);
v___x_3107_ = lean_uint64_to_usize(v___x_3106_);
v___x_3108_ = lean_usize_of_nat(v___x_3098_);
v___x_3109_ = ((size_t)1ULL);
v___x_3110_ = lean_usize_sub(v___x_3108_, v___x_3109_);
v___x_3111_ = lean_usize_land(v___x_3107_, v___x_3110_);
v___x_3112_ = lean_array_uget_borrowed(v_buckets_3097_, v___x_3111_);
v___x_3113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg(v_a_3096_, v___x_3112_);
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg___boxed(lean_object* v_m_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg(v_m_3116_, v_a_3117_);
lean_dec(v_a_3117_);
lean_dec_ref(v_m_3116_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__1(size_t v_sz_3119_, size_t v_i_3120_, lean_object* v_bs_3121_){
_start:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_usize_dec_lt(v_i_3120_, v_sz_3119_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3123_, 0, v_bs_3121_);
return v___x_3123_;
}
else
{
lean_object* v_v_3124_; lean_object* v___x_3125_; 
v_v_3124_ = lean_array_uget_borrowed(v_bs_3121_, v_i_3120_);
v___x_3125_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f(v_v_3124_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v___x_3126_; 
lean_dec_ref(v_bs_3121_);
v___x_3126_ = lean_box(0);
return v___x_3126_;
}
else
{
lean_object* v_val_3127_; lean_object* v_snd_3128_; lean_object* v___x_3129_; lean_object* v_bs_x27_3130_; size_t v___x_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v_val_3127_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3125_, 1);
v_snd_3128_ = lean_ctor_get(v_val_3127_, 1);
lean_inc(v_snd_3128_);
lean_dec(v_val_3127_);
v___x_3129_ = lean_unsigned_to_nat(0u);
v_bs_x27_3130_ = lean_array_uset(v_bs_3121_, v_i_3120_, v___x_3129_);
v___x_3131_ = ((size_t)1ULL);
v___x_3132_ = lean_usize_add(v_i_3120_, v___x_3131_);
v___x_3133_ = lean_array_uset(v_bs_x27_3130_, v_i_3120_, v_snd_3128_);
v_i_3120_ = v___x_3132_;
v_bs_3121_ = v___x_3133_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__1___boxed(lean_object* v_sz_3135_, lean_object* v_i_3136_, lean_object* v_bs_3137_){
_start:
{
size_t v_sz_boxed_3138_; size_t v_i_boxed_3139_; lean_object* v_res_3140_; 
v_sz_boxed_3138_ = lean_unbox_usize(v_sz_3135_);
lean_dec(v_sz_3135_);
v_i_boxed_3139_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__1(v_sz_boxed_3138_, v_i_boxed_3139_, v_bs_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3(lean_object* v_x_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
if (lean_obj_tag(v_x_3143_) == 5)
{
lean_object* v_fn_3146_; lean_object* v_arg_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_fn_3146_ = lean_ctor_get(v_x_3143_, 0);
lean_inc_ref(v_fn_3146_);
v_arg_3147_ = lean_ctor_get(v_x_3143_, 1);
lean_inc_ref(v_arg_3147_);
lean_dec_ref_known(v_x_3143_, 2);
v___x_3148_ = lean_array_set(v_x_3144_, v_x_3145_, v_arg_3147_);
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = lean_nat_sub(v_x_3145_, v___x_3149_);
lean_dec(v_x_3145_);
v_x_3143_ = v_fn_3146_;
v_x_3144_ = v___x_3148_;
v_x_3145_ = v___x_3150_;
goto _start;
}
else
{
lean_dec(v_x_3145_);
if (lean_obj_tag(v_x_3143_) == 4)
{
lean_object* v_declName_3152_; lean_object* v___x_3153_; lean_object* v___y_3155_; uint8_t v___y_3156_; lean_object* v_lower_3157_; lean_object* v_upper_3158_; lean_object* v_fst_3179_; uint8_t v_snd_3180_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_declName_3152_ = lean_ctor_get(v_x_3143_, 0);
lean_inc(v_declName_3152_);
lean_dec_ref_known(v_x_3143_, 2);
v___x_3153_ = l_Lean_instInhabitedExpr;
v___x_3193_ = l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredPropArity;
v___x_3194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg(v___x_3193_, v_declName_3152_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredBoolArity;
v___x_3196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg(v___x_3195_, v_declName_3152_);
lean_dec(v_declName_3152_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v___x_3197_; 
lean_dec_ref(v_x_3144_);
v___x_3197_ = lean_box(0);
return v___x_3197_;
}
else
{
lean_object* v_val_3198_; uint8_t v___x_3199_; 
v_val_3198_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_val_3198_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3199_ = 1;
v_fst_3179_ = v_val_3198_;
v_snd_3180_ = v___x_3199_;
goto v___jp_3178_;
}
}
else
{
lean_object* v_val_3200_; uint8_t v___x_3201_; 
lean_dec(v_declName_3152_);
v_val_3200_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_val_3200_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3201_ = 0;
v_fst_3179_ = v_val_3200_;
v_snd_3180_ = v___x_3201_;
goto v___jp_3178_;
}
v___jp_3154_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; size_t v_sz_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
lean_inc_ref(v_x_3144_);
v___x_3159_ = l_Array_toSubarray___redArg(v_x_3144_, v_lower_3157_, v_upper_3158_);
v___x_3160_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3___closed__0));
v___x_3161_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__0___redArg(v___x_3159_, v___x_3160_);
v_sz_3162_ = lean_array_size(v___x_3161_);
v___x_3163_ = ((size_t)0ULL);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__1(v_sz_3162_, v___x_3163_, v___x_3161_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v___x_3165_; 
lean_dec(v___y_3155_);
lean_dec_ref(v_x_3144_);
v___x_3165_ = lean_box(0);
return v___x_3165_;
}
else
{
lean_object* v_val_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3177_; 
v_val_3166_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3168_ = v___x_3164_;
v_isShared_3169_ = v_isSharedCheck_3177_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_val_3166_);
lean_dec(v___x_3164_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3177_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3170_ = lean_array_get(v___x_3153_, v_x_3144_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v_x_3144_);
v___x_3171_ = l_Lean_mkAppN(v___x_3170_, v_val_3166_);
lean_dec(v_val_3166_);
v___x_3172_ = lean_box(v___y_3156_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v___x_3173_);
v___x_3175_ = v___x_3168_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
v___jp_3178_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3181_ = lean_array_get_size(v_x_3144_);
v___x_3182_ = lean_unsigned_to_nat(5u);
v___x_3183_ = lean_nat_mul(v___x_3182_, v_fst_3179_);
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = lean_nat_add(v___x_3183_, v___x_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_nat_dec_eq(v___x_3181_, v___x_3185_);
lean_dec(v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_dec(v_fst_3179_);
lean_dec_ref(v_x_3144_);
v___x_3187_ = lean_box(0);
return v___x_3187_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3188_ = lean_unsigned_to_nat(4u);
v___x_3189_ = lean_nat_mul(v___x_3188_, v_fst_3179_);
lean_dec(v_fst_3179_);
v___x_3190_ = lean_nat_add(v___x_3189_, v___x_3184_);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = lean_nat_dec_le(v___x_3190_, v___x_3191_);
if (v___x_3192_ == 0)
{
v___y_3155_ = v___x_3189_;
v___y_3156_ = v_snd_3180_;
v_lower_3157_ = v___x_3190_;
v_upper_3158_ = v___x_3181_;
goto v___jp_3154_;
}
else
{
lean_dec(v___x_3190_);
v___y_3155_ = v___x_3189_;
v___y_3156_ = v_snd_3180_;
v_lower_3157_ = v___x_3191_;
v_upper_3158_ = v___x_3181_;
goto v___jp_3154_;
}
}
}
}
else
{
lean_object* v___x_3202_; 
lean_dec_ref(v_x_3144_);
lean_dec_ref(v_x_3143_);
v___x_3202_ = lean_box(0);
return v___x_3202_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f___closed__0(void){
_start:
{
lean_object* v___x_3203_; lean_object* v_dummy_3204_; 
v___x_3203_ = lean_box(0);
v_dummy_3204_ = l_Lean_Expr_sort___override(v___x_3203_);
return v_dummy_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f(lean_object* v_e_3205_){
_start:
{
lean_object* v_dummy_3206_; lean_object* v_nargs_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_dummy_3206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f___closed__0);
v_nargs_3207_ = l_Lean_Expr_getAppNumArgs(v_e_3205_);
lean_inc(v_nargs_3207_);
v___x_3208_ = lean_mk_array(v_nargs_3207_, v_dummy_3206_);
v___x_3209_ = lean_unsigned_to_nat(1u);
v___x_3210_ = lean_nat_sub(v_nargs_3207_, v___x_3209_);
lean_dec(v_nargs_3207_);
v___x_3211_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__3(v_e_3205_, v___x_3208_, v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__0(lean_object* v_inst_3212_, lean_object* v_R_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__0___redArg(v_a_3214_, v_b_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2(lean_object* v_00_u03b2_3217_, lean_object* v_m_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___redArg(v_m_3218_, v_a_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2___boxed(lean_object* v_00_u03b2_3221_, lean_object* v_m_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2(v_00_u03b2_3221_, v_m_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_m_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2(lean_object* v_00_u03b2_3225_, lean_object* v_a_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___redArg(v_a_3226_, v_x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3229_, lean_object* v_a_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f_spec__2_spec__2(v_00_u03b2_3229_, v_a_3230_, v_x_3231_);
lean_dec(v_x_3231_);
lean_dec(v_a_3230_);
return v_res_3232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__0));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg(lean_object* v_var_3236_, lean_object* v_value_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___x_3294_; 
lean_inc_ref(v_var_3236_);
v___x_3294_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_3236_, v_a_3239_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3349_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3349_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3349_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = l_Lean_Expr_cleanupAnnotations(v_a_3295_);
lean_dec(v_a_3295_);
v___x_3300_ = l_Lean_Expr_isApp(v___x_3299_);
if (v___x_3300_ == 0)
{
lean_dec_ref(v___x_3299_);
lean_del_object(v___x_3297_);
v___y_3244_ = v_a_3238_;
v___y_3245_ = v_a_3239_;
v___y_3246_ = v_a_3240_;
v___y_3247_ = v_a_3241_;
goto v___jp_3243_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3299_);
v___x_3302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__25));
v___x_3303_ = l_Lean_Expr_isConstOf(v___x_3301_, v___x_3302_);
lean_dec_ref(v___x_3301_);
if (v___x_3303_ == 0)
{
lean_dec_ref(v___x_3299_);
lean_del_object(v___x_3297_);
v___y_3244_ = v_a_3238_;
v___y_3245_ = v_a_3239_;
v___y_3246_ = v_a_3240_;
v___y_3247_ = v_a_3241_;
goto v___jp_3243_;
}
else
{
lean_object* v_arg_3304_; lean_object* v___x_3305_; 
lean_dec_ref(v_var_3236_);
v_arg_3304_ = lean_ctor_get(v___x_3299_, 1);
lean_inc_ref(v_arg_3304_);
lean_dec_ref(v___x_3299_);
v___x_3305_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f(v_arg_3304_);
if (lean_obj_tag(v___x_3305_) == 1)
{
lean_object* v_val_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3344_; 
v_val_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3344_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_val_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3344_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_fst_3310_; lean_object* v_snd_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3343_; 
v_fst_3310_ = lean_ctor_get(v_val_3306_, 0);
v_snd_3311_ = lean_ctor_get(v_val_3306_, 1);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_val_3306_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3313_ = v_val_3306_;
v_isShared_3314_ = v_isSharedCheck_3343_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_snd_3311_);
lean_inc(v_fst_3310_);
lean_dec(v_val_3306_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3343_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___y_3316_; uint8_t v___x_3328_; 
v___x_3328_ = lean_unbox(v_snd_3311_);
lean_dec(v_snd_3311_);
if (v___x_3328_ == 0)
{
lean_object* v_w_3329_; lean_object* v_bv_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v_w_3329_ = lean_ctor_get(v_value_3237_, 0);
lean_inc(v_w_3329_);
v_bv_3330_ = lean_ctor_get(v_value_3237_, 1);
lean_inc(v_bv_3330_);
lean_dec_ref(v_value_3237_);
v___x_3331_ = lean_unsigned_to_nat(1u);
v___x_3332_ = l_BitVec_ofNat(v_w_3329_, v___x_3331_);
lean_dec(v_w_3329_);
v___x_3333_ = lean_nat_dec_eq(v_bv_3330_, v___x_3332_);
lean_dec(v___x_3332_);
lean_dec(v_bv_3330_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__77));
v___y_3316_ = v___x_3334_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__79));
v___y_3316_ = v___x_3335_;
goto v___jp_3315_;
}
}
else
{
lean_object* v_w_3336_; lean_object* v_bv_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_w_3336_ = lean_ctor_get(v_value_3237_, 0);
lean_inc(v_w_3336_);
v_bv_3337_ = lean_ctor_get(v_value_3237_, 1);
lean_inc(v_bv_3337_);
lean_dec_ref(v_value_3237_);
v___x_3338_ = lean_unsigned_to_nat(1u);
v___x_3339_ = l_BitVec_ofNat(v_w_3336_, v___x_3338_);
lean_dec(v_w_3336_);
v___x_3340_ = lean_nat_dec_eq(v_bv_3337_, v___x_3339_);
lean_dec(v___x_3339_);
lean_dec(v_bv_3337_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__71));
v___y_3316_ = v___x_3341_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation___closed__74));
v___y_3316_ = v___x_3342_;
goto v___jp_3315_;
}
}
v___jp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3317_ = lean_box(0);
lean_inc(v___y_3316_);
v___x_3318_ = l_Lean_mkConst(v___y_3316_, v___x_3317_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v___x_3318_);
v___x_3320_ = v___x_3313_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_fst_3310_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3322_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3320_);
v___x_3322_ = v___x_3308_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3324_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3322_);
v___x_3324_ = v___x_3297_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
lean_dec(v___x_3305_);
lean_dec_ref(v_value_3237_);
v___x_3345_ = lean_box(0);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3345_);
v___x_3347_ = v___x_3297_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec_ref(v_value_3237_);
lean_dec_ref(v_var_3236_);
v_a_3350_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3294_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3294_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
v___jp_3243_:
{
lean_object* v___x_3248_; 
v___x_3248_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprElement_x3f(v_var_3236_);
lean_dec_ref(v_var_3236_);
if (lean_obj_tag(v___x_3248_) == 1)
{
lean_object* v_val_3249_; lean_object* v_fst_3250_; lean_object* v_snd_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3291_; 
v_val_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_val_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v_fst_3250_ = lean_ctor_get(v_val_3249_, 0);
v_snd_3251_ = lean_ctor_get(v_val_3249_, 1);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_val_3249_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3253_ = v_val_3249_;
v_isShared_3254_ = v_isSharedCheck_3291_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_snd_3251_);
lean_inc(v_fst_3250_);
lean_dec(v_val_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3291_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_Expr_fvarId_x3f(v_fst_3250_);
lean_dec(v_fst_3250_);
if (lean_obj_tag(v___x_3255_) == 1)
{
lean_object* v_val_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3288_; 
v_val_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3288_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_val_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3288_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_FVarId_getUserName___redArg(v_val_3256_, v___y_3244_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3279_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3279_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3279_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v_bv_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v_bv_3265_ = lean_ctor_get(v_value_3237_, 1);
lean_inc(v_bv_3265_);
lean_dec_ref(v_value_3237_);
v___x_3266_ = l_Nat_toSubscriptString(v_bv_3265_);
v___x_3267_ = lean_name_append_after(v_a_3261_, v___x_3266_);
v___x_3268_ = lean_box(0);
v___x_3269_ = l_Lean_mkConst(v___x_3267_, v___x_3268_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v___x_3269_);
lean_ctor_set(v___x_3253_, 0, v_snd_3251_);
v___x_3271_ = v___x_3253_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_snd_3251_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3273_; 
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v___x_3271_);
v___x_3273_ = v___x_3258_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3275_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3273_);
v___x_3275_ = v___x_3263_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_del_object(v___x_3258_);
lean_del_object(v___x_3253_);
lean_dec(v_snd_3251_);
lean_dec_ref(v_value_3237_);
v_a_3280_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3260_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3260_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v___x_3255_);
lean_del_object(v___x_3253_);
lean_dec(v_snd_3251_);
lean_dec_ref(v_value_3237_);
v___x_3289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___closed__1);
v___x_3290_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation_spec__2___redArg(v___x_3289_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3290_;
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v___x_3248_);
lean_dec_ref(v_value_3237_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg___boxed(lean_object* v_var_3358_, lean_object* v_value_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg(v_var_3358_, v_value_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f(lean_object* v_var_3366_, lean_object* v_value_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg(v_var_3366_, v_value_3367_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___boxed(lean_object* v_var_3376_, lean_object* v_value_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f(v_var_3376_, v_value_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(lean_object* v_var_3386_, lean_object* v_value_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v___x_3395_; 
lean_inc_ref(v_value_3387_);
lean_inc_ref(v_var_3386_);
v___x_3395_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEprEquation_x3f___redArg(v_var_3386_, v_value_3387_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3444_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3444_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3444_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
if (lean_obj_tag(v_a_3396_) == 1)
{
lean_object* v_val_3400_; lean_object* v_fst_3401_; lean_object* v_snd_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_value_3387_);
lean_dec_ref(v_var_3386_);
v_val_3400_ = lean_ctor_get(v_a_3396_, 0);
lean_inc(v_val_3400_);
lean_dec_ref_known(v_a_3396_, 1);
v_fst_3401_ = lean_ctor_get(v_val_3400_, 0);
v_snd_3402_ = lean_ctor_get(v_val_3400_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_val_3400_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3404_ = v_val_3400_;
v_isShared_3405_ = v_isSharedCheck_3415_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_snd_3402_);
lean_inc(v_fst_3401_);
lean_dec(v_val_3400_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3415_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3406_ = l_Lean_Expr_getAppFn(v_fst_3401_);
v___x_3407_ = l_Lean_Expr_fvarId_x3f(v___x_3406_);
lean_dec_ref(v___x_3406_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3407_);
lean_ctor_set(v___x_3404_, 0, v_snd_3402_);
v___x_3409_ = v___x_3404_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_snd_3402_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v_fst_3401_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3410_);
v___x_3412_ = v___x_3398_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v___x_3416_; 
lean_del_object(v___x_3398_);
lean_dec(v_a_3396_);
v___x_3416_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformBitVecEquation(v_var_3386_, v_value_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3435_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3435_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3435_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3434_; 
v_fst_3421_ = lean_ctor_get(v_a_3417_, 0);
v_snd_3422_ = lean_ctor_get(v_a_3417_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3424_ = v_a_3417_;
v_isShared_3425_ = v_isSharedCheck_3434_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_inc(v_fst_3421_);
lean_dec(v_a_3417_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3434_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3426_ = l_Lean_Expr_fvarId_x3f(v_fst_3421_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3426_);
lean_ctor_set(v___x_3424_, 0, v_snd_3422_);
v___x_3428_ = v___x_3424_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_snd_3422_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v_fst_3421_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3429_);
v___x_3431_ = v___x_3419_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
v_a_3436_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3416_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3416_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v_value_3387_);
lean_dec_ref(v_var_3386_);
v_a_3445_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3395_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3395_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(lean_object* v_var_3453_, lean_object* v_value_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_3453_, v_value_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_3463_, lean_object* v_x_3464_){
_start:
{
if (lean_obj_tag(v_x_3464_) == 0)
{
return v_x_3463_;
}
else
{
lean_object* v_key_3465_; lean_object* v_value_3466_; lean_object* v_tail_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3490_; 
v_key_3465_ = lean_ctor_get(v_x_3464_, 0);
v_value_3466_ = lean_ctor_get(v_x_3464_, 1);
v_tail_3467_ = lean_ctor_get(v_x_3464_, 2);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_x_3464_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3469_ = v_x_3464_;
v_isShared_3470_ = v_isSharedCheck_3490_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_tail_3467_);
lean_inc(v_value_3466_);
lean_inc(v_key_3465_);
lean_dec(v_x_3464_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3490_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; uint64_t v___x_3472_; uint64_t v___x_3473_; uint64_t v___x_3474_; uint64_t v_fold_3475_; uint64_t v___x_3476_; uint64_t v___x_3477_; uint64_t v___x_3478_; size_t v___x_3479_; size_t v___x_3480_; size_t v___x_3481_; size_t v___x_3482_; size_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3471_ = lean_array_get_size(v_x_3463_);
v___x_3472_ = l_Lean_Expr_hash(v_key_3465_);
v___x_3473_ = 32ULL;
v___x_3474_ = lean_uint64_shift_right(v___x_3472_, v___x_3473_);
v_fold_3475_ = lean_uint64_xor(v___x_3472_, v___x_3474_);
v___x_3476_ = 16ULL;
v___x_3477_ = lean_uint64_shift_right(v_fold_3475_, v___x_3476_);
v___x_3478_ = lean_uint64_xor(v_fold_3475_, v___x_3477_);
v___x_3479_ = lean_uint64_to_usize(v___x_3478_);
v___x_3480_ = lean_usize_of_nat(v___x_3471_);
v___x_3481_ = ((size_t)1ULL);
v___x_3482_ = lean_usize_sub(v___x_3480_, v___x_3481_);
v___x_3483_ = lean_usize_land(v___x_3479_, v___x_3482_);
v___x_3484_ = lean_array_uget_borrowed(v_x_3463_, v___x_3483_);
lean_inc(v___x_3484_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 2, v___x_3484_);
v___x_3486_ = v___x_3469_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_key_3465_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_value_3466_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_array_uset(v_x_3463_, v___x_3483_, v___x_3486_);
v_x_3463_ = v___x_3487_;
v_x_3464_ = v_tail_3467_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3491_, lean_object* v_source_3492_, lean_object* v_target_3493_){
_start:
{
lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3494_ = lean_array_get_size(v_source_3492_);
v___x_3495_ = lean_nat_dec_lt(v_i_3491_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_dec_ref(v_source_3492_);
lean_dec(v_i_3491_);
return v_target_3493_;
}
else
{
lean_object* v_es_3496_; lean_object* v___x_3497_; lean_object* v_source_3498_; lean_object* v_target_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_es_3496_ = lean_array_fget(v_source_3492_, v_i_3491_);
v___x_3497_ = lean_box(0);
v_source_3498_ = lean_array_fset(v_source_3492_, v_i_3491_, v___x_3497_);
v_target_3499_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(v_target_3493_, v_es_3496_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = lean_nat_add(v_i_3491_, v___x_3500_);
lean_dec(v_i_3491_);
v_i_3491_ = v___x_3501_;
v_source_3492_ = v_source_3498_;
v_target_3493_ = v_target_3499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(lean_object* v_data_3503_){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v_nbuckets_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3504_ = lean_array_get_size(v_data_3503_);
v___x_3505_ = lean_unsigned_to_nat(2u);
v_nbuckets_3506_ = lean_nat_mul(v___x_3504_, v___x_3505_);
v___x_3507_ = lean_unsigned_to_nat(0u);
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_mk_array(v_nbuckets_3506_, v___x_3508_);
v___x_3510_ = lean_array_propagate_mark(v_data_3503_, v___x_3509_);
v___x_3511_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v___x_3507_, v_data_3503_, v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(lean_object* v_a_3512_, lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
uint8_t v___x_3514_; 
v___x_3514_ = 0;
return v___x_3514_;
}
else
{
lean_object* v_key_3515_; lean_object* v_tail_3516_; uint8_t v___x_3517_; 
v_key_3515_ = lean_ctor_get(v_x_3513_, 0);
v_tail_3516_ = lean_ctor_get(v_x_3513_, 2);
v___x_3517_ = lean_expr_eqv(v_key_3515_, v_a_3512_);
if (v___x_3517_ == 0)
{
v_x_3513_ = v_tail_3516_;
goto _start;
}
else
{
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(lean_object* v_a_3519_, lean_object* v_x_3520_){
_start:
{
uint8_t v_res_3521_; lean_object* v_r_3522_; 
v_res_3521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3519_, v_x_3520_);
lean_dec(v_x_3520_);
lean_dec_ref(v_a_3519_);
v_r_3522_ = lean_box(v_res_3521_);
return v_r_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(lean_object* v_m_3523_, lean_object* v_a_3524_, lean_object* v_b_3525_){
_start:
{
lean_object* v_size_3526_; lean_object* v_buckets_3527_; lean_object* v___x_3528_; uint64_t v___x_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; uint64_t v_fold_3532_; uint64_t v___x_3533_; uint64_t v___x_3534_; uint64_t v___x_3535_; size_t v___x_3536_; size_t v___x_3537_; size_t v___x_3538_; size_t v___x_3539_; size_t v___x_3540_; lean_object* v_bkt_3541_; uint8_t v___x_3542_; 
v_size_3526_ = lean_ctor_get(v_m_3523_, 0);
v_buckets_3527_ = lean_ctor_get(v_m_3523_, 1);
v___x_3528_ = lean_array_get_size(v_buckets_3527_);
v___x_3529_ = l_Lean_Expr_hash(v_a_3524_);
v___x_3530_ = 32ULL;
v___x_3531_ = lean_uint64_shift_right(v___x_3529_, v___x_3530_);
v_fold_3532_ = lean_uint64_xor(v___x_3529_, v___x_3531_);
v___x_3533_ = 16ULL;
v___x_3534_ = lean_uint64_shift_right(v_fold_3532_, v___x_3533_);
v___x_3535_ = lean_uint64_xor(v_fold_3532_, v___x_3534_);
v___x_3536_ = lean_uint64_to_usize(v___x_3535_);
v___x_3537_ = lean_usize_of_nat(v___x_3528_);
v___x_3538_ = ((size_t)1ULL);
v___x_3539_ = lean_usize_sub(v___x_3537_, v___x_3538_);
v___x_3540_ = lean_usize_land(v___x_3536_, v___x_3539_);
v_bkt_3541_ = lean_array_uget_borrowed(v_buckets_3527_, v___x_3540_);
v___x_3542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3524_, v_bkt_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3563_; 
lean_inc_ref(v_buckets_3527_);
lean_inc(v_size_3526_);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_m_3523_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; lean_object* v_unused_3565_; 
v_unused_3564_ = lean_ctor_get(v_m_3523_, 1);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_m_3523_, 0);
lean_dec(v_unused_3565_);
v___x_3544_ = v_m_3523_;
v_isShared_3545_ = v_isSharedCheck_3563_;
goto v_resetjp_3543_;
}
else
{
lean_dec(v_m_3523_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3563_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v_size_x27_3547_; lean_object* v___x_3548_; lean_object* v_buckets_x27_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3546_ = lean_unsigned_to_nat(1u);
v_size_x27_3547_ = lean_nat_add(v_size_3526_, v___x_3546_);
lean_dec(v_size_3526_);
lean_inc(v_bkt_3541_);
v___x_3548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3548_, 0, v_a_3524_);
lean_ctor_set(v___x_3548_, 1, v_b_3525_);
lean_ctor_set(v___x_3548_, 2, v_bkt_3541_);
v_buckets_x27_3549_ = lean_array_uset(v_buckets_3527_, v___x_3540_, v___x_3548_);
v___x_3550_ = lean_unsigned_to_nat(4u);
v___x_3551_ = lean_nat_mul(v_size_x27_3547_, v___x_3550_);
v___x_3552_ = lean_unsigned_to_nat(3u);
v___x_3553_ = lean_nat_div(v___x_3551_, v___x_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_array_get_size(v_buckets_x27_3549_);
v___x_3555_ = lean_nat_dec_le(v___x_3553_, v___x_3554_);
lean_dec(v___x_3553_);
if (v___x_3555_ == 0)
{
lean_object* v_val_3556_; lean_object* v___x_3558_; 
v_val_3556_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_buckets_x27_3549_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v_val_3556_);
lean_ctor_set(v___x_3544_, 0, v_size_x27_3547_);
v___x_3558_ = v___x_3544_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_size_x27_3547_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_val_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v___x_3561_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v_buckets_x27_3549_);
lean_ctor_set(v___x_3544_, 0, v_size_x27_3547_);
v___x_3561_ = v___x_3544_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_size_x27_3547_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_buckets_x27_3549_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_dec(v_b_3525_);
lean_dec_ref(v_a_3524_);
return v_m_3523_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(lean_object* v_m_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_buckets_3568_; lean_object* v___x_3569_; uint64_t v___x_3570_; uint64_t v___x_3571_; uint64_t v___x_3572_; uint64_t v_fold_3573_; uint64_t v___x_3574_; uint64_t v___x_3575_; uint64_t v___x_3576_; size_t v___x_3577_; size_t v___x_3578_; size_t v___x_3579_; size_t v___x_3580_; size_t v___x_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; 
v_buckets_3568_ = lean_ctor_get(v_m_3566_, 1);
v___x_3569_ = lean_array_get_size(v_buckets_3568_);
v___x_3570_ = l_Lean_Expr_hash(v_a_3567_);
v___x_3571_ = 32ULL;
v___x_3572_ = lean_uint64_shift_right(v___x_3570_, v___x_3571_);
v_fold_3573_ = lean_uint64_xor(v___x_3570_, v___x_3572_);
v___x_3574_ = 16ULL;
v___x_3575_ = lean_uint64_shift_right(v_fold_3573_, v___x_3574_);
v___x_3576_ = lean_uint64_xor(v_fold_3573_, v___x_3575_);
v___x_3577_ = lean_uint64_to_usize(v___x_3576_);
v___x_3578_ = lean_usize_of_nat(v___x_3569_);
v___x_3579_ = ((size_t)1ULL);
v___x_3580_ = lean_usize_sub(v___x_3578_, v___x_3579_);
v___x_3581_ = lean_usize_land(v___x_3577_, v___x_3580_);
v___x_3582_ = lean_array_uget_borrowed(v_buckets_3568_, v___x_3581_);
v___x_3583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3567_, v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg___boxed(lean_object* v_m_3584_, lean_object* v_a_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3584_, v_a_3585_);
lean_dec_ref(v_a_3585_);
lean_dec_ref(v_m_3584_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(lean_object* v_as_3588_, size_t v_sz_3589_, size_t v_i_3590_, lean_object* v_b_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_a_3600_; uint8_t v___x_3604_; 
v___x_3604_ = lean_usize_dec_lt(v_i_3590_, v_sz_3589_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3605_, 0, v_b_3591_);
return v___x_3605_;
}
else
{
lean_object* v_a_3606_; lean_object* v_fst_3607_; lean_object* v_snd_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_a_3606_ = lean_array_uget_borrowed(v_as_3588_, v_i_3590_);
v_fst_3607_ = lean_ctor_get(v_a_3606_, 0);
v_snd_3608_ = lean_ctor_get(v_a_3606_, 1);
v___x_3609_ = lean_box(0);
lean_inc(v_snd_3608_);
lean_inc(v_fst_3607_);
v___x_3610_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_3607_, v_snd_3608_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v_snd_3612_; lean_object* v_fst_3613_; lean_object* v_fst_3614_; lean_object* v_snd_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3657_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v_snd_3612_ = lean_ctor_get(v_a_3611_, 1);
lean_inc(v_snd_3612_);
v_fst_3613_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_fst_3613_);
lean_dec(v_a_3611_);
v_fst_3614_ = lean_ctor_get(v_snd_3612_, 0);
v_snd_3615_ = lean_ctor_get(v_snd_3612_, 1);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_snd_3612_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3617_ = v_snd_3612_;
v_isShared_3618_ = v_isSharedCheck_3657_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_snd_3615_);
lean_inc(v_fst_3614_);
lean_dec(v_snd_3612_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3657_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v_uninterpretedSymbols_3620_; lean_object* v_functionSymbols_3621_; lean_object* v_functionSymbolSet_3622_; lean_object* v_unusedRelevantHypotheses_3623_; lean_object* v_derivedEquations_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3656_; 
v___x_3619_ = lean_st_ref_take(v___y_3593_);
v_uninterpretedSymbols_3620_ = lean_ctor_get(v___x_3619_, 0);
v_functionSymbols_3621_ = lean_ctor_get(v___x_3619_, 1);
v_functionSymbolSet_3622_ = lean_ctor_get(v___x_3619_, 2);
v_unusedRelevantHypotheses_3623_ = lean_ctor_get(v___x_3619_, 3);
v_derivedEquations_3624_ = lean_ctor_get(v___x_3619_, 4);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3626_ = v___x_3619_;
v_isShared_3627_ = v_isSharedCheck_3656_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_derivedEquations_3624_);
lean_inc(v_unusedRelevantHypotheses_3623_);
lean_inc(v_functionSymbolSet_3622_);
lean_inc(v_functionSymbols_3621_);
lean_inc(v_uninterpretedSymbols_3620_);
lean_dec(v___x_3619_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3656_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
lean_inc(v_fst_3613_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 1, v_fst_3614_);
lean_ctor_set(v___x_3617_, 0, v_fst_3613_);
v___x_3629_ = v___x_3617_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_fst_3613_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_fst_3614_);
v___x_3629_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3630_ = lean_array_push(v_derivedEquations_3624_, v___x_3629_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 4, v___x_3630_);
v___x_3632_ = v___x_3626_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_uninterpretedSymbols_3620_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_functionSymbols_3621_);
lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_functionSymbolSet_3622_);
lean_ctor_set(v_reuseFailAlloc_3654_, 3, v_unusedRelevantHypotheses_3623_);
lean_ctor_set(v_reuseFailAlloc_3654_, 4, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_st_ref_put(v___y_3593_, v___x_3632_);
if (lean_obj_tag(v_snd_3615_) == 0)
{
lean_object* v___x_3634_; lean_object* v_functionSymbolSet_3635_; uint8_t v___x_3636_; 
v___x_3634_ = lean_st_ref_get(v___y_3593_);
v_functionSymbolSet_3635_ = lean_ctor_get(v___x_3634_, 2);
lean_inc_ref(v_functionSymbolSet_3635_);
lean_dec(v___x_3634_);
v___x_3636_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_functionSymbolSet_3635_, v_fst_3613_);
lean_dec_ref(v_functionSymbolSet_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; lean_object* v_uninterpretedSymbols_3638_; lean_object* v_functionSymbols_3639_; lean_object* v_functionSymbolSet_3640_; lean_object* v_unusedRelevantHypotheses_3641_; lean_object* v_derivedEquations_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3651_; 
v___x_3637_ = lean_st_ref_take(v___y_3593_);
v_uninterpretedSymbols_3638_ = lean_ctor_get(v___x_3637_, 0);
v_functionSymbols_3639_ = lean_ctor_get(v___x_3637_, 1);
v_functionSymbolSet_3640_ = lean_ctor_get(v___x_3637_, 2);
v_unusedRelevantHypotheses_3641_ = lean_ctor_get(v___x_3637_, 3);
v_derivedEquations_3642_ = lean_ctor_get(v___x_3637_, 4);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3644_ = v___x_3637_;
v_isShared_3645_ = v_isSharedCheck_3651_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_derivedEquations_3642_);
lean_inc(v_unusedRelevantHypotheses_3641_);
lean_inc(v_functionSymbolSet_3640_);
lean_inc(v_functionSymbols_3639_);
lean_inc(v_uninterpretedSymbols_3638_);
lean_dec(v___x_3637_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3651_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3646_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_uninterpretedSymbols_3638_, v_fst_3613_, v___x_3609_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3646_);
v___x_3648_ = v___x_3644_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_functionSymbols_3639_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_functionSymbolSet_3640_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_unusedRelevantHypotheses_3641_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_derivedEquations_3642_);
v___x_3648_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_st_ref_put(v___y_3593_, v___x_3648_);
v_a_3600_ = v___x_3609_;
goto v___jp_3599_;
}
}
}
else
{
lean_dec(v_fst_3613_);
v_a_3600_ = v___x_3609_;
goto v___jp_3599_;
}
}
else
{
lean_object* v_val_3652_; lean_object* v___x_3653_; 
lean_dec(v_fst_3613_);
v_val_3652_ = lean_ctor_get(v_snd_3615_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v_snd_3615_, 1);
v___x_3653_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_val_3652_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v_val_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_dec_ref_known(v___x_3653_, 1);
v_a_3600_ = v___x_3609_;
goto v___jp_3599_;
}
else
{
return v___x_3653_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
v_a_3658_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3610_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3610_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
v___jp_3599_:
{
size_t v___x_3601_; size_t v___x_3602_; 
v___x_3601_ = ((size_t)1ULL);
v___x_3602_ = lean_usize_add(v_i_3590_, v___x_3601_);
v_i_3590_ = v___x_3602_;
v_b_3591_ = v_a_3600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3___boxed(lean_object* v_as_3666_, lean_object* v_sz_3667_, lean_object* v_i_3668_, lean_object* v_b_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
size_t v_sz_boxed_3677_; size_t v_i_boxed_3678_; lean_object* v_res_3679_; 
v_sz_boxed_3677_ = lean_unbox_usize(v_sz_3667_);
lean_dec(v_sz_3667_);
v_i_boxed_3678_ = lean_unbox_usize(v_i_3668_);
lean_dec(v_i_3668_);
v_res_3679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_as_3666_, v_sz_boxed_3677_, v_i_boxed_3678_, v_b_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec_ref(v_as_3666_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(lean_object* v_as_3680_, size_t v_sz_3681_, size_t v_i_3682_, lean_object* v_b_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_a_3687_; uint8_t v___x_3691_; 
v___x_3691_ = lean_usize_dec_lt(v_i_3682_, v_sz_3681_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v_b_3683_);
return v___x_3692_;
}
else
{
lean_object* v___x_3693_; lean_object* v_a_3694_; lean_object* v___x_3695_; 
v___x_3693_ = lean_box(0);
v_a_3694_ = lean_array_uget_borrowed(v_as_3680_, v_i_3682_);
lean_inc(v_a_3694_);
v___x_3695_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_isEprPredApp_x3f(v_a_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v___x_3696_; lean_object* v_uninterpretedSymbols_3697_; lean_object* v_functionSymbols_3698_; lean_object* v_functionSymbolSet_3699_; lean_object* v_unusedRelevantHypotheses_3700_; lean_object* v_derivedEquations_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3711_; 
v___x_3696_ = lean_st_ref_take(v___y_3684_);
v_uninterpretedSymbols_3697_ = lean_ctor_get(v___x_3696_, 0);
v_functionSymbols_3698_ = lean_ctor_get(v___x_3696_, 1);
v_functionSymbolSet_3699_ = lean_ctor_get(v___x_3696_, 2);
v_unusedRelevantHypotheses_3700_ = lean_ctor_get(v___x_3696_, 3);
v_derivedEquations_3701_ = lean_ctor_get(v___x_3696_, 4);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3703_ = v___x_3696_;
v_isShared_3704_ = v_isSharedCheck_3711_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_derivedEquations_3701_);
lean_inc(v_unusedRelevantHypotheses_3700_);
lean_inc(v_functionSymbolSet_3699_);
lean_inc(v_functionSymbols_3698_);
lean_inc(v_uninterpretedSymbols_3697_);
lean_dec(v___x_3696_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3711_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_inc_n(v_a_3694_, 2);
v___x_3705_ = lean_array_push(v_functionSymbols_3698_, v_a_3694_);
v___x_3706_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_functionSymbolSet_3699_, v_a_3694_, v___x_3693_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 2, v___x_3706_);
lean_ctor_set(v___x_3703_, 1, v___x_3705_);
v___x_3708_ = v___x_3703_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_uninterpretedSymbols_3697_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_unusedRelevantHypotheses_3700_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_derivedEquations_3701_);
v___x_3708_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_st_ref_put(v___y_3684_, v___x_3708_);
v_a_3687_ = v___x_3693_;
goto v___jp_3686_;
}
}
}
else
{
lean_dec_ref_known(v___x_3695_, 1);
v_a_3687_ = v___x_3693_;
goto v___jp_3686_;
}
}
v___jp_3686_:
{
size_t v___x_3688_; size_t v___x_3689_; 
v___x_3688_ = ((size_t)1ULL);
v___x_3689_ = lean_usize_add(v_i_3682_, v___x_3688_);
v_i_3682_ = v___x_3689_;
v_b_3683_ = v_a_3687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg___boxed(lean_object* v_as_3712_, lean_object* v_sz_3713_, lean_object* v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
size_t v_sz_boxed_3718_; size_t v_i_boxed_3719_; lean_object* v_res_3720_; 
v_sz_boxed_3718_ = lean_unbox_usize(v_sz_3713_);
lean_dec(v_sz_3713_);
v_i_boxed_3719_ = lean_unbox_usize(v_i_3714_);
lean_dec(v_i_3714_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3712_, v_sz_boxed_3718_, v_i_boxed_3719_, v_b_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v_as_3712_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v_equations_3728_; lean_object* v_functionAtoms_3729_; lean_object* v___x_3730_; size_t v_sz_3731_; size_t v___x_3732_; lean_object* v___x_3733_; 
v_equations_3728_ = lean_ctor_get(v_a_3721_, 2);
v_functionAtoms_3729_ = lean_ctor_get(v_a_3721_, 3);
v___x_3730_ = lean_box(0);
v_sz_3731_ = lean_array_size(v_functionAtoms_3729_);
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_functionAtoms_3729_, v_sz_3731_, v___x_3732_, v___x_3730_, v_a_3722_);
if (lean_obj_tag(v___x_3733_) == 0)
{
size_t v_sz_3734_; lean_object* v___x_3735_; 
lean_dec_ref_known(v___x_3733_, 1);
v_sz_3734_ = lean_array_size(v_equations_3728_);
v___x_3735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__3(v_equations_3728_, v_sz_3734_, v___x_3732_, v___x_3730_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3743_);
v___x_3737_ = v___x_3735_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v___x_3735_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3730_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3730_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
else
{
return v___x_3735_;
}
}
else
{
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
return v_res_3751_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(lean_object* v_00_u03b2_3752_, lean_object* v_m_3753_, lean_object* v_a_3754_){
_start:
{
uint8_t v___x_3755_; 
v___x_3755_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_3753_, v_a_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___boxed(lean_object* v_00_u03b2_3756_, lean_object* v_m_3757_, lean_object* v_a_3758_){
_start:
{
uint8_t v_res_3759_; lean_object* v_r_3760_; 
v_res_3759_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(v_00_u03b2_3756_, v_m_3757_, v_a_3758_);
lean_dec_ref(v_a_3758_);
lean_dec_ref(v_m_3757_);
v_r_3760_ = lean_box(v_res_3759_);
return v_r_3760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(lean_object* v_00_u03b2_3761_, lean_object* v_m_3762_, lean_object* v_a_3763_, lean_object* v_b_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___redArg(v_m_3762_, v_a_3763_, v_b_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(lean_object* v_as_3766_, size_t v_sz_3767_, size_t v_i_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___redArg(v_as_3766_, v_sz_3767_, v_i_3768_, v_b_3769_, v___y_3771_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2___boxed(lean_object* v_as_3778_, lean_object* v_sz_3779_, lean_object* v_i_3780_, lean_object* v_b_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
size_t v_sz_boxed_3789_; size_t v_i_boxed_3790_; lean_object* v_res_3791_; 
v_sz_boxed_3789_ = lean_unbox_usize(v_sz_3779_);
lean_dec(v_sz_3779_);
v_i_boxed_3790_ = lean_unbox_usize(v_i_3780_);
lean_dec(v_i_3780_);
v_res_3791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__2(v_as_3778_, v_sz_boxed_3789_, v_i_boxed_3790_, v_b_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v_as_3778_);
return v_res_3791_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(lean_object* v_00_u03b2_3792_, lean_object* v_a_3793_, lean_object* v_x_3794_){
_start:
{
uint8_t v___x_3795_; 
v___x_3795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_3793_, v_x_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3796_, lean_object* v_a_3797_, lean_object* v_x_3798_){
_start:
{
uint8_t v_res_3799_; lean_object* v_r_3800_; 
v_res_3799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_3796_, v_a_3797_, v_x_3798_);
lean_dec(v_x_3798_);
lean_dec_ref(v_a_3797_);
v_r_3800_ = lean_box(v_res_3799_);
return v_r_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2(lean_object* v_00_u03b2_3801_, lean_object* v_data_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2___redArg(v_data_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3804_, lean_object* v_i_3805_, lean_object* v_source_3806_, lean_object* v_target_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3___redArg(v_i_3805_, v_source_3806_, v_target_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3810_, v_x_3811_);
return v___x_3812_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__0));
v___x_3815_ = l_Lean_stringToMessageData(v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(lean_object* v_as_x27_3816_, lean_object* v_b_3817_){
_start:
{
if (lean_obj_tag(v_as_x27_3816_) == 0)
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3818_, 0, v_b_3817_);
return v___x_3818_;
}
else
{
lean_object* v_head_3819_; lean_object* v_tail_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_head_3819_ = lean_ctor_get(v_as_x27_3816_, 0);
v_tail_3820_ = lean_ctor_get(v_as_x27_3816_, 1);
v___x_3821_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1);
lean_inc(v_head_3819_);
v___x_3822_ = l_Lean_MessageData_ofExpr(v_head_3819_);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3817_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v_as_x27_3816_ = v_tail_3820_;
v_b_3817_ = v___x_3824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3826_, lean_object* v_b_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v_as_x27_3826_, v_b_3827_);
lean_dec(v_as_x27_3826_);
return v_res_3828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__0));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer(lean_object* v_d_3832_){
_start:
{
lean_object* v_functionSymbols_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_functionSymbols_3833_ = lean_ctor_get(v_d_3832_, 1);
lean_inc_ref(v_functionSymbols_3833_);
lean_dec_ref(v_d_3832_);
v___x_3834_ = lean_array_get_size(v_functionSymbols_3833_);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = lean_nat_dec_eq(v___x_3834_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_array_to_list(v_functionSymbols_3833_);
v___x_3838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer___closed__1);
v___x_3839_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v___x_3837_, v___x_3838_);
lean_dec(v___x_3837_);
return v___x_3839_;
}
else
{
lean_object* v___x_3840_; 
lean_dec_ref(v_functionSymbols_3833_);
v___x_3840_ = lean_box(0);
return v___x_3840_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(lean_object* v_as_3841_, lean_object* v_as_x27_3842_, lean_object* v_b_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v_as_x27_3842_, v_b_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___boxed(lean_object* v_as_3846_, lean_object* v_as_x27_3847_, lean_object* v_b_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0(v_as_3846_, v_as_x27_3847_, v_b_3848_, v_a_3849_);
lean_dec(v_as_x27_3847_);
lean_dec(v_as_3846_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
if (lean_obj_tag(v_x_3857_) == 0)
{
lean_inc(v_x_3856_);
return v_x_3856_;
}
else
{
lean_object* v_key_3858_; lean_object* v_tail_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_key_3858_ = lean_ctor_get(v_x_3857_, 0);
v_tail_3859_ = lean_ctor_get(v_x_3857_, 2);
v___x_3860_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_x_3856_, v_tail_3859_);
lean_inc(v_key_3858_);
v___x_3861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_key_3858_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
return v___x_3861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0___boxed(lean_object* v_x_3862_, lean_object* v_x_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_x_3862_, v_x_3863_);
lean_dec(v_x_3863_);
lean_dec(v_x_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(lean_object* v_as_3865_, size_t v_i_3866_, size_t v_stop_3867_, lean_object* v_b_3868_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_usize_dec_eq(v_i_3866_, v_stop_3867_);
if (v___x_3869_ == 0)
{
size_t v___x_3870_; size_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3870_ = ((size_t)1ULL);
v___x_3871_ = lean_usize_sub(v_i_3866_, v___x_3870_);
v___x_3872_ = lean_array_uget_borrowed(v_as_3865_, v___x_3871_);
v___x_3873_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v_b_3868_, v___x_3872_);
lean_dec(v_b_3868_);
v_i_3866_ = v___x_3871_;
v_b_3868_ = v___x_3873_;
goto _start;
}
else
{
return v_b_3868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(lean_object* v_as_3875_, lean_object* v_i_3876_, lean_object* v_stop_3877_, lean_object* v_b_3878_){
_start:
{
size_t v_i_boxed_3879_; size_t v_stop_boxed_3880_; lean_object* v_res_3881_; 
v_i_boxed_3879_ = lean_unbox_usize(v_i_3876_);
lean_dec(v_i_3876_);
v_stop_boxed_3880_ = lean_unbox_usize(v_stop_3877_);
lean_dec(v_stop_3877_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_as_3875_, v_i_boxed_3879_, v_stop_boxed_3880_, v_b_3878_);
lean_dec_ref(v_as_3875_);
return v_res_3881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0));
v___x_3884_ = l_Lean_stringToMessageData(v___x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(lean_object* v_d_3885_){
_start:
{
lean_object* v___y_3887_; lean_object* v_uninterpretedSymbols_3890_; lean_object* v_size_3891_; lean_object* v_buckets_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v_uninterpretedSymbols_3890_ = lean_ctor_get(v_d_3885_, 0);
v_size_3891_ = lean_ctor_get(v_uninterpretedSymbols_3890_, 0);
v_buckets_3892_ = lean_ctor_get(v_uninterpretedSymbols_3890_, 1);
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = lean_nat_dec_eq(v_size_3891_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_array_get_size(v_buckets_3892_);
v___x_3897_ = lean_nat_dec_lt(v___x_3893_, v___x_3896_);
if (v___x_3897_ == 0)
{
v___y_3887_ = v___x_3895_;
goto v___jp_3886_;
}
else
{
size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = lean_usize_of_nat(v___x_3896_);
v___x_3899_ = ((size_t)0ULL);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_buckets_3892_, v___x_3898_, v___x_3899_, v___x_3895_);
v___y_3887_ = v___x_3900_;
goto v___jp_3886_;
}
}
else
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_box(0);
return v___x_3901_;
}
v___jp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
v___x_3889_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg(v___y_3887_, v___x_3888_);
lean_dec(v___y_3887_);
return v___x_3889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(lean_object* v_d_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_3902_);
lean_dec_ref(v_d_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(lean_object* v_x_3904_, lean_object* v_x_3905_){
_start:
{
if (lean_obj_tag(v_x_3905_) == 0)
{
lean_inc(v_x_3904_);
return v_x_3904_;
}
else
{
lean_object* v_key_3906_; lean_object* v_tail_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_key_3906_ = lean_ctor_get(v_x_3905_, 0);
v_tail_3907_ = lean_ctor_get(v_x_3905_, 2);
v___x_3908_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3904_, v_tail_3907_);
lean_inc(v_key_3906_);
v___x_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3909_, 0, v_key_3906_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
return v___x_3909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* v_x_3910_, lean_object* v_x_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_3910_, v_x_3911_);
lean_dec(v_x_3911_);
lean_dec(v_x_3910_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(lean_object* v_as_3913_, size_t v_i_3914_, size_t v_stop_3915_, lean_object* v_b_3916_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_usize_dec_eq(v_i_3914_, v_stop_3915_);
if (v___x_3917_ == 0)
{
size_t v___x_3918_; size_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_sub(v_i_3914_, v___x_3918_);
v___x_3920_ = lean_array_uget_borrowed(v_as_3913_, v___x_3919_);
v___x_3921_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_b_3916_, v___x_3920_);
lean_dec(v_b_3916_);
v_i_3914_ = v___x_3919_;
v_b_3916_ = v___x_3921_;
goto _start;
}
else
{
return v_b_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object* v_as_3923_, lean_object* v_i_3924_, lean_object* v_stop_3925_, lean_object* v_b_3926_){
_start:
{
size_t v_i_boxed_3927_; size_t v_stop_boxed_3928_; lean_object* v_res_3929_; 
v_i_boxed_3927_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_stop_boxed_3928_ = lean_unbox_usize(v_stop_3925_);
lean_dec(v_stop_3925_);
v_res_3929_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_3923_, v_i_boxed_3927_, v_stop_boxed_3928_, v_b_3926_);
lean_dec_ref(v_as_3923_);
return v_res_3929_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__0));
v___x_3932_ = l_Lean_stringToMessageData(v___x_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(lean_object* v_as_x27_3933_, lean_object* v_b_3934_){
_start:
{
if (lean_obj_tag(v_as_x27_3933_) == 0)
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v_b_3934_);
return v___x_3935_;
}
else
{
lean_object* v_head_3936_; lean_object* v_tail_3937_; lean_object* v_type_3938_; lean_object* v_source_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_head_3936_ = lean_ctor_get(v_as_x27_3933_, 0);
v_tail_3937_ = lean_ctor_get(v_as_x27_3933_, 1);
v_type_3938_ = lean_ctor_get(v_head_3936_, 1);
v_source_3939_ = lean_ctor_get(v_head_3936_, 3);
v___x_3940_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_functionExplainer_spec__0___redArg___closed__1);
lean_inc_ref(v_type_3938_);
v___x_3941_ = l_Lean_MessageData_ofExpr(v_type_3938_);
v___x_3942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___closed__1);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
lean_inc(v_source_3939_);
v___x_3945_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v_source_3939_);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_b_3934_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v_as_x27_3933_ = v_tail_3937_;
v_b_3934_ = v___x_3947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg___boxed(lean_object* v_as_x27_3949_, lean_object* v_b_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3949_, v_b_3950_);
lean_dec(v_as_x27_3949_);
return v_res_3951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0));
v___x_3954_ = l_Lean_stringToMessageData(v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(lean_object* v_d_3955_){
_start:
{
lean_object* v___y_3957_; lean_object* v_unusedRelevantHypotheses_3960_; lean_object* v_size_3961_; lean_object* v_buckets_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_unusedRelevantHypotheses_3960_ = lean_ctor_get(v_d_3955_, 3);
v_size_3961_ = lean_ctor_get(v_unusedRelevantHypotheses_3960_, 0);
v_buckets_3962_ = lean_ctor_get(v_unusedRelevantHypotheses_3960_, 1);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = lean_nat_dec_eq(v_size_3961_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3965_ = lean_box(0);
v___x_3966_ = lean_array_get_size(v_buckets_3962_);
v___x_3967_ = lean_nat_dec_lt(v___x_3963_, v___x_3966_);
if (v___x_3967_ == 0)
{
v___y_3957_ = v___x_3965_;
goto v___jp_3956_;
}
else
{
size_t v___x_3968_; size_t v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_usize_of_nat(v___x_3966_);
v___x_3969_ = ((size_t)0ULL);
v___x_3970_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_buckets_3962_, v___x_3968_, v___x_3969_, v___x_3965_);
v___y_3957_ = v___x_3970_;
goto v___jp_3956_;
}
}
else
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_box(0);
return v___x_3971_;
}
v___jp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
v___x_3959_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v___y_3957_, v___x_3958_);
lean_dec(v___y_3957_);
return v___x_3959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(lean_object* v_d_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_3972_);
lean_dec_ref(v_d_3972_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(lean_object* v_as_3974_, lean_object* v_as_x27_3975_, lean_object* v_b_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___redArg(v_as_x27_3975_, v_b_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0___boxed(lean_object* v_as_3979_, lean_object* v_as_x27_3980_, lean_object* v_b_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v_as_3979_, v_as_x27_3980_, v_b_3981_, v_a_3982_);
lean_dec(v_as_x27_3980_);
lean_dec(v_as_3979_);
return v_res_3983_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0));
v___x_3995_ = l_Lean_stringToMessageData(v___x_3994_);
return v___x_3995_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2));
v___x_3998_ = l_Lean_stringToMessageData(v___x_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(lean_object* v_as_3999_, size_t v_i_4000_, size_t v_stop_4001_, lean_object* v_b_4002_){
_start:
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_usize_dec_eq(v_i_4000_, v_stop_4001_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; size_t v___x_4010_; size_t v___x_4011_; 
v___x_4004_ = lean_array_uget_borrowed(v_as_3999_, v_i_4000_);
v___x_4005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
v___x_4006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4006_, 0, v_b_4002_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
lean_inc(v___x_4004_);
v___x_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
lean_ctor_set(v___x_4007_, 1, v___x_4004_);
v___x_4008_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_4009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_4000_, v___x_4010_);
v_i_4000_ = v___x_4011_;
v_b_4002_ = v___x_4009_;
goto _start;
}
else
{
return v_b_4002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(lean_object* v_as_4013_, lean_object* v_i_4014_, lean_object* v_stop_4015_, lean_object* v_b_4016_){
_start:
{
size_t v_i_boxed_4017_; size_t v_stop_boxed_4018_; lean_object* v_res_4019_; 
v_i_boxed_4017_ = lean_unbox_usize(v_i_4014_);
lean_dec(v_i_4014_);
v_stop_boxed_4018_ = lean_unbox_usize(v_stop_4015_);
lean_dec(v_stop_4015_);
v_res_4019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_4013_, v_i_boxed_4017_, v_stop_boxed_4018_, v_b_4016_);
lean_dec_ref(v_as_4013_);
return v_res_4019_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0));
v___x_4022_ = l_Lean_stringToMessageData(v___x_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(lean_object* v_as_4023_, size_t v_i_4024_, size_t v_stop_4025_, lean_object* v_b_4026_){
_start:
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_usize_dec_eq(v_i_4024_, v_stop_4025_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v_fst_4029_; lean_object* v_snd_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4047_; 
v___x_4028_ = lean_array_uget(v_as_4023_, v_i_4024_);
v_fst_4029_ = lean_ctor_get(v___x_4028_, 0);
v_snd_4030_ = lean_ctor_get(v___x_4028_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4032_ = v___x_4028_;
v_isShared_4033_ = v_isSharedCheck_4047_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_snd_4030_);
lean_inc(v_fst_4029_);
lean_dec(v___x_4028_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4047_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4037_; 
v___x_4034_ = l_Lean_MessageData_ofExpr(v_fst_4029_);
v___x_4035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
if (v_isShared_4033_ == 0)
{
lean_ctor_set_tag(v___x_4032_, 7);
lean_ctor_set(v___x_4032_, 1, v___x_4035_);
lean_ctor_set(v___x_4032_, 0, v___x_4034_);
v___x_4037_ = v___x_4032_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4034_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; size_t v___x_4043_; size_t v___x_4044_; 
v___x_4038_ = l_Lean_MessageData_ofExpr(v_snd_4030_);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4039_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v_b_4026_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = ((size_t)1ULL);
v___x_4044_ = lean_usize_add(v_i_4024_, v___x_4043_);
v_i_4024_ = v___x_4044_;
v_b_4026_ = v___x_4042_;
goto _start;
}
}
}
else
{
return v_b_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(lean_object* v_as_4048_, lean_object* v_i_4049_, lean_object* v_stop_4050_, lean_object* v_b_4051_){
_start:
{
size_t v_i_boxed_4052_; size_t v_stop_boxed_4053_; lean_object* v_res_4054_; 
v_i_boxed_4052_ = lean_unbox_usize(v_i_4049_);
lean_dec(v_i_4049_);
v_stop_boxed_4053_ = lean_unbox_usize(v_stop_4050_);
lean_dec(v_stop_4050_);
v_res_4054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_4048_, v_i_boxed_4052_, v_stop_boxed_4053_, v_b_4051_);
lean_dec_ref(v_as_4048_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(lean_object* v_a_4055_, lean_object* v_x_4056_, lean_object* v_x_4057_){
_start:
{
if (lean_obj_tag(v_x_4057_) == 0)
{
lean_dec_ref(v_a_4055_);
return v_x_4056_;
}
else
{
lean_object* v_head_4058_; lean_object* v_tail_4059_; lean_object* v___x_4060_; 
v_head_4058_ = lean_ctor_get(v_x_4057_, 0);
lean_inc(v_head_4058_);
v_tail_4059_ = lean_ctor_get(v_x_4057_, 1);
lean_inc(v_tail_4059_);
lean_dec_ref_known(v_x_4057_, 2);
lean_inc_ref(v_a_4055_);
v___x_4060_ = lean_apply_1(v_head_4058_, v_a_4055_);
if (lean_obj_tag(v___x_4060_) == 1)
{
lean_object* v_val_4061_; lean_object* v___x_4062_; 
v_val_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_val_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4062_ = lean_array_push(v_x_4056_, v_val_4061_);
v_x_4056_ = v___x_4062_;
v_x_4057_ = v_tail_4059_;
goto _start;
}
else
{
lean_dec(v___x_4060_);
v_x_4057_ = v_tail_4059_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1(void){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4066_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0));
v___x_4067_ = l_Lean_stringToMessageData(v___x_4066_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3));
v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5));
v___x_4075_ = l_Lean_stringToMessageData(v___x_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(lean_object* v_counterExample_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed), 7, 0);
v___x_4086_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_4085_, v_counterExample_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4140_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4140_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4140_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v_err_4092_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_err_4120_; lean_object* v___y_4132_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4112_ = lean_unsigned_to_nat(0u);
v___x_4113_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2));
v___x_4114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_theoryExplainers));
lean_inc_n(v_a_4087_, 2);
v___x_4115_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_4087_, v___x_4113_, v___x_4114_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_spuriousExplainers));
v___x_4117_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_4087_, v___x_4113_, v___x_4116_);
v___x_4118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4);
v___x_4134_ = lean_array_get_size(v___x_4115_);
v___x_4135_ = lean_nat_dec_eq(v___x_4134_, v___x_4112_);
if (v___x_4135_ == 0)
{
uint8_t v___x_4136_; 
v___x_4136_ = lean_nat_dec_lt(v___x_4112_, v___x_4134_);
if (v___x_4136_ == 0)
{
lean_dec_ref(v___x_4115_);
v___y_4132_ = v___x_4118_;
goto v___jp_4131_;
}
else
{
size_t v___x_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v___x_4137_ = ((size_t)0ULL);
v___x_4138_ = lean_usize_of_nat(v___x_4134_);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_4115_, v___x_4137_, v___x_4138_, v___x_4118_);
lean_dec_ref(v___x_4115_);
v___y_4132_ = v___x_4139_;
goto v___jp_4131_;
}
}
else
{
lean_dec_ref(v___x_4115_);
v_err_4120_ = v___x_4118_;
goto v___jp_4119_;
}
v___jp_4091_:
{
lean_object* v_derivedEquations_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v_derivedEquations_4093_ = lean_ctor_get(v_a_4087_, 4);
lean_inc_ref(v_derivedEquations_4093_);
lean_dec(v_a_4087_);
v___x_4094_ = lean_unsigned_to_nat(0u);
v___x_4095_ = lean_array_get_size(v_derivedEquations_4093_);
v___x_4096_ = lean_nat_dec_lt(v___x_4094_, v___x_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4098_; 
lean_dec_ref(v_derivedEquations_4093_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v_err_4092_);
v___x_4098_ = v___x_4089_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_err_4092_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
else
{
size_t v___x_4100_; size_t v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4100_ = ((size_t)0ULL);
v___x_4101_ = lean_usize_of_nat(v___x_4095_);
v___x_4102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_4093_, v___x_4100_, v___x_4101_, v_err_4092_);
lean_dec_ref(v_derivedEquations_4093_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4102_);
v___x_4104_ = v___x_4089_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
v___jp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___y_4107_);
lean_ctor_set(v___x_4109_, 1, v___y_4108_);
v___x_4110_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1);
v___x_4111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4109_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v_err_4092_ = v___x_4111_;
goto v___jp_4091_;
}
v___jp_4119_:
{
lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4121_ = lean_array_get_size(v___x_4117_);
v___x_4122_ = lean_nat_dec_eq(v___x_4121_, v___x_4112_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; 
v___x_4123_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v_err_4120_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = lean_nat_dec_lt(v___x_4112_, v___x_4121_);
if (v___x_4125_ == 0)
{
lean_dec_ref(v___x_4117_);
v___y_4107_ = v___x_4124_;
v___y_4108_ = v___x_4118_;
goto v___jp_4106_;
}
else
{
size_t v___x_4126_; size_t v___x_4127_; lean_object* v___x_4128_; 
v___x_4126_ = ((size_t)0ULL);
v___x_4127_ = lean_usize_of_nat(v___x_4121_);
v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_4117_, v___x_4126_, v___x_4127_, v___x_4118_);
lean_dec_ref(v___x_4117_);
v___y_4107_ = v___x_4124_;
v___y_4108_ = v___x_4128_;
goto v___jp_4106_;
}
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec_ref(v___x_4117_);
v___x_4129_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8, &l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_err_4120_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v_err_4092_ = v___x_4130_;
goto v___jp_4091_;
}
}
v___jp_4131_:
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4118_);
lean_ctor_set(v___x_4133_, 1, v___y_4132_);
v_err_4120_ = v___x_4133_;
goto v___jp_4119_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
v_a_4141_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4086_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4086_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(lean_object* v_counterExample_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(v_counterExample_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
return v_res_4155_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_Prop(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_Basic(uint8_t builtin);
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
res = runtime_initialize_Std_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_Basic(builtin);
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
lean_object* initialize_Std_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Prop(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_Basic(builtin);
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

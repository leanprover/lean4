// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.EPR.InstSets
// Imports: public import Lean.Meta.Tactic.BVDecide.EPR.Basic import Lean.Data.UnionFind import Lean.Util.ForEachExprWhere import Std.Tactic.BVDecide.EPR.BitVec import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor
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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredPropArity;
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredBoolArity;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_UnionFind_union_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_UnionFind_find_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_UnionFind_emptyWithCapacity(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "EPR"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toBvAux"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 239, 89, 128, 83, 215, 9, 208)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 219, 99, 232, 185, 85, 134, 115)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(169, 44, 27, 80, 162, 73, 229, 119)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__0;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ground_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ground_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: !body.hasLooseBVar 0\n      "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "_private.Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor.0.Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor.visitProp'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__4_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__8_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__10_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__12_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__11_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__13_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__9_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__0;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "epr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instSets"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 19, 168, 128, 92, 3, 227, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 62, 244, 249, 3, 209, 58, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "class "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ": terms "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", exceptions "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", avoid "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", full"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Instantiation set analysis"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "projection "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ": class "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "quantifier "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " variable "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Instantiation sets"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f(lean_object* v_e_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_15_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6));
v___x_16_ = lean_unsigned_to_nat(5u);
v___x_17_ = l_Lean_Expr_isAppOfArity(v_e_14_, v___x_15_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = l_Lean_Expr_appArg_x21(v_e_14_);
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___boxed(lean_object* v_e_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f(v_e_21_);
lean_dec_ref(v_e_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg(lean_object* v_a_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
else
{
lean_object* v_key_26_; lean_object* v_value_27_; lean_object* v_tail_28_; uint8_t v___x_29_; 
v_key_26_ = lean_ctor_get(v_x_24_, 0);
v_value_27_ = lean_ctor_get(v_x_24_, 1);
v_tail_28_ = lean_ctor_get(v_x_24_, 2);
v___x_29_ = lean_name_eq(v_key_26_, v_a_23_);
if (v___x_29_ == 0)
{
v_x_24_ = v_tail_28_;
goto _start;
}
else
{
lean_object* v___x_31_; 
lean_inc(v_value_27_);
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v_value_27_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg(v_a_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_a_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg(lean_object* v_m_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_buckets_37_; lean_object* v___x_38_; uint64_t v___y_40_; 
v_buckets_37_ = lean_ctor_get(v_m_35_, 1);
v___x_38_ = lean_array_get_size(v_buckets_37_);
if (lean_obj_tag(v_a_36_) == 0)
{
uint64_t v___x_54_; 
v___x_54_ = 1723ULL;
v___y_40_ = v___x_54_;
goto v___jp_39_;
}
else
{
uint64_t v_hash_55_; 
v_hash_55_ = lean_ctor_get_uint64(v_a_36_, sizeof(void*)*2);
v___y_40_ = v_hash_55_;
goto v___jp_39_;
}
v___jp_39_:
{
uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v_fold_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; size_t v___x_47_; size_t v___x_48_; size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_41_ = 32ULL;
v___x_42_ = lean_uint64_shift_right(v___y_40_, v___x_41_);
v_fold_43_ = lean_uint64_xor(v___y_40_, v___x_42_);
v___x_44_ = 16ULL;
v___x_45_ = lean_uint64_shift_right(v_fold_43_, v___x_44_);
v___x_46_ = lean_uint64_xor(v_fold_43_, v___x_45_);
v___x_47_ = lean_uint64_to_usize(v___x_46_);
v___x_48_ = lean_usize_of_nat(v___x_38_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_sub(v___x_48_, v___x_49_);
v___x_51_ = lean_usize_land(v___x_47_, v___x_50_);
v___x_52_ = lean_array_uget_borrowed(v_buckets_37_, v___x_51_);
v___x_53_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg(v_a_36_, v___x_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg___boxed(lean_object* v_m_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg(v_m_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_m_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f(lean_object* v_e_59_){
_start:
{
lean_object* v_val_61_; lean_object* v___x_70_; 
v___x_70_ = l_Lean_Expr_getAppFn(v_e_59_);
if (lean_obj_tag(v___x_70_) == 4)
{
lean_object* v_declName_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_declName_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_declName_71_);
lean_dec_ref_known(v___x_70_, 2);
v___x_72_ = l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredPropArity;
v___x_73_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg(v___x_72_, v_declName_71_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = l_Std_Tactic_BVDecide_EPR_BitVec_toBvPredBoolArity;
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg(v___x_74_, v_declName_71_);
lean_dec(v_declName_71_);
if (lean_obj_tag(v___x_75_) == 0)
{
return v___x_75_;
}
else
{
lean_object* v_val_76_; 
v_val_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_val_76_);
lean_dec_ref_known(v___x_75_, 1);
v_val_61_ = v_val_76_;
goto v___jp_60_;
}
}
else
{
lean_object* v_val_77_; 
lean_dec(v_declName_71_);
v_val_77_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v___x_73_, 1);
v_val_61_ = v_val_77_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_78_; 
lean_dec_ref(v___x_70_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_62_ = l_Lean_Expr_getAppNumArgs(v_e_59_);
v___x_63_ = lean_unsigned_to_nat(5u);
v___x_64_ = lean_nat_mul(v___x_63_, v_val_61_);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v___x_64_, v___x_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_nat_dec_eq(v___x_62_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_62_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec(v_val_61_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v_val_61_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f___boxed(lean_object* v_e_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f(v_e_79_);
lean_dec_ref(v_e_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0(lean_object* v_00_u03b2_81_, lean_object* v_m_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___redArg(v_m_82_, v_a_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0___boxed(lean_object* v_00_u03b2_85_, lean_object* v_m_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0(v_00_u03b2_85_, v_m_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_m_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0(lean_object* v_00_u03b2_89_, lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___redArg(v_a_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_93_, lean_object* v_a_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f_spec__0_spec__0(v_00_u03b2_93_, v_a_94_, v_x_95_);
lean_dec(v_x_95_);
lean_dec(v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f_spec__0___redArg(lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_array_99_; lean_object* v_start_100_; lean_object* v_stop_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_114_; 
v_array_99_ = lean_ctor_get(v_a_97_, 0);
v_start_100_ = lean_ctor_get(v_a_97_, 1);
v_stop_101_ = lean_ctor_get(v_a_97_, 2);
v_isSharedCheck_114_ = !lean_is_exclusive(v_a_97_);
if (v_isSharedCheck_114_ == 0)
{
v___x_103_ = v_a_97_;
v_isShared_104_ = v_isSharedCheck_114_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_stop_101_);
lean_inc(v_start_100_);
lean_inc(v_array_99_);
lean_dec(v_a_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_114_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_lt(v_start_100_, v_stop_101_);
if (v___x_105_ == 0)
{
lean_del_object(v___x_103_);
lean_dec(v_stop_101_);
lean_dec(v_start_100_);
lean_dec_ref(v_array_99_);
return v_b_98_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_start_100_, v___x_106_);
lean_inc_ref(v_array_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_107_);
v___x_109_ = v___x_103_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_array_99_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_stop_101_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_array_fget(v_array_99_, v_start_100_);
lean_dec(v_start_100_);
lean_dec_ref(v_array_99_);
v___x_111_ = lean_array_push(v_b_98_, v___x_110_);
v_a_97_ = v___x_109_;
v_b_98_ = v___x_111_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__0(void){
_start:
{
lean_object* v___x_115_; lean_object* v_dummy_116_; 
v___x_115_ = lean_box(0);
v_dummy_116_ = l_Lean_Expr_sort___override(v___x_115_);
return v_dummy_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f(lean_object* v_e_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f(v_e_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; 
lean_dec_ref(v_e_119_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_150_; 
v_val_122_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_150_ == 0)
{
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_150_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_val_122_);
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_150_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v_dummy_127_; lean_object* v_nargs_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_lower_137_; lean_object* v_upper_138_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_126_ = l_Lean_instInhabitedExpr;
v_dummy_127_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__0);
v_nargs_128_ = l_Lean_Expr_getAppNumArgs(v_e_119_);
lean_inc(v_nargs_128_);
v___x_129_ = lean_mk_array(v_nargs_128_, v_dummy_127_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_sub(v_nargs_128_, v___x_130_);
lean_dec(v_nargs_128_);
v___x_132_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_119_, v___x_129_, v___x_131_);
v___x_133_ = lean_unsigned_to_nat(4u);
v___x_134_ = lean_nat_mul(v___x_133_, v_val_122_);
lean_dec(v_val_122_);
v___x_135_ = lean_array_get(v___x_126_, v___x_132_, v___x_134_);
v___x_146_ = lean_nat_add(v___x_134_, v___x_130_);
lean_dec(v___x_134_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_array_get_size(v___x_132_);
v___x_149_ = lean_nat_dec_le(v___x_146_, v___x_147_);
if (v___x_149_ == 0)
{
v_lower_137_ = v___x_146_;
v_upper_138_ = v___x_148_;
goto v___jp_136_;
}
else
{
lean_dec(v___x_146_);
v_lower_137_ = v___x_147_;
v_upper_138_ = v___x_148_;
goto v___jp_136_;
}
v___jp_136_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_139_ = l_Array_toSubarray___redArg(v___x_132_, v_lower_137_, v_upper_138_);
v___x_140_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__1));
v___x_141_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f_spec__0___redArg(v___x_139_, v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_135_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_142_);
v___x_144_ = v___x_124_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f_spec__0(lean_object* v_inst_151_, lean_object* v_R_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f_spec__0___redArg(v_a_153_, v_b_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_unsigned_to_nat(16u);
v___x_158_ = lean_mk_array(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__0);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__2(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_162_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1);
v___x_163_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__1));
v___x_164_ = 0;
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_163_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set(v___x_166_, 4, v___x_162_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__2);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default;
return v___x_168_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
else
{
lean_object* v_key_172_; lean_object* v_tail_173_; uint8_t v___x_174_; 
v_key_172_ = lean_ctor_get(v_x_170_, 0);
v_tail_173_ = lean_ctor_get(v_x_170_, 2);
v___x_174_ = lean_expr_eqv(v_key_172_, v_a_169_);
if (v___x_174_ == 0)
{
v_x_170_ = v_tail_173_;
goto _start;
}
else
{
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg___boxed(lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(v_a_176_, v_x_177_);
lean_dec(v_x_177_);
lean_dec_ref(v_a_176_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(lean_object* v_m_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_buckets_182_; lean_object* v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v_fold_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_buckets_182_ = lean_ctor_get(v_m_180_, 1);
v___x_183_ = lean_array_get_size(v_buckets_182_);
v___x_184_ = l_Lean_Expr_hash(v_a_181_);
v___x_185_ = 32ULL;
v___x_186_ = lean_uint64_shift_right(v___x_184_, v___x_185_);
v_fold_187_ = lean_uint64_xor(v___x_184_, v___x_186_);
v___x_188_ = 16ULL;
v___x_189_ = lean_uint64_shift_right(v_fold_187_, v___x_188_);
v___x_190_ = lean_uint64_xor(v_fold_187_, v___x_189_);
v___x_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = lean_usize_of_nat(v___x_183_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_sub(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_land(v___x_191_, v___x_194_);
v___x_196_ = lean_array_uget_borrowed(v_buckets_182_, v___x_195_);
v___x_197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(v_a_181_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg___boxed(lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(v_m_198_, v_a_199_);
lean_dec_ref(v_a_199_);
lean_dec_ref(v_m_198_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
return v_x_202_;
}
else
{
lean_object* v_key_204_; lean_object* v_value_205_; lean_object* v_tail_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_229_; 
v_key_204_ = lean_ctor_get(v_x_203_, 0);
v_value_205_ = lean_ctor_get(v_x_203_, 1);
v_tail_206_ = lean_ctor_get(v_x_203_, 2);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_229_ == 0)
{
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_229_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_tail_206_);
lean_inc(v_value_205_);
lean_inc(v_key_204_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_229_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v_fold_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_210_ = lean_array_get_size(v_x_202_);
v___x_211_ = l_Lean_Expr_hash(v_key_204_);
v___x_212_ = 32ULL;
v___x_213_ = lean_uint64_shift_right(v___x_211_, v___x_212_);
v_fold_214_ = lean_uint64_xor(v___x_211_, v___x_213_);
v___x_215_ = 16ULL;
v___x_216_ = lean_uint64_shift_right(v_fold_214_, v___x_215_);
v___x_217_ = lean_uint64_xor(v_fold_214_, v___x_216_);
v___x_218_ = lean_uint64_to_usize(v___x_217_);
v___x_219_ = lean_usize_of_nat(v___x_210_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_sub(v___x_219_, v___x_220_);
v___x_222_ = lean_usize_land(v___x_218_, v___x_221_);
v___x_223_ = lean_array_uget_borrowed(v_x_202_, v___x_222_);
lean_inc(v___x_223_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 2, v___x_223_);
v___x_225_ = v___x_208_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_key_204_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_value_205_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v___x_223_);
v___x_225_ = v_reuseFailAlloc_228_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = lean_array_uset(v_x_202_, v___x_222_, v___x_225_);
v_x_202_ = v___x_226_;
v_x_203_ = v_tail_206_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3___redArg(lean_object* v_i_230_, lean_object* v_source_231_, lean_object* v_target_232_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_array_get_size(v_source_231_);
v___x_234_ = lean_nat_dec_lt(v_i_230_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v_source_231_);
lean_dec(v_i_230_);
return v_target_232_;
}
else
{
lean_object* v_es_235_; lean_object* v___x_236_; lean_object* v_source_237_; lean_object* v_target_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_es_235_ = lean_array_fget(v_source_231_, v_i_230_);
v___x_236_ = lean_box(0);
v_source_237_ = lean_array_fset(v_source_231_, v_i_230_, v___x_236_);
v_target_238_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3_spec__4___redArg(v_target_232_, v_es_235_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_i_230_, v___x_239_);
lean_dec(v_i_230_);
v_i_230_ = v___x_240_;
v_source_231_ = v_source_237_;
v_target_232_ = v_target_238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2___redArg(lean_object* v_data_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_nbuckets_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_243_ = lean_array_get_size(v_data_242_);
v___x_244_ = lean_unsigned_to_nat(2u);
v_nbuckets_245_ = lean_nat_mul(v___x_243_, v___x_244_);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_box(0);
v___x_248_ = lean_mk_array(v_nbuckets_245_, v___x_247_);
v___x_249_ = lean_array_propagate_mark(v_data_242_, v___x_248_);
v___x_250_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3___redArg(v___x_246_, v_data_242_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1___redArg(lean_object* v_m_251_, lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
lean_object* v_size_254_; lean_object* v_buckets_255_; lean_object* v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v_fold_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v_bkt_269_; uint8_t v___x_270_; 
v_size_254_ = lean_ctor_get(v_m_251_, 0);
v_buckets_255_ = lean_ctor_get(v_m_251_, 1);
v___x_256_ = lean_array_get_size(v_buckets_255_);
v___x_257_ = l_Lean_Expr_hash(v_a_252_);
v___x_258_ = 32ULL;
v___x_259_ = lean_uint64_shift_right(v___x_257_, v___x_258_);
v_fold_260_ = lean_uint64_xor(v___x_257_, v___x_259_);
v___x_261_ = 16ULL;
v___x_262_ = lean_uint64_shift_right(v_fold_260_, v___x_261_);
v___x_263_ = lean_uint64_xor(v_fold_260_, v___x_262_);
v___x_264_ = lean_uint64_to_usize(v___x_263_);
v___x_265_ = lean_usize_of_nat(v___x_256_);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_sub(v___x_265_, v___x_266_);
v___x_268_ = lean_usize_land(v___x_264_, v___x_267_);
v_bkt_269_ = lean_array_uget_borrowed(v_buckets_255_, v___x_268_);
v___x_270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(v_a_252_, v_bkt_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_291_; 
lean_inc_ref(v_buckets_255_);
lean_inc(v_size_254_);
v_isSharedCheck_291_ = !lean_is_exclusive(v_m_251_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_292_ = lean_ctor_get(v_m_251_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_m_251_, 0);
lean_dec(v_unused_293_);
v___x_272_ = v_m_251_;
v_isShared_273_ = v_isSharedCheck_291_;
goto v_resetjp_271_;
}
else
{
lean_dec(v_m_251_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_291_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v_size_x27_275_; lean_object* v___x_276_; lean_object* v_buckets_x27_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v_size_x27_275_ = lean_nat_add(v_size_254_, v___x_274_);
lean_dec(v_size_254_);
lean_inc(v_bkt_269_);
v___x_276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_276_, 0, v_a_252_);
lean_ctor_set(v___x_276_, 1, v_b_253_);
lean_ctor_set(v___x_276_, 2, v_bkt_269_);
v_buckets_x27_277_ = lean_array_uset(v_buckets_255_, v___x_268_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(4u);
v___x_279_ = lean_nat_mul(v_size_x27_275_, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(3u);
v___x_281_ = lean_nat_div(v___x_279_, v___x_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_array_get_size(v_buckets_x27_277_);
v___x_283_ = lean_nat_dec_le(v___x_281_, v___x_282_);
lean_dec(v___x_281_);
if (v___x_283_ == 0)
{
lean_object* v_val_284_; lean_object* v___x_286_; 
v_val_284_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2___redArg(v_buckets_x27_277_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v_val_284_);
lean_ctor_set(v___x_272_, 0, v_size_x27_275_);
v___x_286_ = v___x_272_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_size_x27_275_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_val_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_289_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v_buckets_x27_277_);
lean_ctor_set(v___x_272_, 0, v_size_x27_275_);
v___x_289_ = v___x_272_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_size_x27_275_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_buckets_x27_277_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_dec(v_b_253_);
lean_dec_ref(v_a_252_);
return v_m_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm(lean_object* v_cls_294_, lean_object* v_term_295_){
_start:
{
lean_object* v_sort_296_; uint8_t v_full_297_; lean_object* v_terms_298_; lean_object* v_termSet_299_; lean_object* v_exceptions_300_; lean_object* v_avoid_301_; uint8_t v___x_302_; 
v_sort_296_ = lean_ctor_get(v_cls_294_, 0);
v_full_297_ = lean_ctor_get_uint8(v_cls_294_, sizeof(void*)*5);
v_terms_298_ = lean_ctor_get(v_cls_294_, 1);
v_termSet_299_ = lean_ctor_get(v_cls_294_, 2);
v_exceptions_300_ = lean_ctor_get(v_cls_294_, 3);
v_avoid_301_ = lean_ctor_get(v_cls_294_, 4);
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(v_termSet_299_, v_term_295_);
if (v___x_302_ == 0)
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_312_; 
lean_inc_ref(v_avoid_301_);
lean_inc_ref(v_exceptions_300_);
lean_inc_ref(v_termSet_299_);
lean_inc_ref(v_terms_298_);
lean_inc(v_sort_296_);
v_isSharedCheck_312_ = !lean_is_exclusive(v_cls_294_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_313_ = lean_ctor_get(v_cls_294_, 4);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_cls_294_, 3);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_cls_294_, 2);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_cls_294_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_cls_294_, 0);
lean_dec(v_unused_317_);
v___x_304_ = v_cls_294_;
v_isShared_305_ = v_isSharedCheck_312_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_cls_294_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_312_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
lean_inc_ref(v_term_295_);
v___x_306_ = lean_array_push(v_terms_298_, v_term_295_);
v___x_307_ = lean_box(0);
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1___redArg(v_termSet_299_, v_term_295_, v___x_307_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 2, v___x_308_);
lean_ctor_set(v___x_304_, 1, v___x_306_);
v___x_310_ = v___x_304_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_sort_296_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_exceptions_300_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_avoid_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*5, v_full_297_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_dec_ref(v_term_295_);
return v_cls_294_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0(lean_object* v_00_u03b2_318_, lean_object* v_m_319_, lean_object* v_a_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(v_m_319_, v_a_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___boxed(lean_object* v_00_u03b2_322_, lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0(v_00_u03b2_322_, v_m_323_, v_a_324_);
lean_dec_ref(v_a_324_);
lean_dec_ref(v_m_323_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_a_329_, lean_object* v_b_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1___redArg(v_m_328_, v_a_329_, v_b_330_);
return v___x_331_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0(lean_object* v_00_u03b2_332_, lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(v_a_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_336_, lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0(v_00_u03b2_336_, v_a_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec_ref(v_a_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2(lean_object* v_00_u03b2_341_, lean_object* v_data_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2___redArg(v_data_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_344_, lean_object* v_i_345_, lean_object* v_source_346_, lean_object* v_target_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3___redArg(v_i_345_, v_source_346_, v_target_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2_spec__3_spec__4___redArg(v_x_350_, v_x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__0(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_unsigned_to_nat(16u);
v___x_355_ = lean_mk_array(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__0);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__3(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__2));
v___x_362_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__3);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets(void){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default;
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg(lean_object* v_sort_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v_uf_370_; lean_object* v_classSorts_371_; lean_object* v_varClasses_372_; lean_object* v_posClasses_373_; lean_object* v_inserts_374_; lean_object* v_exceptions_375_; lean_object* v_avoids_376_; lean_object* v_full_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_391_; 
v___x_369_ = lean_st_ref_take(v_a_367_);
v_uf_370_ = lean_ctor_get(v___x_369_, 0);
v_classSorts_371_ = lean_ctor_get(v___x_369_, 1);
v_varClasses_372_ = lean_ctor_get(v___x_369_, 2);
v_posClasses_373_ = lean_ctor_get(v___x_369_, 3);
v_inserts_374_ = lean_ctor_get(v___x_369_, 4);
v_exceptions_375_ = lean_ctor_get(v___x_369_, 5);
v_avoids_376_ = lean_ctor_get(v___x_369_, 6);
v_full_377_ = lean_ctor_get(v___x_369_, 7);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_391_ == 0)
{
v___x_379_ = v___x_369_;
v_isShared_380_ = v_isSharedCheck_391_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_full_377_);
lean_inc(v_avoids_376_);
lean_inc(v_exceptions_375_);
lean_inc(v_inserts_374_);
lean_inc(v_posClasses_373_);
lean_inc(v_varClasses_372_);
lean_inc(v_classSorts_371_);
lean_inc(v_uf_370_);
lean_dec(v___x_369_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_391_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_newNode_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v_newNode_381_ = lean_array_get_size(v_uf_370_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_383_, 0, v_newNode_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
lean_ctor_set(v___x_383_, 2, v_newNode_381_);
v___x_384_ = lean_array_push(v_uf_370_, v___x_383_);
v___x_385_ = lean_array_push(v_classSorts_371_, v_sort_366_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_385_);
lean_ctor_set(v___x_379_, 0, v___x_384_);
v___x_387_ = v___x_379_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_varClasses_372_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_posClasses_373_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_inserts_374_);
lean_ctor_set(v_reuseFailAlloc_390_, 5, v_exceptions_375_);
lean_ctor_set(v_reuseFailAlloc_390_, 6, v_avoids_376_);
lean_ctor_set(v_reuseFailAlloc_390_, 7, v_full_377_);
v___x_387_ = v_reuseFailAlloc_390_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_st_ref_put(v_a_367_, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_newNode_381_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg___boxed(lean_object* v_sort_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg(v_sort_392_, v_a_393_);
lean_dec(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass(lean_object* v_sort_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg(v_sort_396_, v_a_397_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___boxed(lean_object* v_sort_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass(v_sort_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg(lean_object* v_lhs_412_, lean_object* v_rhs_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v_uf_417_; lean_object* v_classSorts_418_; lean_object* v_varClasses_419_; lean_object* v_posClasses_420_; lean_object* v_inserts_421_; lean_object* v_exceptions_422_; lean_object* v_avoids_423_; lean_object* v_full_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_435_; 
v___x_416_ = lean_st_ref_take(v_a_414_);
v_uf_417_ = lean_ctor_get(v___x_416_, 0);
v_classSorts_418_ = lean_ctor_get(v___x_416_, 1);
v_varClasses_419_ = lean_ctor_get(v___x_416_, 2);
v_posClasses_420_ = lean_ctor_get(v___x_416_, 3);
v_inserts_421_ = lean_ctor_get(v___x_416_, 4);
v_exceptions_422_ = lean_ctor_get(v___x_416_, 5);
v_avoids_423_ = lean_ctor_get(v___x_416_, 6);
v_full_424_ = lean_ctor_get(v___x_416_, 7);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_435_ == 0)
{
v___x_426_ = v___x_416_;
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_full_424_);
lean_inc(v_avoids_423_);
lean_inc(v_exceptions_422_);
lean_inc(v_inserts_421_);
lean_inc(v_posClasses_420_);
lean_inc(v_varClasses_419_);
lean_inc(v_classSorts_418_);
lean_inc(v_uf_417_);
lean_dec(v___x_416_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_box(0);
v___x_429_ = l_Lean_UnionFind_union_x21(v_uf_417_, v_lhs_412_, v_rhs_413_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_classSorts_418_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_varClasses_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_posClasses_420_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v_inserts_421_);
lean_ctor_set(v_reuseFailAlloc_434_, 5, v_exceptions_422_);
lean_ctor_set(v_reuseFailAlloc_434_, 6, v_avoids_423_);
lean_ctor_set(v_reuseFailAlloc_434_, 7, v_full_424_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_st_ref_put(v_a_414_, v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_428_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg___boxed(lean_object* v_lhs_436_, lean_object* v_rhs_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg(v_lhs_436_, v_rhs_437_, v_a_438_);
lean_dec(v_a_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union(lean_object* v_lhs_441_, lean_object* v_rhs_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg(v_lhs_441_, v_rhs_442_, v_a_443_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___boxed(lean_object* v_lhs_450_, lean_object* v_rhs_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union(v_lhs_450_, v_rhs_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4___redArg(lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_dec(v_b_460_);
lean_dec_ref(v_a_459_);
return v_x_461_;
}
else
{
lean_object* v_key_462_; lean_object* v_value_463_; lean_object* v_tail_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_480_; 
v_key_462_ = lean_ctor_get(v_x_461_, 0);
v_value_463_ = lean_ctor_get(v_x_461_, 1);
v_tail_464_ = lean_ctor_get(v_x_461_, 2);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_480_ == 0)
{
v___x_466_ = v_x_461_;
v_isShared_467_ = v_isSharedCheck_480_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_tail_464_);
lean_inc(v_value_463_);
lean_inc(v_key_462_);
lean_dec(v_x_461_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_480_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v_fst_475_; lean_object* v_snd_476_; uint8_t v___x_477_; 
v_fst_473_ = lean_ctor_get(v_key_462_, 0);
v_snd_474_ = lean_ctor_get(v_key_462_, 1);
v_fst_475_ = lean_ctor_get(v_a_459_, 0);
v_snd_476_ = lean_ctor_get(v_a_459_, 1);
v___x_477_ = lean_expr_eqv(v_fst_473_, v_fst_475_);
if (v___x_477_ == 0)
{
goto v___jp_468_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_eq(v_snd_474_, v_snd_476_);
if (v___x_478_ == 0)
{
goto v___jp_468_;
}
else
{
lean_object* v___x_479_; 
lean_del_object(v___x_466_);
lean_dec(v_value_463_);
lean_dec(v_key_462_);
v___x_479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_479_, 0, v_a_459_);
lean_ctor_set(v___x_479_, 1, v_b_460_);
lean_ctor_set(v___x_479_, 2, v_tail_464_);
return v___x_479_;
}
}
v___jp_468_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4___redArg(v_a_459_, v_b_460_, v_tail_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 2, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_key_462_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_value_463_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_object* v_key_484_; lean_object* v_tail_485_; lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v_fst_488_; lean_object* v_snd_489_; uint8_t v___x_490_; 
v_key_484_ = lean_ctor_get(v_x_482_, 0);
v_tail_485_ = lean_ctor_get(v_x_482_, 2);
v_fst_486_ = lean_ctor_get(v_key_484_, 0);
v_snd_487_ = lean_ctor_get(v_key_484_, 1);
v_fst_488_ = lean_ctor_get(v_a_481_, 0);
v_snd_489_ = lean_ctor_get(v_a_481_, 1);
v___x_490_ = lean_expr_eqv(v_fst_486_, v_fst_488_);
if (v___x_490_ == 0)
{
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_eq(v_snd_487_, v_snd_489_);
if (v___x_492_ == 0)
{
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg___boxed(lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg(v_a_494_, v_x_495_);
lean_dec(v_x_495_);
lean_dec_ref(v_a_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
return v_x_498_;
}
else
{
lean_object* v_key_500_; lean_object* v_value_501_; lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_529_; 
v_key_500_ = lean_ctor_get(v_x_499_, 0);
v_value_501_ = lean_ctor_get(v_x_499_, 1);
v_tail_502_ = lean_ctor_get(v_x_499_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_529_ == 0)
{
v___x_504_ = v_x_499_;
v_isShared_505_ = v_isSharedCheck_529_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_inc(v_value_501_);
lean_inc(v_key_500_);
lean_dec(v_x_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_529_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_fold_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v_fst_506_ = lean_ctor_get(v_key_500_, 0);
v_snd_507_ = lean_ctor_get(v_key_500_, 1);
v___x_508_ = lean_array_get_size(v_x_498_);
v___x_509_ = l_Lean_Expr_hash(v_fst_506_);
v___x_510_ = lean_uint64_of_nat(v_snd_507_);
v___x_511_ = lean_uint64_mix_hash(v___x_509_, v___x_510_);
v___x_512_ = 32ULL;
v___x_513_ = lean_uint64_shift_right(v___x_511_, v___x_512_);
v_fold_514_ = lean_uint64_xor(v___x_511_, v___x_513_);
v___x_515_ = 16ULL;
v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = lean_usize_of_nat(v___x_508_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
v___x_523_ = lean_array_uget_borrowed(v_x_498_, v___x_522_);
lean_inc(v___x_523_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 2, v___x_523_);
v___x_525_ = v___x_504_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_key_500_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_value_501_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_523_);
v___x_525_ = v_reuseFailAlloc_528_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_array_uset(v_x_498_, v___x_522_, v___x_525_);
v_x_498_ = v___x_526_;
v_x_499_ = v_tail_502_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4___redArg(lean_object* v_i_530_, lean_object* v_source_531_, lean_object* v_target_532_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_array_get_size(v_source_531_);
v___x_534_ = lean_nat_dec_lt(v_i_530_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_source_531_);
lean_dec(v_i_530_);
return v_target_532_;
}
else
{
lean_object* v_es_535_; lean_object* v___x_536_; lean_object* v_source_537_; lean_object* v_target_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_es_535_ = lean_array_fget(v_source_531_, v_i_530_);
v___x_536_ = lean_box(0);
v_source_537_ = lean_array_fset(v_source_531_, v_i_530_, v___x_536_);
v_target_538_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4_spec__5___redArg(v_target_532_, v_es_535_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_i_530_, v___x_539_);
lean_dec(v_i_530_);
v_i_530_ = v___x_540_;
v_source_531_ = v_source_537_;
v_target_532_ = v_target_538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3___redArg(lean_object* v_data_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_nbuckets_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_543_ = lean_array_get_size(v_data_542_);
v___x_544_ = lean_unsigned_to_nat(2u);
v_nbuckets_545_ = lean_nat_mul(v___x_543_, v___x_544_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_box(0);
v___x_548_ = lean_mk_array(v_nbuckets_545_, v___x_547_);
v___x_549_ = lean_array_propagate_mark(v_data_542_, v___x_548_);
v___x_550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4___redArg(v___x_546_, v_data_542_, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1___redArg(lean_object* v_m_551_, lean_object* v_a_552_, lean_object* v_b_553_){
_start:
{
lean_object* v_size_554_; lean_object* v_buckets_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_602_; 
v_size_554_ = lean_ctor_get(v_m_551_, 0);
v_buckets_555_ = lean_ctor_get(v_m_551_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_m_551_);
if (v_isSharedCheck_602_ == 0)
{
v___x_557_ = v_m_551_;
v_isShared_558_ = v_isSharedCheck_602_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_buckets_555_);
lean_inc(v_size_554_);
lean_dec(v_m_551_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_602_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_561_; uint64_t v___x_562_; uint64_t v___x_563_; uint64_t v___x_564_; uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v_fold_567_; uint64_t v___x_568_; uint64_t v___x_569_; uint64_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v_bkt_576_; uint8_t v___x_577_; 
v_fst_559_ = lean_ctor_get(v_a_552_, 0);
v_snd_560_ = lean_ctor_get(v_a_552_, 1);
v___x_561_ = lean_array_get_size(v_buckets_555_);
v___x_562_ = l_Lean_Expr_hash(v_fst_559_);
v___x_563_ = lean_uint64_of_nat(v_snd_560_);
v___x_564_ = lean_uint64_mix_hash(v___x_562_, v___x_563_);
v___x_565_ = 32ULL;
v___x_566_ = lean_uint64_shift_right(v___x_564_, v___x_565_);
v_fold_567_ = lean_uint64_xor(v___x_564_, v___x_566_);
v___x_568_ = 16ULL;
v___x_569_ = lean_uint64_shift_right(v_fold_567_, v___x_568_);
v___x_570_ = lean_uint64_xor(v_fold_567_, v___x_569_);
v___x_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = lean_usize_of_nat(v___x_561_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_sub(v___x_572_, v___x_573_);
v___x_575_ = lean_usize_land(v___x_571_, v___x_574_);
v_bkt_576_ = lean_array_uget_borrowed(v_buckets_555_, v___x_575_);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg(v_a_552_, v_bkt_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v_size_x27_579_; lean_object* v___x_580_; lean_object* v_buckets_x27_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v_size_x27_579_ = lean_nat_add(v_size_554_, v___x_578_);
lean_dec(v_size_554_);
lean_inc(v_bkt_576_);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v_a_552_);
lean_ctor_set(v___x_580_, 1, v_b_553_);
lean_ctor_set(v___x_580_, 2, v_bkt_576_);
v_buckets_x27_581_ = lean_array_uset(v_buckets_555_, v___x_575_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(4u);
v___x_583_ = lean_nat_mul(v_size_x27_579_, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(3u);
v___x_585_ = lean_nat_div(v___x_583_, v___x_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_array_get_size(v_buckets_x27_581_);
v___x_587_ = lean_nat_dec_le(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
if (v___x_587_ == 0)
{
lean_object* v_val_588_; lean_object* v___x_590_; 
v_val_588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3___redArg(v_buckets_x27_581_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_val_588_);
lean_ctor_set(v___x_557_, 0, v_size_x27_579_);
v___x_590_ = v___x_557_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_size_x27_579_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_val_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_593_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_buckets_x27_581_);
lean_ctor_set(v___x_557_, 0, v_size_x27_579_);
v___x_593_ = v___x_557_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_size_x27_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_buckets_x27_581_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v___x_595_; lean_object* v_buckets_x27_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
lean_inc(v_bkt_576_);
v___x_595_ = lean_box(0);
v_buckets_x27_596_ = lean_array_uset(v_buckets_555_, v___x_575_, v___x_595_);
v___x_597_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4___redArg(v_a_552_, v_b_553_, v_bkt_576_);
v___x_598_ = lean_array_uset(v_buckets_x27_596_, v___x_575_, v___x_597_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_598_);
v___x_600_ = v___x_557_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_size_554_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg(lean_object* v_a_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(0);
return v___x_605_;
}
else
{
lean_object* v_key_606_; lean_object* v_value_607_; lean_object* v_tail_608_; lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v_fst_611_; lean_object* v_snd_612_; uint8_t v___x_613_; 
v_key_606_ = lean_ctor_get(v_x_604_, 0);
v_value_607_ = lean_ctor_get(v_x_604_, 1);
v_tail_608_ = lean_ctor_get(v_x_604_, 2);
v_fst_609_ = lean_ctor_get(v_key_606_, 0);
v_snd_610_ = lean_ctor_get(v_key_606_, 1);
v_fst_611_ = lean_ctor_get(v_a_603_, 0);
v_snd_612_ = lean_ctor_get(v_a_603_, 1);
v___x_613_ = lean_expr_eqv(v_fst_609_, v_fst_611_);
if (v___x_613_ == 0)
{
v_x_604_ = v_tail_608_;
goto _start;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_eq(v_snd_610_, v_snd_612_);
if (v___x_615_ == 0)
{
v_x_604_ = v_tail_608_;
goto _start;
}
else
{
lean_object* v___x_617_; 
lean_inc(v_value_607_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_value_607_);
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg___boxed(lean_object* v_a_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg(v_a_618_, v_x_619_);
lean_dec(v_x_619_);
lean_dec_ref(v_a_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg(lean_object* v_m_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_buckets_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_626_; uint64_t v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; uint64_t v___x_630_; uint64_t v___x_631_; uint64_t v_fold_632_; uint64_t v___x_633_; uint64_t v___x_634_; uint64_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_buckets_623_ = lean_ctor_get(v_m_621_, 1);
v_fst_624_ = lean_ctor_get(v_a_622_, 0);
v_snd_625_ = lean_ctor_get(v_a_622_, 1);
v___x_626_ = lean_array_get_size(v_buckets_623_);
v___x_627_ = l_Lean_Expr_hash(v_fst_624_);
v___x_628_ = lean_uint64_of_nat(v_snd_625_);
v___x_629_ = lean_uint64_mix_hash(v___x_627_, v___x_628_);
v___x_630_ = 32ULL;
v___x_631_ = lean_uint64_shift_right(v___x_629_, v___x_630_);
v_fold_632_ = lean_uint64_xor(v___x_629_, v___x_631_);
v___x_633_ = 16ULL;
v___x_634_ = lean_uint64_shift_right(v_fold_632_, v___x_633_);
v___x_635_ = lean_uint64_xor(v_fold_632_, v___x_634_);
v___x_636_ = lean_uint64_to_usize(v___x_635_);
v___x_637_ = lean_usize_of_nat(v___x_626_);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_sub(v___x_637_, v___x_638_);
v___x_640_ = lean_usize_land(v___x_636_, v___x_639_);
v___x_641_ = lean_array_uget_borrowed(v_buckets_623_, v___x_640_);
v___x_642_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg(v_a_622_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg___boxed(lean_object* v_m_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg(v_m_643_, v_a_644_);
lean_dec_ref(v_a_644_);
lean_dec_ref(v_m_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg(lean_object* v_pred_646_, lean_object* v_idx_647_, lean_object* v_sort_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; lean_object* v_posClasses_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = lean_st_ref_get(v_a_649_);
v_posClasses_652_ = lean_ctor_get(v___x_651_, 3);
lean_inc_ref(v_posClasses_652_);
lean_dec(v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_pred_646_);
lean_ctor_set(v___x_653_, 1, v_idx_647_);
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg(v_posClasses_652_, v___x_653_);
lean_dec_ref(v_posClasses_652_);
if (lean_obj_tag(v___x_654_) == 1)
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref_known(v___x_653_, 2);
lean_dec(v_sort_648_);
v_val_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 0);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_val_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_689_; 
lean_dec(v___x_654_);
v___x_663_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg(v_sort_648_, v_a_649_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_689_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_689_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_689_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_uf_669_; lean_object* v_classSorts_670_; lean_object* v_varClasses_671_; lean_object* v_posClasses_672_; lean_object* v_inserts_673_; lean_object* v_exceptions_674_; lean_object* v_avoids_675_; lean_object* v_full_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_688_; 
v___x_668_ = lean_st_ref_take(v_a_649_);
v_uf_669_ = lean_ctor_get(v___x_668_, 0);
v_classSorts_670_ = lean_ctor_get(v___x_668_, 1);
v_varClasses_671_ = lean_ctor_get(v___x_668_, 2);
v_posClasses_672_ = lean_ctor_get(v___x_668_, 3);
v_inserts_673_ = lean_ctor_get(v___x_668_, 4);
v_exceptions_674_ = lean_ctor_get(v___x_668_, 5);
v_avoids_675_ = lean_ctor_get(v___x_668_, 6);
v_full_676_ = lean_ctor_get(v___x_668_, 7);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_688_ == 0)
{
v___x_678_ = v___x_668_;
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_full_676_);
lean_inc(v_avoids_675_);
lean_inc(v_exceptions_674_);
lean_inc(v_inserts_673_);
lean_inc(v_posClasses_672_);
lean_inc(v_varClasses_671_);
lean_inc(v_classSorts_670_);
lean_inc(v_uf_669_);
lean_dec(v___x_668_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
lean_inc(v_a_664_);
v___x_680_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1___redArg(v_posClasses_672_, v___x_653_, v_a_664_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 3, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_uf_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_classSorts_670_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_varClasses_671_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_inserts_673_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v_exceptions_674_);
lean_ctor_set(v_reuseFailAlloc_687_, 6, v_avoids_675_);
lean_ctor_set(v_reuseFailAlloc_687_, 7, v_full_676_);
v___x_682_ = v_reuseFailAlloc_687_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_st_ref_put(v_a_649_, v___x_682_);
if (v_isShared_667_ == 0)
{
v___x_685_ = v___x_666_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_664_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg___boxed(lean_object* v_pred_690_, lean_object* v_idx_691_, lean_object* v_sort_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg(v_pred_690_, v_idx_691_, v_sort_692_, v_a_693_);
lean_dec(v_a_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass(lean_object* v_pred_696_, lean_object* v_idx_697_, lean_object* v_sort_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg(v_pred_696_, v_idx_697_, v_sort_698_, v_a_699_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___boxed(lean_object* v_pred_706_, lean_object* v_idx_707_, lean_object* v_sort_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass(v_pred_706_, v_idx_707_, v_sort_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0(lean_object* v_00_u03b2_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg(v_m_717_, v_a_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___boxed(lean_object* v_00_u03b2_720_, lean_object* v_m_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0(v_00_u03b2_720_, v_m_721_, v_a_722_);
lean_dec_ref(v_a_722_);
lean_dec_ref(v_m_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1(lean_object* v_00_u03b2_724_, lean_object* v_m_725_, lean_object* v_a_726_, lean_object* v_b_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1___redArg(v_m_725_, v_a_726_, v_b_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0(lean_object* v_00_u03b2_729_, lean_object* v_a_730_, lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___redArg(v_a_730_, v_x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_733_, lean_object* v_a_734_, lean_object* v_x_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0_spec__0(v_00_u03b2_733_, v_a_734_, v_x_735_);
lean_dec(v_x_735_);
lean_dec_ref(v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2(lean_object* v_00_u03b2_737_, lean_object* v_a_738_, lean_object* v_x_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___redArg(v_a_738_, v_x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2___boxed(lean_object* v_00_u03b2_741_, lean_object* v_a_742_, lean_object* v_x_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__2(v_00_u03b2_741_, v_a_742_, v_x_743_);
lean_dec(v_x_743_);
lean_dec_ref(v_a_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3(lean_object* v_00_u03b2_746_, lean_object* v_data_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3___redArg(v_data_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4(lean_object* v_00_u03b2_749_, lean_object* v_a_750_, lean_object* v_b_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__4___redArg(v_a_750_, v_b_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_754_, lean_object* v_i_755_, lean_object* v_source_756_, lean_object* v_target_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4___redArg(v_i_755_, v_source_756_, v_target_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1_spec__3_spec__4_spec__5___redArg(v_x_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorIdx___impl(lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_obj_tag_nat(v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorIdx___impl___boxed(lean_object* v_x_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorIdx___impl(v_x_765_);
lean_dec(v_x_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(lean_object* v_t_767_, lean_object* v_k_768_){
_start:
{
switch(lean_obj_tag(v_t_767_))
{
case 0:
{
lean_object* v_cls_769_; lean_object* v___x_770_; 
v_cls_769_ = lean_ctor_get(v_t_767_, 0);
lean_inc(v_cls_769_);
lean_dec_ref_known(v_t_767_, 1);
v___x_770_ = lean_apply_1(v_k_768_, v_cls_769_);
return v___x_770_;
}
case 1:
{
lean_object* v_elem_771_; lean_object* v___x_772_; 
v_elem_771_ = lean_ctor_get(v_t_767_, 0);
lean_inc_ref(v_elem_771_);
lean_dec_ref_known(v_t_767_, 1);
v___x_772_ = lean_apply_1(v_k_768_, v_elem_771_);
return v___x_772_;
}
default: 
{
return v_k_768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim(lean_object* v_motive_773_, lean_object* v_ctorIdx_774_, lean_object* v_t_775_, lean_object* v_h_776_, lean_object* v_k_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_775_, v_k_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___boxed(lean_object* v_motive_779_, lean_object* v_ctorIdx_780_, lean_object* v_t_781_, lean_object* v_h_782_, lean_object* v_k_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim(v_motive_779_, v_ctorIdx_780_, v_t_781_, v_h_782_, v_k_783_);
lean_dec(v_ctorIdx_780_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_var_elim___redArg(lean_object* v_t_785_, lean_object* v_var_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_785_, v_var_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_var_elim(lean_object* v_motive_788_, lean_object* v_t_789_, lean_object* v_h_790_, lean_object* v_var_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_789_, v_var_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ground_elim___redArg(lean_object* v_t_793_, lean_object* v_ground_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_793_, v_ground_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ground_elim(lean_object* v_motive_796_, lean_object* v_t_797_, lean_object* v_h_798_, lean_object* v_ground_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_797_, v_ground_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_other_elim___redArg(lean_object* v_t_801_, lean_object* v_other_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_801_, v_other_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_other_elim(lean_object* v_motive_804_, lean_object* v_t_805_, lean_object* v_h_806_, lean_object* v_other_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_Term_ctorElim___redArg(v_t_805_, v_other_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg(lean_object* v_a_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_box(0);
return v___x_811_;
}
else
{
lean_object* v_key_812_; lean_object* v_value_813_; lean_object* v_tail_814_; uint8_t v___x_815_; 
v_key_812_ = lean_ctor_get(v_x_810_, 0);
v_value_813_ = lean_ctor_get(v_x_810_, 1);
v_tail_814_ = lean_ctor_get(v_x_810_, 2);
v___x_815_ = lean_expr_eqv(v_key_812_, v_a_809_);
if (v___x_815_ == 0)
{
v_x_810_ = v_tail_814_;
goto _start;
}
else
{
lean_object* v___x_817_; 
lean_inc(v_value_813_);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_value_813_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg___boxed(lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg(v_a_818_, v_x_819_);
lean_dec(v_x_819_);
lean_dec_ref(v_a_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg(lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_buckets_823_; lean_object* v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v_fold_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_buckets_823_ = lean_ctor_get(v_m_821_, 1);
v___x_824_ = lean_array_get_size(v_buckets_823_);
v___x_825_ = l_Lean_Expr_hash(v_a_822_);
v___x_826_ = 32ULL;
v___x_827_ = lean_uint64_shift_right(v___x_825_, v___x_826_);
v_fold_828_ = lean_uint64_xor(v___x_825_, v___x_827_);
v___x_829_ = 16ULL;
v___x_830_ = lean_uint64_shift_right(v_fold_828_, v___x_829_);
v___x_831_ = lean_uint64_xor(v_fold_828_, v___x_830_);
v___x_832_ = lean_uint64_to_usize(v___x_831_);
v___x_833_ = lean_usize_of_nat(v___x_824_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_usize_land(v___x_832_, v___x_835_);
v___x_837_ = lean_array_uget_borrowed(v_buckets_823_, v___x_836_);
v___x_838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg(v_a_822_, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg___boxed(lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg(v_m_839_, v_a_840_);
lean_dec_ref(v_a_840_);
lean_dec_ref(v_m_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(lean_object* v_problem_842_, lean_object* v_varMap_843_, lean_object* v_e_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f(v_e_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = lean_box(2);
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_866_; 
v_val_847_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_866_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_866_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_866_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg(v_varMap_843_, v_val_847_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_object* v_val_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
v_val_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_val_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 0);
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_val_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_sortMap_860_; uint8_t v___x_861_; 
lean_dec(v___x_851_);
v_sortMap_860_ = lean_ctor_get(v_problem_842_, 1);
v___x_861_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(v_sortMap_860_, v_val_847_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
v___x_862_ = lean_box(2);
return v___x_862_;
}
else
{
lean_object* v___x_864_; 
if (v_isShared_850_ == 0)
{
v___x_864_ = v___x_849_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_val_847_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify___boxed(lean_object* v_problem_867_, lean_object* v_varMap_868_, lean_object* v_e_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(v_problem_867_, v_varMap_868_, v_e_869_);
lean_dec_ref(v_e_869_);
lean_dec_ref(v_varMap_868_);
lean_dec_ref(v_problem_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_m_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg(v_m_872_, v_a_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___boxed(lean_object* v_00_u03b2_875_, lean_object* v_m_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0(v_00_u03b2_875_, v_m_876_, v_a_877_);
lean_dec_ref(v_a_877_);
lean_dec_ref(v_m_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0(lean_object* v_00_u03b2_879_, lean_object* v_a_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___redArg(v_a_880_, v_x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0___boxed(lean_object* v_00_u03b2_883_, lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0_spec__0(v_00_u03b2_883_, v_a_884_, v_x_885_);
lean_dec(v_x_885_);
lean_dec_ref(v_a_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg(lean_object* v_upperBound_887_, lean_object* v_snd_888_, lean_object* v_problem_889_, lean_object* v_varMap_890_, lean_object* v_val_891_, lean_object* v_fst_892_, lean_object* v_a_893_, lean_object* v_b_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_a_898_; uint8_t v___x_902_; 
v___x_902_ = lean_nat_dec_lt(v_a_893_, v_upperBound_887_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_a_893_);
lean_dec_ref(v_fst_892_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v_b_894_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_box(0);
v___x_905_ = lean_array_fget_borrowed(v_snd_888_, v_a_893_);
v___x_906_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(v_problem_889_, v_varMap_890_, v___x_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_toPredInfo_907_; lean_object* v_cls_908_; lean_object* v_argumentSorts_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_toPredInfo_907_ = lean_ctor_get(v_val_891_, 0);
v_cls_908_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_cls_908_);
lean_dec_ref_known(v___x_906_, 1);
v_argumentSorts_909_ = lean_ctor_get(v_toPredInfo_907_, 0);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_array_get_borrowed(v___x_910_, v_argumentSorts_909_, v_a_893_);
lean_inc(v___x_911_);
lean_inc(v_a_893_);
lean_inc_ref(v_fst_892_);
v___x_912_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass___redArg(v_fst_892_, v_a_893_, v___x_911_, v___y_895_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg(v_cls_908_, v_a_913_, v___y_895_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_dec_ref_known(v___x_914_, 1);
v_a_898_ = v___x_904_;
goto v___jp_897_;
}
else
{
lean_dec(v_a_893_);
lean_dec_ref(v_fst_892_);
return v___x_914_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_cls_908_);
lean_dec(v_a_893_);
lean_dec_ref(v_fst_892_);
v_a_915_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_912_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_912_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_dec(v___x_906_);
v_a_898_ = v___x_904_;
goto v___jp_897_;
}
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_add(v_a_893_, v___x_899_);
lean_dec(v_a_893_);
v_a_893_ = v___x_900_;
v_b_894_ = v_a_898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg___boxed(lean_object* v_upperBound_923_, lean_object* v_snd_924_, lean_object* v_problem_925_, lean_object* v_varMap_926_, lean_object* v_val_927_, lean_object* v_fst_928_, lean_object* v_a_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg(v_upperBound_923_, v_snd_924_, v_problem_925_, v_varMap_926_, v_val_927_, v_fst_928_, v_a_929_, v_b_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v_val_927_);
lean_dec_ref(v_varMap_926_);
lean_dec_ref(v_problem_925_);
lean_dec_ref(v_snd_924_);
lean_dec(v_upperBound_923_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(lean_object* v_problem_939_, lean_object* v_varMap_940_, lean_object* v_atom_941_, uint8_t v_pol_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = l_Lean_Expr_cleanupAnnotations(v_atom_941_);
v___x_988_ = l_Lean_Expr_isApp(v___x_987_);
if (v___x_988_ == 0)
{
lean_dec_ref(v___x_987_);
v___y_950_ = v_a_943_;
v___y_951_ = v_a_944_;
v___y_952_ = v_a_945_;
v___y_953_ = v_a_946_;
v___y_954_ = v_a_947_;
goto v___jp_949_;
}
else
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_987_);
v___x_990_ = l_Lean_Expr_isApp(v___x_989_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
v___y_950_ = v_a_943_;
v___y_951_ = v_a_944_;
v___y_952_ = v_a_945_;
v___y_953_ = v_a_946_;
v___y_954_ = v_a_947_;
goto v___jp_949_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_989_);
v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
v___y_950_ = v_a_943_;
v___y_951_ = v_a_944_;
v___y_952_ = v_a_945_;
v___y_953_ = v_a_946_;
v___y_954_ = v_a_947_;
goto v___jp_949_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
lean_dec_ref(v___x_991_);
v___x_994_ = l_Lean_Expr_isApp(v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
v___y_950_ = v_a_943_;
v___y_951_ = v_a_944_;
v___y_952_ = v_a_945_;
v___y_953_ = v_a_946_;
v___y_954_ = v_a_947_;
goto v___jp_949_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_993_);
lean_dec_ref(v___x_993_);
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2));
v___x_997_ = l_Lean_Expr_isConstOf(v___x_995_, v___x_996_);
lean_dec_ref(v___x_995_);
if (v___x_997_ == 0)
{
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
v___y_950_ = v_a_943_;
v___y_951_ = v_a_944_;
v___y_952_ = v_a_945_;
v___y_953_ = v_a_946_;
v___y_954_ = v_a_947_;
goto v___jp_949_;
}
else
{
lean_object* v_arg_998_; lean_object* v_arg_999_; lean_object* v___x_1000_; 
lean_dec_ref(v_atom_941_);
v_arg_998_ = lean_ctor_get(v___x_987_, 1);
lean_inc_ref(v_arg_998_);
lean_dec_ref(v___x_987_);
v_arg_999_ = lean_ctor_get(v___x_989_, 1);
lean_inc_ref(v_arg_999_);
lean_dec_ref(v___x_989_);
v___x_1000_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(v_problem_939_, v_varMap_940_, v_arg_999_);
lean_dec_ref(v_arg_999_);
switch(lean_obj_tag(v___x_1000_))
{
case 0:
{
lean_object* v_cls_1001_; lean_object* v___x_1002_; 
v_cls_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_cls_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(v_problem_939_, v_varMap_940_, v_arg_998_);
lean_dec_ref(v_arg_998_);
switch(lean_obj_tag(v___x_1002_))
{
case 0:
{
if (v_pol_942_ == 0)
{
lean_object* v_cls_1003_; lean_object* v___x_1004_; 
v_cls_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_cls_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_union___redArg(v_cls_1001_, v_cls_1003_, v_a_943_);
return v___x_1004_;
}
else
{
lean_object* v_cls_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1034_; 
v_cls_1005_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1007_ = v___x_1002_;
v_isShared_1008_ = v_isSharedCheck_1034_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_cls_1005_);
lean_dec(v___x_1002_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1034_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_uf_1010_; lean_object* v_classSorts_1011_; lean_object* v_varClasses_1012_; lean_object* v_posClasses_1013_; lean_object* v_inserts_1014_; lean_object* v_exceptions_1015_; lean_object* v_avoids_1016_; lean_object* v_full_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1033_; 
v___x_1009_ = lean_st_ref_take(v_a_943_);
v_uf_1010_ = lean_ctor_get(v___x_1009_, 0);
v_classSorts_1011_ = lean_ctor_get(v___x_1009_, 1);
v_varClasses_1012_ = lean_ctor_get(v___x_1009_, 2);
v_posClasses_1013_ = lean_ctor_get(v___x_1009_, 3);
v_inserts_1014_ = lean_ctor_get(v___x_1009_, 4);
v_exceptions_1015_ = lean_ctor_get(v___x_1009_, 5);
v_avoids_1016_ = lean_ctor_get(v___x_1009_, 6);
v_full_1017_ = lean_ctor_get(v___x_1009_, 7);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1019_ = v___x_1009_;
v_isShared_1020_ = v_isSharedCheck_1033_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_full_1017_);
lean_inc(v_avoids_1016_);
lean_inc(v_exceptions_1015_);
lean_inc(v_inserts_1014_);
lean_inc(v_posClasses_1013_);
lean_inc(v_varClasses_1012_);
lean_inc(v_classSorts_1011_);
lean_inc(v_uf_1010_);
lean_dec(v___x_1009_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1033_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1021_ = lean_box(0);
lean_inc(v_cls_1005_);
lean_inc(v_cls_1001_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_cls_1001_);
lean_ctor_set(v___x_1022_, 1, v_cls_1005_);
v___x_1023_ = lean_array_push(v_avoids_1016_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_cls_1005_);
lean_ctor_set(v___x_1024_, 1, v_cls_1001_);
v___x_1025_ = lean_array_push(v___x_1023_, v___x_1024_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 6, v___x_1025_);
v___x_1027_ = v___x_1019_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_uf_1010_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_classSorts_1011_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_varClasses_1012_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_posClasses_1013_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_inserts_1014_);
lean_ctor_set(v_reuseFailAlloc_1032_, 5, v_exceptions_1015_);
lean_ctor_set(v_reuseFailAlloc_1032_, 6, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1032_, 7, v_full_1017_);
v___x_1027_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_st_ref_put(v_a_943_, v___x_1027_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1021_);
v___x_1030_ = v___x_1007_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1021_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
case 1:
{
if (v_pol_942_ == 0)
{
lean_object* v_elem_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1062_; 
v_elem_1035_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1037_ = v___x_1002_;
v_isShared_1038_ = v_isSharedCheck_1062_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_elem_1035_);
lean_dec(v___x_1002_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1062_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v_uf_1040_; lean_object* v_classSorts_1041_; lean_object* v_varClasses_1042_; lean_object* v_posClasses_1043_; lean_object* v_inserts_1044_; lean_object* v_exceptions_1045_; lean_object* v_avoids_1046_; lean_object* v_full_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1061_; 
v___x_1039_ = lean_st_ref_take(v_a_943_);
v_uf_1040_ = lean_ctor_get(v___x_1039_, 0);
v_classSorts_1041_ = lean_ctor_get(v___x_1039_, 1);
v_varClasses_1042_ = lean_ctor_get(v___x_1039_, 2);
v_posClasses_1043_ = lean_ctor_get(v___x_1039_, 3);
v_inserts_1044_ = lean_ctor_get(v___x_1039_, 4);
v_exceptions_1045_ = lean_ctor_get(v___x_1039_, 5);
v_avoids_1046_ = lean_ctor_get(v___x_1039_, 6);
v_full_1047_ = lean_ctor_get(v___x_1039_, 7);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1049_ = v___x_1039_;
v_isShared_1050_ = v_isSharedCheck_1061_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_full_1047_);
lean_inc(v_avoids_1046_);
lean_inc(v_exceptions_1045_);
lean_inc(v_inserts_1044_);
lean_inc(v_posClasses_1043_);
lean_inc(v_varClasses_1042_);
lean_inc(v_classSorts_1041_);
lean_inc(v_uf_1040_);
lean_dec(v___x_1039_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1061_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_cls_1001_);
lean_ctor_set(v___x_1052_, 1, v_elem_1035_);
v___x_1053_ = lean_array_push(v_inserts_1044_, v___x_1052_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 4, v___x_1053_);
v___x_1055_ = v___x_1049_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_uf_1040_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_classSorts_1041_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_varClasses_1042_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_posClasses_1043_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 5, v_exceptions_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 6, v_avoids_1046_);
lean_ctor_set(v_reuseFailAlloc_1060_, 7, v_full_1047_);
v___x_1055_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_st_ref_put(v_a_943_, v___x_1055_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1051_);
v___x_1058_ = v___x_1037_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1051_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
else
{
lean_object* v_elem_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1091_; 
v_elem_1063_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1065_ = v___x_1002_;
v_isShared_1066_ = v_isSharedCheck_1091_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_elem_1063_);
lean_dec(v___x_1002_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1091_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v_uf_1068_; lean_object* v_classSorts_1069_; lean_object* v_varClasses_1070_; lean_object* v_posClasses_1071_; lean_object* v_inserts_1072_; lean_object* v_exceptions_1073_; lean_object* v_avoids_1074_; lean_object* v_full_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1090_; 
v___x_1067_ = lean_st_ref_take(v_a_943_);
v_uf_1068_ = lean_ctor_get(v___x_1067_, 0);
v_classSorts_1069_ = lean_ctor_get(v___x_1067_, 1);
v_varClasses_1070_ = lean_ctor_get(v___x_1067_, 2);
v_posClasses_1071_ = lean_ctor_get(v___x_1067_, 3);
v_inserts_1072_ = lean_ctor_get(v___x_1067_, 4);
v_exceptions_1073_ = lean_ctor_get(v___x_1067_, 5);
v_avoids_1074_ = lean_ctor_get(v___x_1067_, 6);
v_full_1075_ = lean_ctor_get(v___x_1067_, 7);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1077_ = v___x_1067_;
v_isShared_1078_ = v_isSharedCheck_1090_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_full_1075_);
lean_inc(v_avoids_1074_);
lean_inc(v_exceptions_1073_);
lean_inc(v_inserts_1072_);
lean_inc(v_posClasses_1071_);
lean_inc(v_varClasses_1070_);
lean_inc(v_classSorts_1069_);
lean_inc(v_uf_1068_);
lean_dec(v___x_1067_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1090_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1079_ = lean_box(0);
lean_inc(v_cls_1001_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_cls_1001_);
lean_ctor_set(v___x_1080_, 1, v_elem_1063_);
v___x_1081_ = lean_array_push(v_exceptions_1073_, v___x_1080_);
v___x_1082_ = lean_array_push(v_full_1075_, v_cls_1001_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 7, v___x_1082_);
lean_ctor_set(v___x_1077_, 5, v___x_1081_);
v___x_1084_ = v___x_1077_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_uf_1068_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_classSorts_1069_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_varClasses_1070_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_posClasses_1071_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_inserts_1072_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_avoids_1074_);
lean_ctor_set(v_reuseFailAlloc_1089_, 7, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_st_ref_put(v_a_943_, v___x_1084_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1079_);
v___x_1087_ = v___x_1065_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1079_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
default: 
{
lean_dec(v___x_1002_);
lean_dec(v_cls_1001_);
goto v___jp_984_;
}
}
}
case 1:
{
lean_object* v_elem_1092_; lean_object* v___x_1093_; 
v_elem_1092_ = lean_ctor_get(v___x_1000_, 0);
lean_inc_ref(v_elem_1092_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1093_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify(v_problem_939_, v_varMap_940_, v_arg_998_);
lean_dec_ref(v_arg_998_);
if (lean_obj_tag(v___x_1093_) == 0)
{
if (v_pol_942_ == 0)
{
lean_object* v_cls_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1121_; 
v_cls_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_cls_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v_uf_1099_; lean_object* v_classSorts_1100_; lean_object* v_varClasses_1101_; lean_object* v_posClasses_1102_; lean_object* v_inserts_1103_; lean_object* v_exceptions_1104_; lean_object* v_avoids_1105_; lean_object* v_full_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1120_; 
v___x_1098_ = lean_st_ref_take(v_a_943_);
v_uf_1099_ = lean_ctor_get(v___x_1098_, 0);
v_classSorts_1100_ = lean_ctor_get(v___x_1098_, 1);
v_varClasses_1101_ = lean_ctor_get(v___x_1098_, 2);
v_posClasses_1102_ = lean_ctor_get(v___x_1098_, 3);
v_inserts_1103_ = lean_ctor_get(v___x_1098_, 4);
v_exceptions_1104_ = lean_ctor_get(v___x_1098_, 5);
v_avoids_1105_ = lean_ctor_get(v___x_1098_, 6);
v_full_1106_ = lean_ctor_get(v___x_1098_, 7);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1108_ = v___x_1098_;
v_isShared_1109_ = v_isSharedCheck_1120_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_full_1106_);
lean_inc(v_avoids_1105_);
lean_inc(v_exceptions_1104_);
lean_inc(v_inserts_1103_);
lean_inc(v_posClasses_1102_);
lean_inc(v_varClasses_1101_);
lean_inc(v_classSorts_1100_);
lean_inc(v_uf_1099_);
lean_dec(v___x_1098_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1120_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_cls_1094_);
lean_ctor_set(v___x_1111_, 1, v_elem_1092_);
v___x_1112_ = lean_array_push(v_inserts_1103_, v___x_1111_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1112_);
v___x_1114_ = v___x_1108_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_uf_1099_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_classSorts_1100_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_varClasses_1101_);
lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_posClasses_1102_);
lean_ctor_set(v_reuseFailAlloc_1119_, 4, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1119_, 5, v_exceptions_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 6, v_avoids_1105_);
lean_ctor_set(v_reuseFailAlloc_1119_, 7, v_full_1106_);
v___x_1114_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_st_ref_put(v_a_943_, v___x_1114_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1110_);
v___x_1117_ = v___x_1096_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1110_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
else
{
lean_object* v_cls_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1150_; 
v_cls_1122_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1124_ = v___x_1093_;
v_isShared_1125_ = v_isSharedCheck_1150_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_cls_1122_);
lean_dec(v___x_1093_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1150_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v_uf_1127_; lean_object* v_classSorts_1128_; lean_object* v_varClasses_1129_; lean_object* v_posClasses_1130_; lean_object* v_inserts_1131_; lean_object* v_exceptions_1132_; lean_object* v_avoids_1133_; lean_object* v_full_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1149_; 
v___x_1126_ = lean_st_ref_take(v_a_943_);
v_uf_1127_ = lean_ctor_get(v___x_1126_, 0);
v_classSorts_1128_ = lean_ctor_get(v___x_1126_, 1);
v_varClasses_1129_ = lean_ctor_get(v___x_1126_, 2);
v_posClasses_1130_ = lean_ctor_get(v___x_1126_, 3);
v_inserts_1131_ = lean_ctor_get(v___x_1126_, 4);
v_exceptions_1132_ = lean_ctor_get(v___x_1126_, 5);
v_avoids_1133_ = lean_ctor_get(v___x_1126_, 6);
v_full_1134_ = lean_ctor_get(v___x_1126_, 7);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1136_ = v___x_1126_;
v_isShared_1137_ = v_isSharedCheck_1149_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_full_1134_);
lean_inc(v_avoids_1133_);
lean_inc(v_exceptions_1132_);
lean_inc(v_inserts_1131_);
lean_inc(v_posClasses_1130_);
lean_inc(v_varClasses_1129_);
lean_inc(v_classSorts_1128_);
lean_inc(v_uf_1127_);
lean_dec(v___x_1126_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1149_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1138_ = lean_box(0);
lean_inc(v_cls_1122_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_cls_1122_);
lean_ctor_set(v___x_1139_, 1, v_elem_1092_);
v___x_1140_ = lean_array_push(v_exceptions_1132_, v___x_1139_);
v___x_1141_ = lean_array_push(v_full_1134_, v_cls_1122_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 7, v___x_1141_);
lean_ctor_set(v___x_1136_, 5, v___x_1140_);
v___x_1143_ = v___x_1136_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_uf_1127_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_classSorts_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_varClasses_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_posClasses_1130_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_inserts_1131_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 6, v_avoids_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 7, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_st_ref_put(v_a_943_, v___x_1143_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1138_);
v___x_1146_ = v___x_1124_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1138_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1093_);
lean_dec_ref(v_elem_1092_);
goto v___jp_984_;
}
}
default: 
{
lean_dec(v___x_1000_);
lean_dec_ref(v_arg_998_);
goto v___jp_984_;
}
}
}
}
}
}
}
v___jp_949_:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f(v_atom_941_);
if (lean_obj_tag(v___x_955_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_981_; 
v_val_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_981_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_981_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_981_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v_predInfo_962_; lean_object* v___x_963_; 
v_fst_960_ = lean_ctor_get(v_val_956_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_val_956_, 1);
lean_inc(v_snd_961_);
lean_dec(v_val_956_);
v_predInfo_962_ = lean_ctor_get(v_problem_939_, 2);
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_classify_spec__0___redArg(v_predInfo_962_, v_fst_960_);
if (lean_obj_tag(v___x_963_) == 1)
{
lean_object* v_val_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_958_);
v_val_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_array_get_size(v_snd_961_);
v___x_967_ = lean_box(0);
v___x_968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg(v___x_966_, v_snd_961_, v_problem_939_, v_varMap_940_, v_val_964_, v_fst_960_, v___x_965_, v___x_967_, v___y_950_);
lean_dec(v_val_964_);
lean_dec(v_snd_961_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_976_);
v___x_970_ = v___x_968_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_dec(v___x_968_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_967_);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
return v___x_968_;
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_979_; 
lean_dec(v___x_963_);
lean_dec(v_snd_961_);
lean_dec(v_fst_960_);
v___x_977_ = lean_box(0);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 0);
lean_ctor_set(v___x_958_, 0, v___x_977_);
v___x_979_ = v___x_958_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v___x_955_);
v___x_982_ = lean_box(0);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___boxed(lean_object* v_problem_1151_, lean_object* v_varMap_1152_, lean_object* v_atom_1153_, lean_object* v_pol_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
uint8_t v_pol_boxed_1161_; lean_object* v_res_1162_; 
v_pol_boxed_1161_ = lean_unbox(v_pol_1154_);
v_res_1162_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1151_, v_varMap_1152_, v_atom_1153_, v_pol_boxed_1161_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_varMap_1152_);
lean_dec_ref(v_problem_1151_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0(lean_object* v_upperBound_1163_, lean_object* v_snd_1164_, lean_object* v_problem_1165_, lean_object* v_varMap_1166_, lean_object* v_val_1167_, lean_object* v_fst_1168_, lean_object* v_inst_1169_, lean_object* v_R_1170_, lean_object* v_a_1171_, lean_object* v_b_1172_, lean_object* v_c_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___redArg(v_upperBound_1163_, v_snd_1164_, v_problem_1165_, v_varMap_1166_, v_val_1167_, v_fst_1168_, v_a_1171_, v_b_1172_, v___y_1174_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1181_ = _args[0];
lean_object* v_snd_1182_ = _args[1];
lean_object* v_problem_1183_ = _args[2];
lean_object* v_varMap_1184_ = _args[3];
lean_object* v_val_1185_ = _args[4];
lean_object* v_fst_1186_ = _args[5];
lean_object* v_inst_1187_ = _args[6];
lean_object* v_R_1188_ = _args[7];
lean_object* v_a_1189_ = _args[8];
lean_object* v_b_1190_ = _args[9];
lean_object* v_c_1191_ = _args[10];
lean_object* v___y_1192_ = _args[11];
lean_object* v___y_1193_ = _args[12];
lean_object* v___y_1194_ = _args[13];
lean_object* v___y_1195_ = _args[14];
lean_object* v___y_1196_ = _args[15];
lean_object* v___y_1197_ = _args[16];
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom_spec__0(v_upperBound_1181_, v_snd_1182_, v_problem_1183_, v_varMap_1184_, v_val_1185_, v_fst_1186_, v_inst_1187_, v_R_1188_, v_a_1189_, v_b_1190_, v_c_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_val_1185_);
lean_dec_ref(v_varMap_1184_);
lean_dec_ref(v_problem_1183_);
lean_dec_ref(v_snd_1182_);
lean_dec(v_upperBound_1181_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___lam__0(lean_object* v_k_1199_, lean_object* v___y_1200_, lean_object* v_b_1201_, lean_object* v_c_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1200_);
v___x_1208_ = lean_apply_8(v_k_1199_, v_b_1201_, v_c_1202_, v___y_1200_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, lean_box(0));
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___lam__0___boxed(lean_object* v_k_1209_, lean_object* v___y_1210_, lean_object* v_b_1211_, lean_object* v_c_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___lam__0(v_k_1209_, v___y_1210_, v_b_1211_, v_c_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1210_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg(lean_object* v_type_1219_, lean_object* v_maxFVars_x3f_1220_, lean_object* v_k_1221_, uint8_t v_cleanupAnnotations_1222_, uint8_t v_whnfType_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___f_1230_; lean_object* v___x_1231_; 
lean_inc(v___y_1224_);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1230_, 0, v_k_1221_);
lean_closure_set(v___f_1230_, 1, v___y_1224_);
v___x_1231_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1219_, v_maxFVars_x3f_1220_, v___f_1230_, v_cleanupAnnotations_1222_, v_whnfType_1223_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1231_) == 0)
{
return v___x_1231_;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg___boxed(lean_object* v_type_1240_, lean_object* v_maxFVars_x3f_1241_, lean_object* v_k_1242_, lean_object* v_cleanupAnnotations_1243_, lean_object* v_whnfType_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1251_; uint8_t v_whnfType_boxed_1252_; lean_object* v_res_1253_; 
v_cleanupAnnotations_boxed_1251_ = lean_unbox(v_cleanupAnnotations_1243_);
v_whnfType_boxed_1252_ = lean_unbox(v_whnfType_1244_);
v_res_1253_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg(v_type_1240_, v_maxFVars_x3f_1241_, v_k_1242_, v_cleanupAnnotations_boxed_1251_, v_whnfType_boxed_1252_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4(lean_object* v_00_u03b1_1254_, lean_object* v_type_1255_, lean_object* v_maxFVars_x3f_1256_, lean_object* v_k_1257_, uint8_t v_cleanupAnnotations_1258_, uint8_t v_whnfType_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg(v_type_1255_, v_maxFVars_x3f_1256_, v_k_1257_, v_cleanupAnnotations_1258_, v_whnfType_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_type_1268_, lean_object* v_maxFVars_x3f_1269_, lean_object* v_k_1270_, lean_object* v_cleanupAnnotations_1271_, lean_object* v_whnfType_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1279_; uint8_t v_whnfType_boxed_1280_; lean_object* v_res_1281_; 
v_cleanupAnnotations_boxed_1279_ = lean_unbox(v_cleanupAnnotations_1271_);
v_whnfType_boxed_1280_ = lean_unbox(v_whnfType_1272_);
v_res_1281_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4(v_00_u03b1_1267_, v_type_1268_, v_maxFVars_x3f_1269_, v_k_1270_, v_cleanupAnnotations_boxed_1279_, v_whnfType_boxed_1280_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0___redArg(lean_object* v_a_1282_, lean_object* v_b_1283_, lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1284_) == 0)
{
lean_dec(v_b_1283_);
lean_dec_ref(v_a_1282_);
return v_x_1284_;
}
else
{
lean_object* v_key_1285_; lean_object* v_value_1286_; lean_object* v_tail_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1299_; 
v_key_1285_ = lean_ctor_get(v_x_1284_, 0);
v_value_1286_ = lean_ctor_get(v_x_1284_, 1);
v_tail_1287_ = lean_ctor_get(v_x_1284_, 2);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_x_1284_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1289_ = v_x_1284_;
v_isShared_1290_ = v_isSharedCheck_1299_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_tail_1287_);
lean_inc(v_value_1286_);
lean_inc(v_key_1285_);
lean_dec(v_x_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1299_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_expr_eqv(v_key_1285_, v_a_1282_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0___redArg(v_a_1282_, v_b_1283_, v_tail_1287_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 2, v___x_1292_);
v___x_1294_ = v___x_1289_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_key_1285_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_value_1286_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
else
{
lean_object* v___x_1297_; 
lean_dec(v_value_1286_);
lean_dec(v_key_1285_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v_b_1283_);
lean_ctor_set(v___x_1289_, 0, v_a_1282_);
v___x_1297_ = v___x_1289_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1282_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_b_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_tail_1287_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0___redArg(lean_object* v_m_1300_, lean_object* v_a_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v_size_1303_; lean_object* v_buckets_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1347_; 
v_size_1303_ = lean_ctor_get(v_m_1300_, 0);
v_buckets_1304_ = lean_ctor_get(v_m_1300_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_m_1300_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1306_ = v_m_1300_;
v_isShared_1307_ = v_isSharedCheck_1347_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_buckets_1304_);
lean_inc(v_size_1303_);
lean_dec(v_m_1300_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1347_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v_fold_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v_bkt_1321_; uint8_t v___x_1322_; 
v___x_1308_ = lean_array_get_size(v_buckets_1304_);
v___x_1309_ = l_Lean_Expr_hash(v_a_1301_);
v___x_1310_ = 32ULL;
v___x_1311_ = lean_uint64_shift_right(v___x_1309_, v___x_1310_);
v_fold_1312_ = lean_uint64_xor(v___x_1309_, v___x_1311_);
v___x_1313_ = 16ULL;
v___x_1314_ = lean_uint64_shift_right(v_fold_1312_, v___x_1313_);
v___x_1315_ = lean_uint64_xor(v_fold_1312_, v___x_1314_);
v___x_1316_ = lean_uint64_to_usize(v___x_1315_);
v___x_1317_ = lean_usize_of_nat(v___x_1308_);
v___x_1318_ = ((size_t)1ULL);
v___x_1319_ = lean_usize_sub(v___x_1317_, v___x_1318_);
v___x_1320_ = lean_usize_land(v___x_1316_, v___x_1319_);
v_bkt_1321_ = lean_array_uget_borrowed(v_buckets_1304_, v___x_1320_);
v___x_1322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0_spec__0___redArg(v_a_1301_, v_bkt_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v_size_x27_1324_; lean_object* v___x_1325_; lean_object* v_buckets_x27_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v_size_x27_1324_ = lean_nat_add(v_size_1303_, v___x_1323_);
lean_dec(v_size_1303_);
lean_inc(v_bkt_1321_);
v___x_1325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1325_, 0, v_a_1301_);
lean_ctor_set(v___x_1325_, 1, v_b_1302_);
lean_ctor_set(v___x_1325_, 2, v_bkt_1321_);
v_buckets_x27_1326_ = lean_array_uset(v_buckets_1304_, v___x_1320_, v___x_1325_);
v___x_1327_ = lean_unsigned_to_nat(4u);
v___x_1328_ = lean_nat_mul(v_size_x27_1324_, v___x_1327_);
v___x_1329_ = lean_unsigned_to_nat(3u);
v___x_1330_ = lean_nat_div(v___x_1328_, v___x_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_array_get_size(v_buckets_x27_1326_);
v___x_1332_ = lean_nat_dec_le(v___x_1330_, v___x_1331_);
lean_dec(v___x_1330_);
if (v___x_1332_ == 0)
{
lean_object* v_val_1333_; lean_object* v___x_1335_; 
v_val_1333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1_spec__2___redArg(v_buckets_x27_1326_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v_val_1333_);
lean_ctor_set(v___x_1306_, 0, v_size_x27_1324_);
v___x_1335_ = v___x_1306_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_size_x27_1324_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_val_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
else
{
lean_object* v___x_1338_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v_buckets_x27_1326_);
lean_ctor_set(v___x_1306_, 0, v_size_x27_1324_);
v___x_1338_ = v___x_1306_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_size_x27_1324_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_buckets_x27_1326_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v_buckets_x27_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
lean_inc(v_bkt_1321_);
v___x_1340_ = lean_box(0);
v_buckets_x27_1341_ = lean_array_uset(v_buckets_1304_, v___x_1320_, v___x_1340_);
v___x_1342_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0___redArg(v_a_1301_, v_b_1302_, v_bkt_1321_);
v___x_1343_ = lean_array_uset(v_buckets_x27_1341_, v___x_1320_, v___x_1342_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1343_);
v___x_1345_ = v___x_1306_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_size_1303_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg(lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_b_1351_);
return v___x_1354_;
}
else
{
lean_object* v_snd_1355_; lean_object* v_fst_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1389_; 
v_snd_1355_ = lean_ctor_get(v_b_1351_, 1);
v_fst_1356_ = lean_ctor_get(v_b_1351_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1358_ = v_b_1351_;
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1356_);
lean_dec(v_b_1351_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1389_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_array_1360_; lean_object* v_start_1361_; lean_object* v_stop_1362_; uint8_t v___x_1363_; 
v_array_1360_ = lean_ctor_get(v_snd_1355_, 0);
v_start_1361_ = lean_ctor_get(v_snd_1355_, 1);
v_stop_1362_ = lean_ctor_get(v_snd_1355_, 2);
v___x_1363_ = lean_nat_dec_lt(v_start_1361_, v_stop_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1365_; 
if (v_isShared_1359_ == 0)
{
v___x_1365_ = v___x_1358_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1356_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1355_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
else
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1385_; 
lean_inc(v_stop_1362_);
lean_inc(v_start_1361_);
lean_inc_ref(v_array_1360_);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_snd_1355_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; lean_object* v_unused_1387_; lean_object* v_unused_1388_; 
v_unused_1386_ = lean_ctor_get(v_snd_1355_, 2);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_snd_1355_, 1);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_snd_1355_, 0);
lean_dec(v_unused_1388_);
v___x_1369_ = v_snd_1355_;
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v_snd_1355_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v_a_1371_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
v___x_1372_ = lean_array_fget(v_array_1360_, v_start_1361_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_add(v_start_1361_, v___x_1373_);
lean_dec(v_start_1361_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v___x_1374_);
v___x_1376_ = v___x_1369_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_array_1360_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_stop_1362_);
v___x_1376_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_inc(v_a_1371_);
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0___redArg(v_fst_1356_, v_a_1371_, v___x_1372_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1376_);
lean_ctor_set(v___x_1358_, 0, v___x_1377_);
v___x_1379_ = v___x_1358_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1376_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1350_, v___x_1380_);
v_i_1350_ = v___x_1381_;
v_b_1351_ = v___x_1379_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg___boxed(lean_object* v_as_1390_, lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg(v_as_1390_, v_sz_boxed_1395_, v_i_boxed_1396_, v_b_1393_);
lean_dec_ref(v_as_1390_);
return v_res_1397_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_instMonadEIO___redArg();
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11(lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_toApplicative_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1476_; 
v___x_1411_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__0);
v___x_1412_ = l_StateRefT_x27_instMonad___redArg(v___x_1411_);
v_toApplicative_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1412_, 1);
lean_dec(v_unused_1477_);
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1476_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_toApplicative_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1476_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_toFunctor_1417_; lean_object* v_toSeq_1418_; lean_object* v_toSeqLeft_1419_; lean_object* v_toSeqRight_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1474_; 
v_toFunctor_1417_ = lean_ctor_get(v_toApplicative_1413_, 0);
v_toSeq_1418_ = lean_ctor_get(v_toApplicative_1413_, 2);
v_toSeqLeft_1419_ = lean_ctor_get(v_toApplicative_1413_, 3);
v_toSeqRight_1420_ = lean_ctor_get(v_toApplicative_1413_, 4);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_toApplicative_1413_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_toApplicative_1413_, 1);
lean_dec(v_unused_1475_);
v___x_1422_ = v_toApplicative_1413_;
v_isShared_1423_ = v_isSharedCheck_1474_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_toSeqRight_1420_);
lean_inc(v_toSeqLeft_1419_);
lean_inc(v_toSeq_1418_);
lean_inc(v_toFunctor_1417_);
lean_dec(v_toApplicative_1413_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1474_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___f_1424_; lean_object* v___f_1425_; lean_object* v___f_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; lean_object* v___f_1430_; lean_object* v___f_1431_; lean_object* v___x_1433_; 
v___f_1424_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__1));
v___f_1425_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__2));
lean_inc_ref(v_toFunctor_1417_);
v___f_1426_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1426_, 0, v_toFunctor_1417_);
v___f_1427_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1427_, 0, v_toFunctor_1417_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___f_1426_);
lean_ctor_set(v___x_1428_, 1, v___f_1427_);
v___f_1429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1429_, 0, v_toSeqRight_1420_);
v___f_1430_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1430_, 0, v_toSeqLeft_1419_);
v___f_1431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1431_, 0, v_toSeq_1418_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v___f_1429_);
lean_ctor_set(v___x_1422_, 3, v___f_1430_);
lean_ctor_set(v___x_1422_, 2, v___f_1431_);
lean_ctor_set(v___x_1422_, 1, v___f_1424_);
lean_ctor_set(v___x_1422_, 0, v___x_1428_);
v___x_1433_ = v___x_1422_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___f_1424_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v___f_1431_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v___f_1430_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v___f_1429_);
v___x_1433_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___f_1425_);
lean_ctor_set(v___x_1415_, 0, v___x_1433_);
v___x_1435_ = v___x_1415_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___f_1425_);
v___x_1435_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v_toApplicative_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1470_; 
v___x_1436_ = l_StateRefT_x27_instMonad___redArg(v___x_1435_);
v_toApplicative_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1436_, 1);
lean_dec(v_unused_1471_);
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1470_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_toApplicative_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1470_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_toFunctor_1441_; lean_object* v_toSeq_1442_; lean_object* v_toSeqLeft_1443_; lean_object* v_toSeqRight_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1468_; 
v_toFunctor_1441_ = lean_ctor_get(v_toApplicative_1437_, 0);
v_toSeq_1442_ = lean_ctor_get(v_toApplicative_1437_, 2);
v_toSeqLeft_1443_ = lean_ctor_get(v_toApplicative_1437_, 3);
v_toSeqRight_1444_ = lean_ctor_get(v_toApplicative_1437_, 4);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_toApplicative_1437_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_toApplicative_1437_, 1);
lean_dec(v_unused_1469_);
v___x_1446_ = v_toApplicative_1437_;
v_isShared_1447_ = v_isSharedCheck_1468_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_toSeqRight_1444_);
lean_inc(v_toSeqLeft_1443_);
lean_inc(v_toSeq_1442_);
lean_inc(v_toFunctor_1441_);
lean_dec(v_toApplicative_1437_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1468_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___x_1457_; 
v___f_1448_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__3));
v___f_1449_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___closed__4));
lean_inc_ref(v_toFunctor_1441_);
v___f_1450_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1450_, 0, v_toFunctor_1441_);
v___f_1451_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1451_, 0, v_toFunctor_1441_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___f_1450_);
lean_ctor_set(v___x_1452_, 1, v___f_1451_);
v___f_1453_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1453_, 0, v_toSeqRight_1444_);
v___f_1454_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1454_, 0, v_toSeqLeft_1443_);
v___f_1455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1455_, 0, v_toSeq_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 4, v___f_1453_);
lean_ctor_set(v___x_1446_, 3, v___f_1454_);
lean_ctor_set(v___x_1446_, 2, v___f_1455_);
lean_ctor_set(v___x_1446_, 1, v___f_1448_);
lean_ctor_set(v___x_1446_, 0, v___x_1452_);
v___x_1457_ = v___x_1446_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___f_1448_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v___f_1455_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___f_1454_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v___f_1453_);
v___x_1457_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___f_1449_);
lean_ctor_set(v___x_1439_, 0, v___x_1457_);
v___x_1459_ = v___x_1439_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___f_1449_);
v___x_1459_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_11777__overap_1464_; lean_object* v___x_1465_; 
v___x_1460_ = l_StateRefT_x27_instMonad___redArg(v___x_1459_);
v___x_1461_ = l_StateRefT_x27_instMonad___redArg(v___x_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = l_instInhabitedOfMonad___redArg(v___x_1461_, v___x_1462_);
v___x_11777__overap_1464_ = lean_panic_fn_borrowed(v___x_1463_, v_msg_1403_);
lean_dec(v___x_1463_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc(v___y_1404_);
v___x_1465_ = lean_apply_7(v___x_11777__overap_1464_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, lean_box(0));
return v___x_1465_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11___boxed(lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11(v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_a_1487_, lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1488_) == 0)
{
uint8_t v___x_1489_; 
v___x_1489_ = 0;
return v___x_1489_;
}
else
{
lean_object* v_key_1490_; lean_object* v_tail_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v_fst_1494_; lean_object* v_snd_1495_; uint8_t v___x_1496_; 
v_key_1490_ = lean_ctor_get(v_x_1488_, 0);
v_tail_1491_ = lean_ctor_get(v_x_1488_, 2);
v_fst_1492_ = lean_ctor_get(v_key_1490_, 0);
v_snd_1493_ = lean_ctor_get(v_key_1490_, 1);
v_fst_1494_ = lean_ctor_get(v_a_1487_, 0);
v_snd_1495_ = lean_ctor_get(v_a_1487_, 1);
v___x_1496_ = lean_expr_eqv(v_fst_1492_, v_fst_1494_);
if (v___x_1496_ == 0)
{
v_x_1488_ = v_tail_1491_;
goto _start;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_unbox(v_snd_1495_);
if (v___x_1498_ == 0)
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_unbox(v_snd_1493_);
if (v___x_1499_ == 0)
{
return v___x_1496_;
}
else
{
v_x_1488_ = v_tail_1491_;
goto _start;
}
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_unbox(v_snd_1493_);
if (v___x_1501_ == 0)
{
v_x_1488_ = v_tail_1491_;
goto _start;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_unbox(v_snd_1493_);
return v___x_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_a_1504_, lean_object* v_x_1505_){
_start:
{
uint8_t v_res_1506_; lean_object* v_r_1507_; 
v_res_1506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg(v_a_1504_, v_x_1505_);
lean_dec(v_x_1505_);
lean_dec_ref(v_a_1504_);
v_r_1507_ = lean_box(v_res_1506_);
return v_r_1507_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg(lean_object* v_m_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_buckets_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1513_; uint64_t v___x_1514_; uint64_t v___y_1516_; uint8_t v___x_1531_; 
v_buckets_1510_ = lean_ctor_get(v_m_1508_, 1);
v_fst_1511_ = lean_ctor_get(v_a_1509_, 0);
v_snd_1512_ = lean_ctor_get(v_a_1509_, 1);
v___x_1513_ = lean_array_get_size(v_buckets_1510_);
v___x_1514_ = l_Lean_Expr_hash(v_fst_1511_);
v___x_1531_ = lean_unbox(v_snd_1512_);
if (v___x_1531_ == 0)
{
uint64_t v___x_1532_; 
v___x_1532_ = 13ULL;
v___y_1516_ = v___x_1532_;
goto v___jp_1515_;
}
else
{
uint64_t v___x_1533_; 
v___x_1533_ = 11ULL;
v___y_1516_ = v___x_1533_;
goto v___jp_1515_;
}
v___jp_1515_:
{
uint64_t v___x_1517_; uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v_fold_1520_; uint64_t v___x_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1517_ = lean_uint64_mix_hash(v___x_1514_, v___y_1516_);
v___x_1518_ = 32ULL;
v___x_1519_ = lean_uint64_shift_right(v___x_1517_, v___x_1518_);
v_fold_1520_ = lean_uint64_xor(v___x_1517_, v___x_1519_);
v___x_1521_ = 16ULL;
v___x_1522_ = lean_uint64_shift_right(v_fold_1520_, v___x_1521_);
v___x_1523_ = lean_uint64_xor(v_fold_1520_, v___x_1522_);
v___x_1524_ = lean_uint64_to_usize(v___x_1523_);
v___x_1525_ = lean_usize_of_nat(v___x_1513_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_sub(v___x_1525_, v___x_1526_);
v___x_1528_ = lean_usize_land(v___x_1524_, v___x_1527_);
v___x_1529_ = lean_array_uget_borrowed(v_buckets_1510_, v___x_1528_);
v___x_1530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg(v_a_1509_, v___x_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg(v_m_1534_, v_a_1535_);
lean_dec_ref(v_a_1535_);
lean_dec_ref(v_m_1534_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10_spec__14___redArg(lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
return v_x_1538_;
}
else
{
lean_object* v_key_1540_; lean_object* v_value_1541_; lean_object* v_tail_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1573_; 
v_key_1540_ = lean_ctor_get(v_x_1539_, 0);
v_value_1541_ = lean_ctor_get(v_x_1539_, 1);
v_tail_1542_ = lean_ctor_get(v_x_1539_, 2);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1539_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1544_ = v_x_1539_;
v_isShared_1545_ = v_isSharedCheck_1573_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_tail_1542_);
lean_inc(v_value_1541_);
lean_inc(v_key_1540_);
lean_dec(v_x_1539_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1573_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_fst_1546_; lean_object* v_snd_1547_; lean_object* v___x_1548_; uint64_t v___x_1549_; uint64_t v___y_1551_; uint8_t v___x_1570_; 
v_fst_1546_ = lean_ctor_get(v_key_1540_, 0);
v_snd_1547_ = lean_ctor_get(v_key_1540_, 1);
v___x_1548_ = lean_array_get_size(v_x_1538_);
v___x_1549_ = l_Lean_Expr_hash(v_fst_1546_);
v___x_1570_ = lean_unbox(v_snd_1547_);
if (v___x_1570_ == 0)
{
uint64_t v___x_1571_; 
v___x_1571_ = 13ULL;
v___y_1551_ = v___x_1571_;
goto v___jp_1550_;
}
else
{
uint64_t v___x_1572_; 
v___x_1572_ = 11ULL;
v___y_1551_ = v___x_1572_;
goto v___jp_1550_;
}
v___jp_1550_:
{
uint64_t v___x_1552_; uint64_t v___x_1553_; uint64_t v___x_1554_; uint64_t v_fold_1555_; uint64_t v___x_1556_; uint64_t v___x_1557_; uint64_t v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; size_t v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1552_ = lean_uint64_mix_hash(v___x_1549_, v___y_1551_);
v___x_1553_ = 32ULL;
v___x_1554_ = lean_uint64_shift_right(v___x_1552_, v___x_1553_);
v_fold_1555_ = lean_uint64_xor(v___x_1552_, v___x_1554_);
v___x_1556_ = 16ULL;
v___x_1557_ = lean_uint64_shift_right(v_fold_1555_, v___x_1556_);
v___x_1558_ = lean_uint64_xor(v_fold_1555_, v___x_1557_);
v___x_1559_ = lean_uint64_to_usize(v___x_1558_);
v___x_1560_ = lean_usize_of_nat(v___x_1548_);
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_sub(v___x_1560_, v___x_1561_);
v___x_1563_ = lean_usize_land(v___x_1559_, v___x_1562_);
v___x_1564_ = lean_array_uget_borrowed(v_x_1538_, v___x_1563_);
lean_inc(v___x_1564_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 2, v___x_1564_);
v___x_1566_ = v___x_1544_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_key_1540_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_value_1541_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_array_uset(v_x_1538_, v___x_1563_, v___x_1566_);
v_x_1538_ = v___x_1567_;
v_x_1539_ = v_tail_1542_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_i_1574_, lean_object* v_source_1575_, lean_object* v_target_1576_){
_start:
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_array_get_size(v_source_1575_);
v___x_1578_ = lean_nat_dec_lt(v_i_1574_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v_source_1575_);
lean_dec(v_i_1574_);
return v_target_1576_;
}
else
{
lean_object* v_es_1579_; lean_object* v___x_1580_; lean_object* v_source_1581_; lean_object* v_target_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_es_1579_ = lean_array_fget(v_source_1575_, v_i_1574_);
v___x_1580_ = lean_box(0);
v_source_1581_ = lean_array_fset(v_source_1575_, v_i_1574_, v___x_1580_);
v_target_1582_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10_spec__14___redArg(v_target_1576_, v_es_1579_);
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = lean_nat_add(v_i_1574_, v___x_1583_);
lean_dec(v_i_1574_);
v_i_1574_ = v___x_1584_;
v_source_1575_ = v_source_1581_;
v_target_1576_ = v_target_1582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_data_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_nbuckets_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1587_ = lean_array_get_size(v_data_1586_);
v___x_1588_ = lean_unsigned_to_nat(2u);
v_nbuckets_1589_ = lean_nat_mul(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_mk_array(v_nbuckets_1589_, v___x_1591_);
v___x_1593_ = lean_array_propagate_mark(v_data_1586_, v___x_1592_);
v___x_1594_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10___redArg(v___x_1590_, v_data_1586_, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7___redArg(lean_object* v_m_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_){
_start:
{
lean_object* v_size_1598_; lean_object* v_buckets_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1602_; uint64_t v___x_1603_; uint64_t v___y_1605_; uint8_t v___x_1643_; 
v_size_1598_ = lean_ctor_get(v_m_1595_, 0);
v_buckets_1599_ = lean_ctor_get(v_m_1595_, 1);
v_fst_1600_ = lean_ctor_get(v_a_1596_, 0);
v_snd_1601_ = lean_ctor_get(v_a_1596_, 1);
v___x_1602_ = lean_array_get_size(v_buckets_1599_);
v___x_1603_ = l_Lean_Expr_hash(v_fst_1600_);
v___x_1643_ = lean_unbox(v_snd_1601_);
if (v___x_1643_ == 0)
{
uint64_t v___x_1644_; 
v___x_1644_ = 13ULL;
v___y_1605_ = v___x_1644_;
goto v___jp_1604_;
}
else
{
uint64_t v___x_1645_; 
v___x_1645_ = 11ULL;
v___y_1605_ = v___x_1645_;
goto v___jp_1604_;
}
v___jp_1604_:
{
uint64_t v___x_1606_; uint64_t v___x_1607_; uint64_t v___x_1608_; uint64_t v_fold_1609_; uint64_t v___x_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; size_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; size_t v___x_1617_; lean_object* v_bkt_1618_; uint8_t v___x_1619_; 
v___x_1606_ = lean_uint64_mix_hash(v___x_1603_, v___y_1605_);
v___x_1607_ = 32ULL;
v___x_1608_ = lean_uint64_shift_right(v___x_1606_, v___x_1607_);
v_fold_1609_ = lean_uint64_xor(v___x_1606_, v___x_1608_);
v___x_1610_ = 16ULL;
v___x_1611_ = lean_uint64_shift_right(v_fold_1609_, v___x_1610_);
v___x_1612_ = lean_uint64_xor(v_fold_1609_, v___x_1611_);
v___x_1613_ = lean_uint64_to_usize(v___x_1612_);
v___x_1614_ = lean_usize_of_nat(v___x_1602_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_sub(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_usize_land(v___x_1613_, v___x_1616_);
v_bkt_1618_ = lean_array_uget_borrowed(v_buckets_1599_, v___x_1617_);
v___x_1619_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg(v_a_1596_, v_bkt_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1640_; 
lean_inc_ref(v_buckets_1599_);
lean_inc(v_size_1598_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_m_1595_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1641_ = lean_ctor_get(v_m_1595_, 1);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_m_1595_, 0);
lean_dec(v_unused_1642_);
v___x_1621_ = v_m_1595_;
v_isShared_1622_ = v_isSharedCheck_1640_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v_m_1595_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1640_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v_size_x27_1624_; lean_object* v___x_1625_; lean_object* v_buckets_x27_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1623_ = lean_unsigned_to_nat(1u);
v_size_x27_1624_ = lean_nat_add(v_size_1598_, v___x_1623_);
lean_dec(v_size_1598_);
lean_inc(v_bkt_1618_);
v___x_1625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1625_, 0, v_a_1596_);
lean_ctor_set(v___x_1625_, 1, v_b_1597_);
lean_ctor_set(v___x_1625_, 2, v_bkt_1618_);
v_buckets_x27_1626_ = lean_array_uset(v_buckets_1599_, v___x_1617_, v___x_1625_);
v___x_1627_ = lean_unsigned_to_nat(4u);
v___x_1628_ = lean_nat_mul(v_size_x27_1624_, v___x_1627_);
v___x_1629_ = lean_unsigned_to_nat(3u);
v___x_1630_ = lean_nat_div(v___x_1628_, v___x_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_array_get_size(v_buckets_x27_1626_);
v___x_1632_ = lean_nat_dec_le(v___x_1630_, v___x_1631_);
lean_dec(v___x_1630_);
if (v___x_1632_ == 0)
{
lean_object* v_val_1633_; lean_object* v___x_1635_; 
v_val_1633_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9___redArg(v_buckets_x27_1626_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v_val_1633_);
lean_ctor_set(v___x_1621_, 0, v_size_x27_1624_);
v___x_1635_ = v___x_1621_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_size_x27_1624_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_val_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
lean_object* v___x_1638_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v_buckets_x27_1626_);
lean_ctor_set(v___x_1621_, 0, v_size_x27_1624_);
v___x_1638_ = v___x_1621_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_size_x27_1624_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_buckets_x27_1626_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_dec(v_b_1597_);
lean_dec_ref(v_a_1596_);
return v_m_1595_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__2));
v___x_1656_ = lean_unsigned_to_nat(6u);
v___x_1657_ = lean_unsigned_to_nat(114u);
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__1));
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__0));
v___x_1660_ = l_mkPanicMessageWithDecl(v___x_1659_, v___x_1658_, v___x_1657_, v___x_1656_, v___x_1655_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9(lean_object* v_problem_1714_, lean_object* v___x_1715_, lean_object* v_p_1716_, lean_object* v_q_1717_, uint8_t v_polarity_1718_, uint8_t v_flip_1719_, lean_object* v_a_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; uint8_t v___y_1734_; 
v___x_1730_ = l_Lean_Expr_cleanupAnnotations(v_p_1716_);
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2));
v___x_1732_ = l_Lean_Expr_isConstOf(v___x_1730_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4));
v___x_1738_ = l_Lean_Expr_isConstOf(v___x_1730_, v___x_1737_);
lean_dec_ref(v___x_1730_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; uint8_t v___x_1740_; uint8_t v___y_1742_; 
v___x_1739_ = l_Lean_Expr_cleanupAnnotations(v_q_1717_);
v___x_1740_ = l_Lean_Expr_isConstOf(v___x_1739_, v___x_1731_);
if (v___x_1740_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Lean_Expr_isConstOf(v___x_1739_, v___x_1737_);
lean_dec_ref(v___x_1739_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = 1;
lean_inc_ref(v_p_1716_);
v___x_1749_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1748_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v___x_1750_; 
lean_dec_ref_known(v___x_1749_, 1);
v___x_1750_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1747_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref_known(v___x_1750_, 1);
lean_inc_ref(v_q_1717_);
v___x_1751_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1748_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; 
lean_dec_ref_known(v___x_1751_, 1);
v___x_1752_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1747_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1752_;
}
else
{
lean_dec_ref(v_q_1717_);
return v___x_1751_;
}
}
else
{
lean_dec_ref(v_q_1717_);
return v___x_1750_;
}
}
else
{
lean_dec_ref(v_q_1717_);
lean_dec_ref(v_p_1716_);
return v___x_1749_;
}
}
else
{
lean_dec_ref(v_q_1717_);
if (v_flip_1719_ == 0)
{
if (v_polarity_1718_ == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1740_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1747_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1754_;
}
}
else
{
if (v_polarity_1718_ == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1747_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1740_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1756_;
}
}
}
}
else
{
lean_dec_ref(v___x_1739_);
lean_dec_ref(v_q_1717_);
if (v_polarity_1718_ == 0)
{
v___y_1742_ = v___x_1740_;
goto v___jp_1741_;
}
else
{
v___y_1742_ = v___x_1738_;
goto v___jp_1741_;
}
}
v___jp_1741_:
{
if (v_flip_1719_ == 0)
{
if (v___y_1742_ == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1738_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1740_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1744_;
}
}
else
{
if (v___y_1742_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1740_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_p_1716_, v___x_1738_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1746_;
}
}
}
}
else
{
lean_dec_ref(v_p_1716_);
if (v_flip_1719_ == 0)
{
if (v_polarity_1718_ == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1732_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1738_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1758_;
}
}
else
{
if (v_polarity_1718_ == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1738_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1732_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1760_;
}
}
}
}
else
{
lean_dec_ref(v___x_1730_);
lean_dec_ref(v_p_1716_);
if (v_polarity_1718_ == 0)
{
v___y_1734_ = v___x_1732_;
goto v___jp_1733_;
}
else
{
uint8_t v___x_1761_; 
v___x_1761_ = 0;
v___y_1734_ = v___x_1761_;
goto v___jp_1733_;
}
}
v___jp_1727_:
{
uint8_t v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = 0;
v___x_1729_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1728_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1729_;
}
v___jp_1733_:
{
if (v_flip_1719_ == 0)
{
if (v___y_1734_ == 0)
{
goto v___jp_1727_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1732_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1735_;
}
}
else
{
if (v___y_1734_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1714_, v___x_1715_, v_q_1717_, v___x_1732_, v_a_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1736_;
}
else
{
goto v___jp_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(lean_object* v_problem_1762_, lean_object* v___x_1763_, lean_object* v_e_1764_, uint8_t v_polarity_1765_, lean_object* v_a_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_p_1774_; lean_object* v_q_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1787_ = l_Lean_Expr_cleanupAnnotations(v_e_1764_);
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__2));
v___x_1789_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1788_);
v___x_1790_ = lean_st_ref_get(v_a_1766_);
v___x_1791_ = lean_box(v_polarity_1765_);
lean_inc_ref(v_e_1764_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_e_1764_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg(v___x_1790_, v___x_1792_);
lean_dec(v___x_1790_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_st_ref_take(v_a_1766_);
v___x_1795_ = lean_box(0);
v___x_1796_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7___redArg(v___x_1794_, v___x_1792_, v___x_1795_);
v___x_1797_ = lean_st_ref_put(v_a_1766_, v___x_1796_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___closed__4));
v___x_1799_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
v___x_1800_ = l_Lean_Expr_isApp(v___x_1787_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v___x_1787_);
v___x_1801_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1801_;
}
else
{
lean_object* v_arg_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_arg_1802_ = lean_ctor_get(v___x_1787_, 1);
lean_inc_ref(v_arg_1802_);
v___x_1803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1787_);
lean_dec_ref(v___x_1787_);
v___x_1804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__1));
v___x_1805_ = l_Lean_Expr_isConstOf(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Lean_Expr_isApp(v___x_1803_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_arg_1802_);
v___x_1807_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1807_;
}
else
{
lean_object* v_arg_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_arg_1808_ = lean_ctor_get(v___x_1803_, 1);
lean_inc_ref(v_arg_1808_);
v___x_1809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__4));
v___x_1811_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__6));
v___x_1813_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__8));
v___x_1815_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__10));
v___x_1817_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1816_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Lean_Expr_isApp(v___x_1809_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
v___x_1819_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1809_);
v___x_1821_ = l_Lean_Expr_isApp(v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1820_);
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
v___x_1822_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1820_);
v___x_1824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__12));
v___x_1825_ = l_Lean_Expr_isConstOf(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v_arg_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
lean_dec_ref(v___x_1809_);
v_arg_1826_ = lean_ctor_get(v___x_1820_, 1);
lean_inc_ref(v_arg_1826_);
lean_dec_ref(v___x_1820_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom___closed__2));
v___x_1828_ = l_Lean_Expr_isConstOf(v___x_1823_, v___x_1827_);
if (v___x_1828_ == 0)
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Lean_Expr_isApp(v___x_1823_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
lean_dec_ref(v_arg_1826_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
v___x_1830_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1823_);
lean_dec_ref(v___x_1823_);
v___x_1832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__14));
v___x_1833_ = l_Lean_Expr_isConstOf(v___x_1831_, v___x_1832_);
lean_dec_ref(v___x_1831_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref(v_arg_1826_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
v___x_1834_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; 
lean_dec_ref(v_e_1764_);
lean_inc_ref(v_arg_1826_);
v___x_1835_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1762_, v___x_1763_, v_arg_1826_, v___x_1833_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v___x_1836_; 
lean_dec_ref_known(v___x_1835_, 1);
v___x_1836_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1762_, v___x_1763_, v_arg_1826_, v___x_1828_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref_known(v___x_1836_, 1);
v___x_1837_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1762_, v___x_1763_, v_arg_1808_, v_polarity_1765_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_dec_ref_known(v___x_1837_, 1);
v_e_1764_ = v_arg_1802_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1802_);
return v___x_1837_;
}
}
else
{
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
return v___x_1836_;
}
}
else
{
lean_dec_ref(v_arg_1826_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
return v___x_1835_;
}
}
}
}
else
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
lean_dec_ref(v___x_1823_);
v___x_1839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__15));
v___x_1840_ = l_Lean_Expr_isConstOf(v_arg_1826_, v___x_1839_);
lean_dec_ref(v_arg_1826_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
v___x_1841_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1762_, v___x_1763_, v_e_1764_, v_polarity_1765_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; 
lean_dec_ref(v_e_1764_);
v___x_1842_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9(v_problem_1762_, v___x_1763_, v_arg_1808_, v_arg_1802_, v_polarity_1765_, v___x_1825_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1842_;
}
}
}
else
{
lean_object* v_arg_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1820_);
lean_dec_ref(v_e_1764_);
v_arg_1843_ = lean_ctor_get(v___x_1809_, 1);
lean_inc_ref_n(v_arg_1843_, 2);
lean_dec_ref(v___x_1809_);
v___x_1844_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1762_, v___x_1763_, v_arg_1843_, v___x_1825_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1844_, 1);
v___x_1845_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1762_, v___x_1763_, v_arg_1843_, v___x_1817_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1845_, 1);
v___x_1846_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1762_, v___x_1763_, v_arg_1808_, v_polarity_1765_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_dec_ref_known(v___x_1846_, 1);
v_e_1764_ = v_arg_1802_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1802_);
return v___x_1846_;
}
}
else
{
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
return v___x_1845_;
}
}
else
{
lean_dec_ref(v_arg_1843_);
lean_dec_ref(v_arg_1808_);
lean_dec_ref(v_arg_1802_);
return v___x_1844_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_e_1764_);
v_p_1774_ = v_arg_1808_;
v_q_1775_ = v_arg_1802_;
v___y_1776_ = v_a_1766_;
v___y_1777_ = v___y_1767_;
v___y_1778_ = v___y_1768_;
v___y_1779_ = v___y_1769_;
v___y_1780_ = v___y_1770_;
v___y_1781_ = v___y_1771_;
goto v___jp_1773_;
}
}
else
{
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_e_1764_);
v_p_1774_ = v_arg_1808_;
v_q_1775_ = v_arg_1802_;
v___y_1776_ = v_a_1766_;
v___y_1777_ = v___y_1767_;
v___y_1778_ = v___y_1768_;
v___y_1779_ = v___y_1769_;
v___y_1780_ = v___y_1770_;
v___y_1781_ = v___y_1771_;
goto v___jp_1773_;
}
}
else
{
lean_object* v___x_1848_; 
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_e_1764_);
v___x_1848_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9(v_problem_1762_, v___x_1763_, v_arg_1808_, v_arg_1802_, v_polarity_1765_, v___x_1813_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1848_;
}
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_arg_1802_);
lean_dec_ref(v_e_1764_);
v___x_1849_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1762_, v___x_1763_, v_arg_1808_, v_polarity_1765_, v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1849_;
}
}
}
else
{
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_e_1764_);
if (v_polarity_1765_ == 0)
{
v_e_1764_ = v_arg_1802_;
v_polarity_1765_ = v___x_1805_;
goto _start;
}
else
{
v_e_1764_ = v_arg_1802_;
v_polarity_1765_ = v___x_1799_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_e_1764_);
goto v___jp_1784_;
}
}
else
{
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_e_1764_);
goto v___jp_1784_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1792_, 2);
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_e_1764_);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
v___jp_1773_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1762_, v___x_1763_, v_p_1774_, v_polarity_1765_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_dec_ref_known(v___x_1782_, 1);
v_e_1764_ = v_q_1775_;
v_a_1766_ = v___y_1776_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1778_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1781_;
goto _start;
}
else
{
lean_dec_ref(v_q_1775_);
return v___x_1782_;
}
}
v___jp_1784_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(lean_object* v_problem_1854_, lean_object* v___x_1855_, lean_object* v_e_1856_, uint8_t v_polarity_1857_, lean_object* v_a_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1865_ = lean_st_ref_get(v_a_1858_);
v___x_1866_ = lean_box(v_polarity_1857_);
lean_inc_ref(v_e_1856_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_e_1856_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg(v___x_1865_, v___x_1867_);
lean_dec(v___x_1865_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v_p_1874_; lean_object* v_q_1875_; lean_object* v___y_1876_; 
v___x_1869_ = lean_st_ref_take(v_a_1858_);
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7___redArg(v___x_1869_, v___x_1867_, v___x_1870_);
v___x_1872_ = lean_st_ref_put(v_a_1858_, v___x_1871_);
if (lean_obj_tag(v_e_1856_) == 7)
{
lean_object* v_binderType_1879_; lean_object* v_body_1880_; uint8_t v___y_1882_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_binderType_1879_ = lean_ctor_get(v_e_1856_, 1);
lean_inc_ref(v_binderType_1879_);
v_body_1880_ = lean_ctor_get(v_e_1856_, 2);
lean_inc_ref(v_body_1880_);
lean_dec_ref_known(v_e_1856_, 3);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_expr_has_loose_bvar(v_body_1880_, v___x_1885_);
if (v___x_1886_ == 0)
{
if (v_polarity_1857_ == 0)
{
uint8_t v___x_1887_; 
v___x_1887_ = 1;
v___y_1882_ = v___x_1887_;
goto v___jp_1881_;
}
else
{
v___y_1882_ = v___x_1886_;
goto v___jp_1881_;
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
v___x_1888_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__3);
v___x_1889_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__11(v___x_1888_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1889_;
}
v___jp_1881_:
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1854_, v___x_1855_, v_binderType_1879_, v___y_1882_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_dec_ref_known(v___x_1883_, 1);
v_e_1856_ = v_body_1880_;
goto _start;
}
else
{
lean_dec_ref(v_body_1880_);
return v___x_1883_;
}
}
}
else
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = l_Lean_Expr_cleanupAnnotations(v_e_1856_);
v___x_1891_ = l_Lean_Expr_isApp(v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref(v___x_1890_);
v___x_1892_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1892_;
}
else
{
lean_object* v_arg_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_arg_1893_ = lean_ctor_get(v___x_1890_, 1);
lean_inc_ref(v_arg_1893_);
v___x_1894_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1890_);
lean_dec_ref(v___x_1890_);
v___x_1895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__5));
v___x_1896_ = l_Lean_Expr_isConstOf(v___x_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Lean_Expr_isApp(v___x_1894_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_arg_1893_);
v___x_1898_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1898_;
}
else
{
lean_object* v_arg_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_arg_1899_ = lean_ctor_get(v___x_1894_, 1);
lean_inc_ref(v_arg_1899_);
v___x_1900_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1894_);
lean_dec_ref(v___x_1894_);
v___x_1901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__7));
v___x_1902_ = l_Lean_Expr_isConstOf(v___x_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__9));
v___x_1904_ = l_Lean_Expr_isConstOf(v___x_1900_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__11));
v___x_1906_ = l_Lean_Expr_isConstOf(v___x_1900_, v___x_1905_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_isApp(v___x_1900_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
lean_dec_ref(v___x_1900_);
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
v___x_1908_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1908_;
}
else
{
lean_object* v_arg_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_arg_1909_ = lean_ctor_get(v___x_1900_, 1);
lean_inc_ref(v_arg_1909_);
v___x_1910_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1900_);
lean_dec_ref(v___x_1900_);
v___x_1911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__13));
v___x_1912_ = l_Lean_Expr_isConstOf(v___x_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Lean_Expr_isApp(v___x_1910_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_arg_1909_);
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
v___x_1914_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1910_);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__12));
v___x_1917_ = l_Lean_Expr_isConstOf(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
lean_dec_ref(v_arg_1909_);
v___x_1918_ = l_Lean_Expr_isApp(v___x_1915_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
lean_dec_ref(v___x_1915_);
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
v___x_1919_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1920_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1915_);
lean_dec_ref(v___x_1915_);
v___x_1921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__14));
v___x_1922_ = l_Lean_Expr_isConstOf(v___x_1920_, v___x_1921_);
lean_dec_ref(v___x_1920_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
v___x_1923_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1923_;
}
else
{
lean_object* v_arg_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v_e_1856_);
v_arg_1924_ = lean_ctor_get(v___x_1910_, 1);
lean_inc_ref_n(v_arg_1924_, 2);
lean_dec_ref(v___x_1910_);
v___x_1925_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1854_, v___x_1855_, v_arg_1924_, v___x_1922_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref_known(v___x_1925_, 1);
v___x_1926_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1854_, v___x_1855_, v_arg_1924_, v___x_1917_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref_known(v___x_1926_, 1);
v___x_1927_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1854_, v___x_1855_, v_arg_1899_, v_polarity_1857_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_dec_ref_known(v___x_1927_, 1);
v_e_1856_ = v_arg_1893_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1893_);
return v___x_1927_;
}
}
else
{
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
return v___x_1926_;
}
}
else
{
lean_dec_ref(v_arg_1924_);
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
return v___x_1925_;
}
}
}
}
else
{
lean_object* v___x_1929_; 
lean_dec_ref(v___x_1915_);
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_e_1856_);
lean_inc_ref(v_arg_1909_);
v___x_1929_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1854_, v___x_1855_, v_arg_1909_, v___x_1917_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref_known(v___x_1929_, 1);
v___x_1930_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_1854_, v___x_1855_, v_arg_1909_, v___x_1912_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref_known(v___x_1930_, 1);
v___x_1931_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1854_, v___x_1855_, v_arg_1899_, v_polarity_1857_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_dec_ref_known(v___x_1931_, 1);
v_e_1856_ = v_arg_1893_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1893_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
return v___x_1930_;
}
}
else
{
lean_dec_ref(v_arg_1909_);
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
return v___x_1929_;
}
}
}
}
else
{
uint8_t v___x_1933_; 
lean_dec_ref(v___x_1910_);
v___x_1933_ = l_Lean_Expr_isProp(v_arg_1909_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___closed__15));
v___x_1935_ = l_Lean_Expr_isConstOf(v_arg_1909_, v___x_1934_);
lean_dec_ref(v_arg_1909_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v_arg_1899_);
lean_dec_ref(v_arg_1893_);
v___x_1936_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeAtom(v_problem_1854_, v___x_1855_, v_e_1856_, v_polarity_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1936_;
}
else
{
lean_object* v___x_1937_; 
lean_dec_ref(v_e_1856_);
v___x_1937_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9(v_problem_1854_, v___x_1855_, v_arg_1899_, v_arg_1893_, v_polarity_1857_, v___x_1933_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1937_;
}
}
else
{
lean_object* v___x_1938_; 
lean_dec_ref(v_arg_1909_);
lean_dec_ref(v_e_1856_);
v___x_1938_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12(v_problem_1854_, v___x_1855_, v_arg_1899_, v_arg_1893_, v_polarity_1857_, v___x_1906_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1938_;
}
}
}
}
else
{
lean_dec_ref(v___x_1900_);
lean_dec_ref(v_e_1856_);
v_p_1874_ = v_arg_1899_;
v_q_1875_ = v_arg_1893_;
v___y_1876_ = v_a_1858_;
goto v___jp_1873_;
}
}
else
{
lean_dec_ref(v___x_1900_);
lean_dec_ref(v_e_1856_);
v_p_1874_ = v_arg_1899_;
v_q_1875_ = v_arg_1893_;
v___y_1876_ = v_a_1858_;
goto v___jp_1873_;
}
}
else
{
lean_object* v___x_1939_; 
lean_dec_ref(v___x_1900_);
lean_dec_ref(v_e_1856_);
v___x_1939_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12(v_problem_1854_, v___x_1855_, v_arg_1899_, v_arg_1893_, v_polarity_1857_, v___x_1896_, v_a_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1939_;
}
}
}
else
{
lean_dec_ref(v___x_1894_);
lean_dec_ref(v_e_1856_);
if (v_polarity_1857_ == 0)
{
v_e_1856_ = v_arg_1893_;
v_polarity_1857_ = v___x_1896_;
goto _start;
}
else
{
v_e_1856_ = v_arg_1893_;
v_polarity_1857_ = v___x_1868_;
goto _start;
}
}
}
}
v___jp_1873_:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1854_, v___x_1855_, v_p_1874_, v_polarity_1857_, v___y_1876_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_dec_ref_known(v___x_1877_, 1);
v_e_1856_ = v_q_1875_;
v_a_1858_ = v___y_1876_;
goto _start;
}
else
{
lean_dec_ref(v_q_1875_);
return v___x_1877_;
}
}
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec_ref_known(v___x_1867_, 2);
lean_dec_ref(v_e_1856_);
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12(lean_object* v_problem_1944_, lean_object* v___x_1945_, lean_object* v_p_1946_, lean_object* v_q_1947_, uint8_t v_polarity_1948_, uint8_t v_flip_1949_, lean_object* v_a_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; uint8_t v___y_1964_; 
v___x_1960_ = l_Lean_Expr_cleanupAnnotations(v_p_1946_);
v___x_1961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__1));
v___x_1962_ = l_Lean_Expr_isConstOf(v___x_1960_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___closed__3));
v___x_1968_ = l_Lean_Expr_isConstOf(v___x_1960_, v___x_1967_);
lean_dec_ref(v___x_1960_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; uint8_t v___x_1970_; uint8_t v___y_1972_; 
v___x_1969_ = l_Lean_Expr_cleanupAnnotations(v_q_1947_);
v___x_1970_ = l_Lean_Expr_isConstOf(v___x_1969_, v___x_1961_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1977_; 
v___x_1977_ = l_Lean_Expr_isConstOf(v___x_1969_, v___x_1967_);
lean_dec_ref(v___x_1969_);
if (v___x_1977_ == 0)
{
uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = 1;
lean_inc_ref(v_p_1946_);
v___x_1979_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1978_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1980_; 
lean_dec_ref_known(v___x_1979_, 1);
v___x_1980_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1977_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1981_; 
lean_dec_ref_known(v___x_1980_, 1);
lean_inc_ref(v_q_1947_);
v___x_1981_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1978_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1982_; 
lean_dec_ref_known(v___x_1981_, 1);
v___x_1982_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1977_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1982_;
}
else
{
lean_dec_ref(v_q_1947_);
return v___x_1981_;
}
}
else
{
lean_dec_ref(v_q_1947_);
return v___x_1980_;
}
}
else
{
lean_dec_ref(v_q_1947_);
lean_dec_ref(v_p_1946_);
return v___x_1979_;
}
}
else
{
lean_dec_ref(v_q_1947_);
if (v_flip_1949_ == 0)
{
if (v_polarity_1948_ == 0)
{
lean_object* v___x_1983_; 
v___x_1983_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1970_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1977_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1984_;
}
}
else
{
if (v_polarity_1948_ == 0)
{
lean_object* v___x_1985_; 
v___x_1985_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1977_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; 
v___x_1986_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1970_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1986_;
}
}
}
}
else
{
lean_dec_ref(v___x_1969_);
lean_dec_ref(v_q_1947_);
if (v_polarity_1948_ == 0)
{
v___y_1972_ = v___x_1970_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v___x_1968_;
goto v___jp_1971_;
}
}
v___jp_1971_:
{
if (v_flip_1949_ == 0)
{
if (v___y_1972_ == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1968_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1970_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1974_;
}
}
else
{
if (v___y_1972_ == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1970_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_p_1946_, v___x_1968_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1976_;
}
}
}
}
else
{
lean_dec_ref(v_p_1946_);
if (v_flip_1949_ == 0)
{
if (v_polarity_1948_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1962_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1968_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1988_;
}
}
else
{
if (v_polarity_1948_ == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1968_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1962_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1990_;
}
}
}
}
else
{
lean_dec_ref(v___x_1960_);
lean_dec_ref(v_p_1946_);
if (v_polarity_1948_ == 0)
{
v___y_1964_ = v___x_1962_;
goto v___jp_1963_;
}
else
{
uint8_t v___x_1991_; 
v___x_1991_ = 0;
v___y_1964_ = v___x_1991_;
goto v___jp_1963_;
}
}
v___jp_1957_:
{
uint8_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = 0;
v___x_1959_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1958_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1959_;
}
v___jp_1963_:
{
if (v_flip_1949_ == 0)
{
if (v___y_1964_ == 0)
{
goto v___jp_1957_;
}
else
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1962_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1965_;
}
}
else
{
if (v___y_1964_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_1944_, v___x_1945_, v_q_1947_, v___x_1962_, v_a_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1966_;
}
else
{
goto v___jp_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12___boxed(lean_object* v_problem_1992_, lean_object* v___x_1993_, lean_object* v_p_1994_, lean_object* v_q_1995_, lean_object* v_polarity_1996_, lean_object* v_flip_1997_, lean_object* v_a_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v_polarity_boxed_2005_; uint8_t v_flip_boxed_2006_; lean_object* v_res_2007_; 
v_polarity_boxed_2005_ = lean_unbox(v_polarity_1996_);
v_flip_boxed_2006_ = lean_unbox(v_flip_1997_);
v_res_2007_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8_spec__12(v_problem_1992_, v___x_1993_, v_p_1994_, v_q_1995_, v_polarity_boxed_2005_, v_flip_boxed_2006_, v_a_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v___x_1993_);
lean_dec_ref(v_problem_1992_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9___boxed(lean_object* v_problem_2008_, lean_object* v___x_2009_, lean_object* v_p_2010_, lean_object* v_q_2011_, lean_object* v_polarity_2012_, lean_object* v_flip_2013_, lean_object* v_a_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_polarity_boxed_2021_; uint8_t v_flip_boxed_2022_; lean_object* v_res_2023_; 
v_polarity_boxed_2021_ = lean_unbox(v_polarity_2012_);
v_flip_boxed_2022_ = lean_unbox(v_flip_2013_);
v_res_2023_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__9(v_problem_2008_, v___x_2009_, v_p_2010_, v_q_2011_, v_polarity_boxed_2021_, v_flip_boxed_2022_, v_a_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_problem_2008_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4___boxed(lean_object* v_problem_2024_, lean_object* v___x_2025_, lean_object* v_e_2026_, lean_object* v_polarity_2027_, lean_object* v_a_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_polarity_boxed_2035_; lean_object* v_res_2036_; 
v_polarity_boxed_2035_ = lean_unbox(v_polarity_2027_);
v_res_2036_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_2024_, v___x_2025_, v_e_2026_, v_polarity_boxed_2035_, v_a_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v___x_2025_);
lean_dec_ref(v_problem_2024_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___boxed(lean_object* v_problem_2037_, lean_object* v___x_2038_, lean_object* v_e_2039_, lean_object* v_polarity_2040_, lean_object* v_a_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_polarity_boxed_2048_; lean_object* v_res_2049_; 
v_polarity_boxed_2048_ = lean_unbox(v_polarity_2040_);
v_res_2049_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8(v_problem_2037_, v___x_2038_, v_e_2039_, v_polarity_boxed_2048_, v_a_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v___x_2038_);
lean_dec_ref(v_problem_2037_);
return v_res_2049_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_unsigned_to_nat(16u);
v___x_2052_ = lean_mk_array(v___x_2051_, v___x_2050_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__0);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___x_2053_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3(lean_object* v_problem_2056_, lean_object* v___x_2057_, lean_object* v_e_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = 1;
v___x_2066_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___closed__1);
v___x_2067_ = lean_st_mk_ref(v___x_2066_);
v___x_2068_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4(v_problem_2056_, v___x_2057_, v_e_2058_, v___x_2065_, v___x_2067_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2077_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_st_ref_get(v___x_2067_);
lean_dec(v___x_2067_);
lean_dec(v___x_2073_);
if (v_isShared_2072_ == 0)
{
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2069_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
else
{
lean_dec(v___x_2067_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3___boxed(lean_object* v_problem_2078_, lean_object* v___x_2079_, lean_object* v_e_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3(v_problem_2078_, v___x_2079_, v_e_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___x_2079_);
lean_dec_ref(v_problem_2078_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__0(lean_object* v_a_2088_, lean_object* v_xs_2089_, size_t v___x_2090_, lean_object* v_problem_2091_, lean_object* v___guards_2092_, lean_object* v_body_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_Expr_cleanupAnnotations(v_body_2093_);
v___x_2104_ = l_Lean_Expr_isApp(v___x_2103_);
if (v___x_2104_ == 0)
{
lean_dec_ref(v___x_2103_);
lean_dec_ref(v_a_2088_);
goto v___jp_2100_;
}
else
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2103_);
lean_dec_ref(v___x_2103_);
v___x_2106_ = l_Lean_Expr_isApp(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___x_2105_);
lean_dec_ref(v_a_2088_);
goto v___jp_2100_;
}
else
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2105_);
v___x_2108_ = l_Lean_Expr_isApp(v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v___x_2107_);
lean_dec_ref(v___x_2105_);
lean_dec_ref(v_a_2088_);
goto v___jp_2100_;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2107_);
lean_dec_ref(v___x_2107_);
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__8___closed__13));
v___x_2111_ = l_Lean_Expr_isConstOf(v___x_2109_, v___x_2110_);
lean_dec_ref(v___x_2109_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v___x_2105_);
lean_dec_ref(v_a_2088_);
goto v___jp_2100_;
}
else
{
lean_object* v_arg_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; size_t v_sz_2118_; lean_object* v___x_2119_; 
v_arg_2112_ = lean_ctor_get(v___x_2105_, 1);
lean_inc_ref(v_arg_2112_);
lean_dec_ref(v___x_2105_);
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1);
v___x_2115_ = lean_array_get_size(v_a_2088_);
v___x_2116_ = l_Array_toSubarray___redArg(v_a_2088_, v___x_2113_, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2114_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v_sz_2118_ = lean_array_size(v_xs_2089_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg(v_xs_2089_, v_sz_2118_, v___x_2090_, v___x_2117_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_fst_2121_; lean_object* v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v_fst_2121_ = lean_ctor_get(v_a_2120_, 0);
lean_inc(v_fst_2121_);
lean_dec(v_a_2120_);
v___x_2122_ = l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3(v_problem_2091_, v_fst_2121_, v_arg_2112_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v_fst_2121_);
return v___x_2122_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v_arg_2112_);
v_a_2123_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2119_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2119_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
}
v___jp_2100_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__0___boxed(lean_object* v_a_2131_, lean_object* v_xs_2132_, lean_object* v___x_2133_, lean_object* v_problem_2134_, lean_object* v___guards_2135_, lean_object* v_body_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
size_t v___x_14945__boxed_2143_; lean_object* v_res_2144_; 
v___x_14945__boxed_2143_ = lean_unbox_usize(v___x_2133_);
lean_dec(v___x_2133_);
v_res_2144_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__0(v_a_2131_, v_xs_2132_, v___x_14945__boxed_2143_, v_problem_2134_, v___guards_2135_, v_body_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v_body_2136_);
lean_dec_ref(v___guards_2135_);
lean_dec_ref(v_problem_2134_);
lean_dec_ref(v_xs_2132_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__1(lean_object* v_a_2145_, size_t v___x_2146_, lean_object* v_problem_2147_, lean_object* v___x_2148_, lean_object* v_xs_2149_, lean_object* v_body_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___f_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = lean_box_usize(v___x_2146_);
v___f_2158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__0___boxed), 12, 4);
lean_closure_set(v___f_2158_, 0, v_a_2145_);
lean_closure_set(v___f_2158_, 1, v_xs_2149_);
lean_closure_set(v___f_2158_, 2, v___x_2157_);
lean_closure_set(v___f_2158_, 3, v_problem_2147_);
v___x_2159_ = 0;
v___x_2160_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg(v_body_2150_, v___x_2148_, v___f_2158_, v___x_2159_, v___x_2159_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__1___boxed(lean_object* v_a_2161_, lean_object* v___x_2162_, lean_object* v_problem_2163_, lean_object* v___x_2164_, lean_object* v_xs_2165_, lean_object* v_body_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
size_t v___x_15032__boxed_2173_; lean_object* v_res_2174_; 
v___x_15032__boxed_2173_ = lean_unbox_usize(v___x_2162_);
lean_dec(v___x_2162_);
v_res_2174_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__1(v_a_2161_, v___x_15032__boxed_2173_, v_problem_2163_, v___x_2164_, v_xs_2165_, v_body_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg(size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_bs_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_bs_2177_);
return v___x_2181_;
}
else
{
lean_object* v_v_2182_; lean_object* v___x_2183_; lean_object* v_bs_x27_2184_; lean_object* v___x_2185_; 
v_v_2182_ = lean_array_uget(v_bs_2177_, v_i_2176_);
v___x_2183_ = lean_unsigned_to_nat(0u);
v_bs_x27_2184_ = lean_array_uset(v_bs_2177_, v_i_2176_, v___x_2183_);
v___x_2185_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freshClass___redArg(v_v_2182_, v___y_2178_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = ((size_t)1ULL);
v___x_2188_ = lean_usize_add(v_i_2176_, v___x_2187_);
v___x_2189_ = lean_array_uset(v_bs_x27_2184_, v_i_2176_, v_a_2186_);
v_i_2176_ = v___x_2188_;
v_bs_2177_ = v___x_2189_;
goto _start;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_bs_x27_2184_);
v_a_2191_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2185_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2185_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg___boxed(lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_bs_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg(v_sz_boxed_2204_, v_i_boxed_2205_, v_bs_2201_, v___y_2202_);
lean_dec(v___y_2202_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact(lean_object* v_problem_2209_, lean_object* v_fact_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_hyp_2217_; lean_object* v_boundSorts_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_hyp_2217_ = lean_ctor_get(v_fact_2210_, 0);
lean_inc_ref(v_hyp_2217_);
v_boundSorts_2218_ = lean_ctor_get(v_fact_2210_, 1);
lean_inc_ref_n(v_boundSorts_2218_, 2);
lean_dec_ref(v_fact_2210_);
v_sz_2219_ = lean_array_size(v_boundSorts_2218_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg(v_sz_2219_, v___x_2220_, v_boundSorts_2218_, v_a_2211_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2223_; lean_object* v_uf_2224_; lean_object* v_classSorts_2225_; lean_object* v_varClasses_2226_; lean_object* v_posClasses_2227_; lean_object* v_inserts_2228_; lean_object* v_exceptions_2229_; lean_object* v_avoids_2230_; lean_object* v_full_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2247_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = lean_st_ref_take(v_a_2211_);
v_uf_2224_ = lean_ctor_get(v___x_2223_, 0);
v_classSorts_2225_ = lean_ctor_get(v___x_2223_, 1);
v_varClasses_2226_ = lean_ctor_get(v___x_2223_, 2);
v_posClasses_2227_ = lean_ctor_get(v___x_2223_, 3);
v_inserts_2228_ = lean_ctor_get(v___x_2223_, 4);
v_exceptions_2229_ = lean_ctor_get(v___x_2223_, 5);
v_avoids_2230_ = lean_ctor_get(v___x_2223_, 6);
v_full_2231_ = lean_ctor_get(v___x_2223_, 7);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2233_ = v___x_2223_;
v_isShared_2234_ = v_isSharedCheck_2247_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_full_2231_);
lean_inc(v_avoids_2230_);
lean_inc(v_exceptions_2229_);
lean_inc(v_inserts_2228_);
lean_inc(v_posClasses_2227_);
lean_inc(v_varClasses_2226_);
lean_inc(v_classSorts_2225_);
lean_inc(v_uf_2224_);
lean_dec(v___x_2223_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2247_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_inc(v_a_2222_);
v___x_2235_ = lean_array_push(v_varClasses_2226_, v_a_2222_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 2, v___x_2235_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_uf_2224_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_classSorts_2225_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_posClasses_2227_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v_inserts_2228_);
lean_ctor_set(v_reuseFailAlloc_2246_, 5, v_exceptions_2229_);
lean_ctor_set(v_reuseFailAlloc_2246_, 6, v_avoids_2230_);
lean_ctor_set(v_reuseFailAlloc_2246_, 7, v_full_2231_);
v___x_2237_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; lean_object* v_type_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; 
v___x_2238_ = lean_st_ref_put(v_a_2211_, v___x_2237_);
v_type_2239_ = lean_ctor_get(v_hyp_2217_, 1);
lean_inc_ref(v_type_2239_);
lean_dec_ref(v_hyp_2217_);
v___x_2240_ = lean_array_get_size(v_boundSorts_2218_);
lean_dec_ref(v_boundSorts_2218_);
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
v___x_2242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___boxed__const__1));
lean_inc_ref(v___x_2241_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___lam__1___boxed), 12, 4);
lean_closure_set(v___f_2243_, 0, v_a_2222_);
lean_closure_set(v___f_2243_, 1, v___x_2242_);
lean_closure_set(v___f_2243_, 2, v_problem_2209_);
lean_closure_set(v___f_2243_, 3, v___x_2241_);
v___x_2244_ = 0;
v___x_2245_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__4___redArg(v_type_2239_, v___x_2241_, v___f_2243_, v___x_2244_, v___x_2244_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2245_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v_boundSorts_2218_);
lean_dec_ref(v_hyp_2217_);
lean_dec_ref(v_problem_2209_);
v_a_2248_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2221_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2221_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact___boxed(lean_object* v_problem_2256_, lean_object* v_fact_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact(v_problem_2256_, v_fact_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0(lean_object* v_00_u03b2_2265_, lean_object* v_m_2266_, lean_object* v_a_2267_, lean_object* v_b_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0___redArg(v_m_2266_, v_a_2267_, v_b_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1(size_t v_sz_2270_, size_t v_i_2271_, lean_object* v_bs_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___redArg(v_sz_2270_, v_i_2271_, v_bs_2272_, v___y_2273_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1___boxed(lean_object* v_sz_2280_, lean_object* v_i_2281_, lean_object* v_bs_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
size_t v_sz_boxed_2289_; size_t v_i_boxed_2290_; lean_object* v_res_2291_; 
v_sz_boxed_2289_ = lean_unbox_usize(v_sz_2280_);
lean_dec(v_sz_2280_);
v_i_boxed_2290_ = lean_unbox_usize(v_i_2281_);
lean_dec(v_i_2281_);
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__1(v_sz_boxed_2289_, v_i_boxed_2290_, v_bs_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2(lean_object* v_as_2292_, size_t v_sz_2293_, size_t v_i_2294_, lean_object* v_b_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___redArg(v_as_2292_, v_sz_2293_, v_i_2294_, v_b_2295_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2___boxed(lean_object* v_as_2303_, lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_b_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
size_t v_sz_boxed_2313_; size_t v_i_boxed_2314_; lean_object* v_res_2315_; 
v_sz_boxed_2313_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2314_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__2(v_as_2303_, v_sz_boxed_2313_, v_i_boxed_2314_, v_b_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v_as_2303_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0(lean_object* v_00_u03b2_2316_, lean_object* v_a_2317_, lean_object* v_b_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__0_spec__0___redArg(v_a_2317_, v_b_2318_, v_x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_2321_, lean_object* v_m_2322_, lean_object* v_a_2323_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___redArg(v_m_2322_, v_a_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2325_, lean_object* v_m_2326_, lean_object* v_a_2327_){
_start:
{
uint8_t v_res_2328_; lean_object* v_r_2329_; 
v_res_2328_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6(v_00_u03b2_2325_, v_m_2326_, v_a_2327_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_m_2326_);
v_r_2329_ = lean_box(v_res_2328_);
return v_r_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_2330_, lean_object* v_m_2331_, lean_object* v_a_2332_, lean_object* v_b_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7___redArg(v_m_2331_, v_a_2332_, v_b_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_2335_, lean_object* v_a_2336_, lean_object* v_x_2337_){
_start:
{
uint8_t v___x_2338_; 
v___x_2338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___redArg(v_a_2336_, v_x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2339_, lean_object* v_a_2340_, lean_object* v_x_2341_){
_start:
{
uint8_t v_res_2342_; lean_object* v_r_2343_; 
v_res_2342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__6_spec__7(v_00_u03b2_2339_, v_a_2340_, v_x_2341_);
lean_dec(v_x_2341_);
lean_dec_ref(v_a_2340_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2344_, lean_object* v_data_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9___redArg(v_data_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_2347_, lean_object* v_i_2348_, lean_object* v_source_2349_, lean_object* v_target_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10___redArg(v_i_2348_, v_source_2349_, v_target_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10_spec__14(lean_object* v_00_u03b2_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___at___00Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact_spec__3_spec__4_spec__7_spec__9_spec__10_spec__14___redArg(v_x_2353_, v_x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4_spec__19___redArg(lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 0)
{
return v_x_2356_;
}
else
{
lean_object* v_key_2358_; lean_object* v_value_2359_; lean_object* v_tail_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2383_; 
v_key_2358_ = lean_ctor_get(v_x_2357_, 0);
v_value_2359_ = lean_ctor_get(v_x_2357_, 1);
v_tail_2360_ = lean_ctor_get(v_x_2357_, 2);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_x_2357_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2362_ = v_x_2357_;
v_isShared_2363_ = v_isSharedCheck_2383_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_tail_2360_);
lean_inc(v_value_2359_);
lean_inc(v_key_2358_);
lean_dec(v_x_2357_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2383_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; uint64_t v___x_2365_; uint64_t v___x_2366_; uint64_t v___x_2367_; uint64_t v_fold_2368_; uint64_t v___x_2369_; uint64_t v___x_2370_; uint64_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2364_ = lean_array_get_size(v_x_2356_);
v___x_2365_ = lean_uint64_of_nat(v_key_2358_);
v___x_2366_ = 32ULL;
v___x_2367_ = lean_uint64_shift_right(v___x_2365_, v___x_2366_);
v_fold_2368_ = lean_uint64_xor(v___x_2365_, v___x_2367_);
v___x_2369_ = 16ULL;
v___x_2370_ = lean_uint64_shift_right(v_fold_2368_, v___x_2369_);
v___x_2371_ = lean_uint64_xor(v_fold_2368_, v___x_2370_);
v___x_2372_ = lean_uint64_to_usize(v___x_2371_);
v___x_2373_ = lean_usize_of_nat(v___x_2364_);
v___x_2374_ = ((size_t)1ULL);
v___x_2375_ = lean_usize_sub(v___x_2373_, v___x_2374_);
v___x_2376_ = lean_usize_land(v___x_2372_, v___x_2375_);
v___x_2377_ = lean_array_uget_borrowed(v_x_2356_, v___x_2376_);
lean_inc(v___x_2377_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 2, v___x_2377_);
v___x_2379_ = v___x_2362_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_key_2358_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_value_2359_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_array_uset(v_x_2356_, v___x_2376_, v___x_2379_);
v_x_2356_ = v___x_2380_;
v_x_2357_ = v_tail_2360_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4___redArg(lean_object* v_i_2384_, lean_object* v_source_2385_, lean_object* v_target_2386_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_array_get_size(v_source_2385_);
v___x_2388_ = lean_nat_dec_lt(v_i_2384_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_dec_ref(v_source_2385_);
lean_dec(v_i_2384_);
return v_target_2386_;
}
else
{
lean_object* v_es_2389_; lean_object* v___x_2390_; lean_object* v_source_2391_; lean_object* v_target_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_es_2389_ = lean_array_fget(v_source_2385_, v_i_2384_);
v___x_2390_ = lean_box(0);
v_source_2391_ = lean_array_fset(v_source_2385_, v_i_2384_, v___x_2390_);
v_target_2392_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4_spec__19___redArg(v_target_2386_, v_es_2389_);
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = lean_nat_add(v_i_2384_, v___x_2393_);
lean_dec(v_i_2384_);
v_i_2384_ = v___x_2394_;
v_source_2385_ = v_source_2391_;
v_target_2386_ = v_target_2392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3___redArg(lean_object* v_data_2396_){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_nbuckets_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2397_ = lean_array_get_size(v_data_2396_);
v___x_2398_ = lean_unsigned_to_nat(2u);
v_nbuckets_2399_ = lean_nat_mul(v___x_2397_, v___x_2398_);
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_box(0);
v___x_2402_ = lean_mk_array(v_nbuckets_2399_, v___x_2401_);
v___x_2403_ = lean_array_propagate_mark(v_data_2396_, v___x_2402_);
v___x_2404_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4___redArg(v___x_2400_, v_data_2396_, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(lean_object* v_a_2405_, lean_object* v_x_2406_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
uint8_t v___x_2407_; 
v___x_2407_ = 0;
return v___x_2407_;
}
else
{
lean_object* v_key_2408_; lean_object* v_tail_2409_; uint8_t v___x_2410_; 
v_key_2408_ = lean_ctor_get(v_x_2406_, 0);
v_tail_2409_ = lean_ctor_get(v_x_2406_, 2);
v___x_2410_ = lean_nat_dec_eq(v_key_2408_, v_a_2405_);
if (v___x_2410_ == 0)
{
v_x_2406_ = v_tail_2409_;
goto _start;
}
else
{
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg___boxed(lean_object* v_a_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2412_, v_x_2413_);
lean_dec(v_x_2413_);
lean_dec(v_a_2412_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__5___redArg(lean_object* v_m_2416_, lean_object* v_a_2417_, lean_object* v_b_2418_){
_start:
{
lean_object* v_size_2419_; lean_object* v_buckets_2420_; lean_object* v___x_2421_; uint64_t v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; uint64_t v_fold_2425_; uint64_t v___x_2426_; uint64_t v___x_2427_; uint64_t v___x_2428_; size_t v___x_2429_; size_t v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; lean_object* v_bkt_2434_; uint8_t v___x_2435_; 
v_size_2419_ = lean_ctor_get(v_m_2416_, 0);
v_buckets_2420_ = lean_ctor_get(v_m_2416_, 1);
v___x_2421_ = lean_array_get_size(v_buckets_2420_);
v___x_2422_ = lean_uint64_of_nat(v_a_2417_);
v___x_2423_ = 32ULL;
v___x_2424_ = lean_uint64_shift_right(v___x_2422_, v___x_2423_);
v_fold_2425_ = lean_uint64_xor(v___x_2422_, v___x_2424_);
v___x_2426_ = 16ULL;
v___x_2427_ = lean_uint64_shift_right(v_fold_2425_, v___x_2426_);
v___x_2428_ = lean_uint64_xor(v_fold_2425_, v___x_2427_);
v___x_2429_ = lean_uint64_to_usize(v___x_2428_);
v___x_2430_ = lean_usize_of_nat(v___x_2421_);
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_sub(v___x_2430_, v___x_2431_);
v___x_2433_ = lean_usize_land(v___x_2429_, v___x_2432_);
v_bkt_2434_ = lean_array_uget_borrowed(v_buckets_2420_, v___x_2433_);
v___x_2435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2417_, v_bkt_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2456_; 
lean_inc_ref(v_buckets_2420_);
lean_inc(v_size_2419_);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_m_2416_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; lean_object* v_unused_2458_; 
v_unused_2457_ = lean_ctor_get(v_m_2416_, 1);
lean_dec(v_unused_2457_);
v_unused_2458_ = lean_ctor_get(v_m_2416_, 0);
lean_dec(v_unused_2458_);
v___x_2437_ = v_m_2416_;
v_isShared_2438_ = v_isSharedCheck_2456_;
goto v_resetjp_2436_;
}
else
{
lean_dec(v_m_2416_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2456_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v_size_x27_2440_; lean_object* v___x_2441_; lean_object* v_buckets_x27_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2439_ = lean_unsigned_to_nat(1u);
v_size_x27_2440_ = lean_nat_add(v_size_2419_, v___x_2439_);
lean_dec(v_size_2419_);
lean_inc(v_bkt_2434_);
v___x_2441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2441_, 0, v_a_2417_);
lean_ctor_set(v___x_2441_, 1, v_b_2418_);
lean_ctor_set(v___x_2441_, 2, v_bkt_2434_);
v_buckets_x27_2442_ = lean_array_uset(v_buckets_2420_, v___x_2433_, v___x_2441_);
v___x_2443_ = lean_unsigned_to_nat(4u);
v___x_2444_ = lean_nat_mul(v_size_x27_2440_, v___x_2443_);
v___x_2445_ = lean_unsigned_to_nat(3u);
v___x_2446_ = lean_nat_div(v___x_2444_, v___x_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_array_get_size(v_buckets_x27_2442_);
v___x_2448_ = lean_nat_dec_le(v___x_2446_, v___x_2447_);
lean_dec(v___x_2446_);
if (v___x_2448_ == 0)
{
lean_object* v_val_2449_; lean_object* v___x_2451_; 
v_val_2449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3___redArg(v_buckets_x27_2442_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v_val_2449_);
lean_ctor_set(v___x_2437_, 0, v_size_x27_2440_);
v___x_2451_ = v___x_2437_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_size_x27_2440_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_val_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
else
{
lean_object* v___x_2454_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v_buckets_x27_2442_);
lean_ctor_set(v___x_2437_, 0, v_size_x27_2440_);
v___x_2454_ = v___x_2437_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_size_x27_2440_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_buckets_x27_2442_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_dec(v_b_2418_);
lean_dec(v_a_2417_);
return v_m_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6_spec__11(lean_object* v___x_2459_, lean_object* v_a_2460_, lean_object* v_x_2461_){
_start:
{
if (lean_obj_tag(v_x_2461_) == 0)
{
lean_dec(v_a_2460_);
lean_dec(v___x_2459_);
return v_x_2461_;
}
else
{
lean_object* v_key_2462_; lean_object* v_value_2463_; lean_object* v_tail_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2491_; 
v_key_2462_ = lean_ctor_get(v_x_2461_, 0);
v_value_2463_ = lean_ctor_get(v_x_2461_, 1);
v_tail_2464_ = lean_ctor_get(v_x_2461_, 2);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_x_2461_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2466_ = v_x_2461_;
v_isShared_2467_ = v_isSharedCheck_2491_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_tail_2464_);
lean_inc(v_value_2463_);
lean_inc(v_key_2462_);
lean_dec(v_x_2461_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2491_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_nat_dec_eq(v_key_2462_, v_a_2460_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6_spec__11(v___x_2459_, v_a_2460_, v_tail_2464_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 2, v___x_2469_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_key_2462_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_value_2463_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
else
{
lean_object* v_sort_2473_; uint8_t v_full_2474_; lean_object* v_terms_2475_; lean_object* v_termSet_2476_; lean_object* v_exceptions_2477_; lean_object* v_avoid_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_key_2462_);
v_sort_2473_ = lean_ctor_get(v_value_2463_, 0);
v_full_2474_ = lean_ctor_get_uint8(v_value_2463_, sizeof(void*)*5);
v_terms_2475_ = lean_ctor_get(v_value_2463_, 1);
v_termSet_2476_ = lean_ctor_get(v_value_2463_, 2);
v_exceptions_2477_ = lean_ctor_get(v_value_2463_, 3);
v_avoid_2478_ = lean_ctor_get(v_value_2463_, 4);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_value_2463_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2480_ = v_value_2463_;
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_avoid_2478_);
lean_inc(v_exceptions_2477_);
lean_inc(v_termSet_2476_);
lean_inc(v_terms_2475_);
lean_inc(v_sort_2473_);
lean_dec(v_value_2463_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2490_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2482_ = lean_box(0);
v___x_2483_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__5___redArg(v_avoid_2478_, v___x_2459_, v___x_2482_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 4, v___x_2483_);
v___x_2485_ = v___x_2480_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_sort_2473_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_terms_2475_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_termSet_2476_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_exceptions_2477_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v___x_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2489_, sizeof(void*)*5, v_full_2474_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2485_);
lean_ctor_set(v___x_2466_, 0, v_a_2460_);
v___x_2487_ = v___x_2466_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2460_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_tail_2464_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6(lean_object* v___x_2492_, lean_object* v_m_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_size_2495_; lean_object* v_buckets_2496_; lean_object* v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; uint64_t v_fold_2501_; uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; lean_object* v_bucket_2510_; uint8_t v___x_2511_; 
v_size_2495_ = lean_ctor_get(v_m_2493_, 0);
v_buckets_2496_ = lean_ctor_get(v_m_2493_, 1);
v___x_2497_ = lean_array_get_size(v_buckets_2496_);
v___x_2498_ = lean_uint64_of_nat(v_a_2494_);
v___x_2499_ = 32ULL;
v___x_2500_ = lean_uint64_shift_right(v___x_2498_, v___x_2499_);
v_fold_2501_ = lean_uint64_xor(v___x_2498_, v___x_2500_);
v___x_2502_ = 16ULL;
v___x_2503_ = lean_uint64_shift_right(v_fold_2501_, v___x_2502_);
v___x_2504_ = lean_uint64_xor(v_fold_2501_, v___x_2503_);
v___x_2505_ = lean_uint64_to_usize(v___x_2504_);
v___x_2506_ = lean_usize_of_nat(v___x_2497_);
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_sub(v___x_2506_, v___x_2507_);
v___x_2509_ = lean_usize_land(v___x_2505_, v___x_2508_);
v_bucket_2510_ = lean_array_uget_borrowed(v_buckets_2496_, v___x_2509_);
v___x_2511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2494_, v_bucket_2510_);
if (v___x_2511_ == 0)
{
lean_dec(v_a_2494_);
lean_dec(v___x_2492_);
return v_m_2493_;
}
else
{
lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2522_; 
lean_inc(v_bucket_2510_);
lean_inc_ref(v_buckets_2496_);
lean_inc(v_size_2495_);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_m_2493_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; lean_object* v_unused_2524_; 
v_unused_2523_ = lean_ctor_get(v_m_2493_, 1);
lean_dec(v_unused_2523_);
v_unused_2524_ = lean_ctor_get(v_m_2493_, 0);
lean_dec(v_unused_2524_);
v___x_2513_ = v_m_2493_;
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
else
{
lean_dec(v_m_2493_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v_buckets_2516_; lean_object* v_bucket_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2515_ = lean_box(0);
v_buckets_2516_ = lean_array_uset(v_buckets_2496_, v___x_2509_, v___x_2515_);
v_bucket_2517_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6_spec__11(v___x_2492_, v_a_2494_, v_bucket_2510_);
v___x_2518_ = lean_array_uset(v_buckets_2516_, v___x_2509_, v_bucket_2517_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2518_);
v___x_2520_ = v___x_2513_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_size_2495_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg(lean_object* v___x_2525_, lean_object* v_as_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_b_2529_){
_start:
{
lean_object* v_a_2532_; uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_b_2529_);
return v___x_2537_;
}
else
{
lean_object* v_a_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v_a_2538_ = lean_array_uget_borrowed(v_as_2526_, v_i_2528_);
v_fst_2539_ = lean_ctor_get(v_a_2538_, 0);
v_snd_2540_ = lean_ctor_get(v_a_2538_, 1);
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_array_get_borrowed(v___x_2541_, v___x_2525_, v_fst_2539_);
v___x_2543_ = lean_array_get_borrowed(v___x_2541_, v___x_2525_, v_snd_2540_);
v___x_2544_ = lean_nat_dec_eq(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
lean_inc(v___x_2542_);
lean_inc(v___x_2543_);
v___x_2545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__6(v___x_2543_, v_b_2529_, v___x_2542_);
v_a_2532_ = v___x_2545_;
goto v___jp_2531_;
}
else
{
v_a_2532_ = v_b_2529_;
goto v___jp_2531_;
}
}
v___jp_2531_:
{
size_t v___x_2533_; size_t v___x_2534_; 
v___x_2533_ = ((size_t)1ULL);
v___x_2534_ = lean_usize_add(v_i_2528_, v___x_2533_);
v_i_2528_ = v___x_2534_;
v_b_2529_ = v_a_2532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg___boxed(lean_object* v___x_2546_, lean_object* v_as_2547_, lean_object* v_sz_2548_, lean_object* v_i_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_){
_start:
{
size_t v_sz_boxed_2552_; size_t v_i_boxed_2553_; lean_object* v_res_2554_; 
v_sz_boxed_2552_ = lean_unbox_usize(v_sz_2548_);
lean_dec(v_sz_2548_);
v_i_boxed_2553_ = lean_unbox_usize(v_i_2549_);
lean_dec(v_i_2549_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg(v___x_2546_, v_as_2547_, v_sz_boxed_2552_, v_i_boxed_2553_, v_b_2550_);
lean_dec_ref(v_as_2547_);
lean_dec_ref(v___x_2546_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4___redArg(lean_object* v_a_2555_, lean_object* v_b_2556_, lean_object* v_x_2557_){
_start:
{
if (lean_obj_tag(v_x_2557_) == 0)
{
lean_dec(v_b_2556_);
lean_dec(v_a_2555_);
return v_x_2557_;
}
else
{
lean_object* v_key_2558_; lean_object* v_value_2559_; lean_object* v_tail_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2572_; 
v_key_2558_ = lean_ctor_get(v_x_2557_, 0);
v_value_2559_ = lean_ctor_get(v_x_2557_, 1);
v_tail_2560_ = lean_ctor_get(v_x_2557_, 2);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_x_2557_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2562_ = v_x_2557_;
v_isShared_2563_ = v_isSharedCheck_2572_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_tail_2560_);
lean_inc(v_value_2559_);
lean_inc(v_key_2558_);
lean_dec(v_x_2557_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2572_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_nat_dec_eq(v_key_2558_, v_a_2555_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4___redArg(v_a_2555_, v_b_2556_, v_tail_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 2, v___x_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_key_2558_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_value_2559_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
lean_object* v___x_2570_; 
lean_dec(v_value_2559_);
lean_dec(v_key_2558_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v_b_2556_);
lean_ctor_set(v___x_2562_, 0, v_a_2555_);
v___x_2570_ = v___x_2562_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2555_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_b_2556_);
lean_ctor_set(v_reuseFailAlloc_2571_, 2, v_tail_2560_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2___redArg(lean_object* v_m_2573_, lean_object* v_a_2574_, lean_object* v_b_2575_){
_start:
{
lean_object* v_size_2576_; lean_object* v_buckets_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2620_; 
v_size_2576_ = lean_ctor_get(v_m_2573_, 0);
v_buckets_2577_ = lean_ctor_get(v_m_2573_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_m_2573_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2579_ = v_m_2573_;
v_isShared_2580_ = v_isSharedCheck_2620_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_buckets_2577_);
lean_inc(v_size_2576_);
lean_dec(v_m_2573_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2620_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; uint64_t v___x_2582_; uint64_t v___x_2583_; uint64_t v___x_2584_; uint64_t v_fold_2585_; uint64_t v___x_2586_; uint64_t v___x_2587_; uint64_t v___x_2588_; size_t v___x_2589_; size_t v___x_2590_; size_t v___x_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v_bkt_2594_; uint8_t v___x_2595_; 
v___x_2581_ = lean_array_get_size(v_buckets_2577_);
v___x_2582_ = lean_uint64_of_nat(v_a_2574_);
v___x_2583_ = 32ULL;
v___x_2584_ = lean_uint64_shift_right(v___x_2582_, v___x_2583_);
v_fold_2585_ = lean_uint64_xor(v___x_2582_, v___x_2584_);
v___x_2586_ = 16ULL;
v___x_2587_ = lean_uint64_shift_right(v_fold_2585_, v___x_2586_);
v___x_2588_ = lean_uint64_xor(v_fold_2585_, v___x_2587_);
v___x_2589_ = lean_uint64_to_usize(v___x_2588_);
v___x_2590_ = lean_usize_of_nat(v___x_2581_);
v___x_2591_ = ((size_t)1ULL);
v___x_2592_ = lean_usize_sub(v___x_2590_, v___x_2591_);
v___x_2593_ = lean_usize_land(v___x_2589_, v___x_2592_);
v_bkt_2594_ = lean_array_uget_borrowed(v_buckets_2577_, v___x_2593_);
v___x_2595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2574_, v_bkt_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v_size_x27_2597_; lean_object* v___x_2598_; lean_object* v_buckets_x27_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
v_size_x27_2597_ = lean_nat_add(v_size_2576_, v___x_2596_);
lean_dec(v_size_2576_);
lean_inc(v_bkt_2594_);
v___x_2598_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2598_, 0, v_a_2574_);
lean_ctor_set(v___x_2598_, 1, v_b_2575_);
lean_ctor_set(v___x_2598_, 2, v_bkt_2594_);
v_buckets_x27_2599_ = lean_array_uset(v_buckets_2577_, v___x_2593_, v___x_2598_);
v___x_2600_ = lean_unsigned_to_nat(4u);
v___x_2601_ = lean_nat_mul(v_size_x27_2597_, v___x_2600_);
v___x_2602_ = lean_unsigned_to_nat(3u);
v___x_2603_ = lean_nat_div(v___x_2601_, v___x_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_array_get_size(v_buckets_x27_2599_);
v___x_2605_ = lean_nat_dec_le(v___x_2603_, v___x_2604_);
lean_dec(v___x_2603_);
if (v___x_2605_ == 0)
{
lean_object* v_val_2606_; lean_object* v___x_2608_; 
v_val_2606_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3___redArg(v_buckets_x27_2599_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 1, v_val_2606_);
lean_ctor_set(v___x_2579_, 0, v_size_x27_2597_);
v___x_2608_ = v___x_2579_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_size_x27_2597_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_val_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
else
{
lean_object* v___x_2611_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 1, v_buckets_x27_2599_);
lean_ctor_set(v___x_2579_, 0, v_size_x27_2597_);
v___x_2611_ = v___x_2579_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_size_x27_2597_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_buckets_x27_2599_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
else
{
lean_object* v___x_2613_; lean_object* v_buckets_x27_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_inc(v_bkt_2594_);
v___x_2613_ = lean_box(0);
v_buckets_x27_2614_ = lean_array_uset(v_buckets_2577_, v___x_2593_, v___x_2613_);
v___x_2615_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4___redArg(v_a_2574_, v_b_2575_, v_bkt_2594_);
v___x_2616_ = lean_array_uset(v_buckets_x27_2614_, v___x_2593_, v___x_2615_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 1, v___x_2616_);
v___x_2618_ = v___x_2579_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_size_2576_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg(lean_object* v_m_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_buckets_2623_; lean_object* v___x_2624_; uint64_t v___x_2625_; uint64_t v___x_2626_; uint64_t v___x_2627_; uint64_t v_fold_2628_; uint64_t v___x_2629_; uint64_t v___x_2630_; uint64_t v___x_2631_; size_t v___x_2632_; size_t v___x_2633_; size_t v___x_2634_; size_t v___x_2635_; size_t v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_buckets_2623_ = lean_ctor_get(v_m_2621_, 1);
v___x_2624_ = lean_array_get_size(v_buckets_2623_);
v___x_2625_ = lean_uint64_of_nat(v_a_2622_);
v___x_2626_ = 32ULL;
v___x_2627_ = lean_uint64_shift_right(v___x_2625_, v___x_2626_);
v_fold_2628_ = lean_uint64_xor(v___x_2625_, v___x_2627_);
v___x_2629_ = 16ULL;
v___x_2630_ = lean_uint64_shift_right(v_fold_2628_, v___x_2629_);
v___x_2631_ = lean_uint64_xor(v_fold_2628_, v___x_2630_);
v___x_2632_ = lean_uint64_to_usize(v___x_2631_);
v___x_2633_ = lean_usize_of_nat(v___x_2624_);
v___x_2634_ = ((size_t)1ULL);
v___x_2635_ = lean_usize_sub(v___x_2633_, v___x_2634_);
v___x_2636_ = lean_usize_land(v___x_2632_, v___x_2635_);
v___x_2637_ = lean_array_uget_borrowed(v_buckets_2623_, v___x_2636_);
v___x_2638_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2622_, v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg___boxed(lean_object* v_m_2639_, lean_object* v_a_2640_){
_start:
{
uint8_t v_res_2641_; lean_object* v_r_2642_; 
v_res_2641_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg(v_m_2639_, v_a_2640_);
lean_dec(v_a_2640_);
lean_dec_ref(v_m_2639_);
v_r_2642_ = lean_box(v_res_2641_);
return v_r_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg(lean_object* v_val_2643_, lean_object* v_as_2644_, size_t v_sz_2645_, size_t v_i_2646_, lean_object* v_b_2647_){
_start:
{
lean_object* v_a_2650_; uint8_t v___x_2654_; 
v___x_2654_ = lean_usize_dec_lt(v_i_2646_, v_sz_2645_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_b_2647_);
return v___x_2655_;
}
else
{
lean_object* v_a_2656_; uint8_t v___x_2657_; 
v_a_2656_ = lean_array_uget_borrowed(v_as_2644_, v_i_2646_);
v___x_2657_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg(v_b_2647_, v_a_2656_);
if (v___x_2657_ == 0)
{
lean_object* v_classSorts_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_classSorts_2658_ = lean_ctor_get(v_val_2643_, 1);
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_array_get_borrowed(v___x_2659_, v_classSorts_2658_, v_a_2656_);
v___x_2661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f___closed__1));
v___x_2662_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default___closed__1);
lean_inc(v___x_2660_);
v___x_2663_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2663_, 0, v___x_2660_);
lean_ctor_set(v___x_2663_, 1, v___x_2661_);
lean_ctor_set(v___x_2663_, 2, v___x_2662_);
lean_ctor_set(v___x_2663_, 3, v___x_2662_);
lean_ctor_set(v___x_2663_, 4, v___x_2662_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*5, v___x_2657_);
lean_inc(v_a_2656_);
v___x_2664_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2___redArg(v_b_2647_, v_a_2656_, v___x_2663_);
v_a_2650_ = v___x_2664_;
goto v___jp_2649_;
}
else
{
v_a_2650_ = v_b_2647_;
goto v___jp_2649_;
}
}
v___jp_2649_:
{
size_t v___x_2651_; size_t v___x_2652_; 
v___x_2651_ = ((size_t)1ULL);
v___x_2652_ = lean_usize_add(v_i_2646_, v___x_2651_);
v_i_2646_ = v___x_2652_;
v_b_2647_ = v_a_2650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg___boxed(lean_object* v_val_2665_, lean_object* v_as_2666_, lean_object* v_sz_2667_, lean_object* v_i_2668_, lean_object* v_b_2669_, lean_object* v___y_2670_){
_start:
{
size_t v_sz_boxed_2671_; size_t v_i_boxed_2672_; lean_object* v_res_2673_; 
v_sz_boxed_2671_ = lean_unbox_usize(v_sz_2667_);
lean_dec(v_sz_2667_);
v_i_boxed_2672_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg(v_val_2665_, v_as_2666_, v_sz_boxed_2671_, v_i_boxed_2672_, v_b_2669_);
lean_dec_ref(v_as_2666_);
lean_dec_ref(v_val_2665_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7_spec__13(lean_object* v_a_2674_, lean_object* v_x_2675_){
_start:
{
if (lean_obj_tag(v_x_2675_) == 0)
{
lean_dec(v_a_2674_);
return v_x_2675_;
}
else
{
lean_object* v_key_2676_; lean_object* v_value_2677_; lean_object* v_tail_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2702_; 
v_key_2676_ = lean_ctor_get(v_x_2675_, 0);
v_value_2677_ = lean_ctor_get(v_x_2675_, 1);
v_tail_2678_ = lean_ctor_get(v_x_2675_, 2);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_x_2675_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2680_ = v_x_2675_;
v_isShared_2681_ = v_isSharedCheck_2702_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_tail_2678_);
lean_inc(v_value_2677_);
lean_inc(v_key_2676_);
lean_dec(v_x_2675_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2702_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_nat_dec_eq(v_key_2676_, v_a_2674_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7_spec__13(v_a_2674_, v_tail_2678_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 2, v___x_2683_);
v___x_2685_ = v___x_2680_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_key_2676_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_value_2677_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
else
{
lean_object* v_sort_2687_; lean_object* v_terms_2688_; lean_object* v_termSet_2689_; lean_object* v_exceptions_2690_; lean_object* v_avoid_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_key_2676_);
v_sort_2687_ = lean_ctor_get(v_value_2677_, 0);
v_terms_2688_ = lean_ctor_get(v_value_2677_, 1);
v_termSet_2689_ = lean_ctor_get(v_value_2677_, 2);
v_exceptions_2690_ = lean_ctor_get(v_value_2677_, 3);
v_avoid_2691_ = lean_ctor_get(v_value_2677_, 4);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_value_2677_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2693_ = v_value_2677_;
v_isShared_2694_ = v_isSharedCheck_2701_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_avoid_2691_);
lean_inc(v_exceptions_2690_);
lean_inc(v_termSet_2689_);
lean_inc(v_terms_2688_);
lean_inc(v_sort_2687_);
lean_dec(v_value_2677_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2701_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_sort_2687_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_terms_2688_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_termSet_2689_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_exceptions_2690_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_avoid_2691_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
lean_ctor_set_uint8(v___x_2696_, sizeof(void*)*5, v___x_2682_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 1, v___x_2696_);
lean_ctor_set(v___x_2680_, 0, v_a_2674_);
v___x_2698_ = v___x_2680_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2674_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_tail_2678_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7(lean_object* v_m_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_size_2705_; lean_object* v_buckets_2706_; lean_object* v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; uint64_t v___x_2710_; uint64_t v_fold_2711_; uint64_t v___x_2712_; uint64_t v___x_2713_; uint64_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; lean_object* v_bucket_2720_; uint8_t v___x_2721_; 
v_size_2705_ = lean_ctor_get(v_m_2703_, 0);
v_buckets_2706_ = lean_ctor_get(v_m_2703_, 1);
v___x_2707_ = lean_array_get_size(v_buckets_2706_);
v___x_2708_ = lean_uint64_of_nat(v_a_2704_);
v___x_2709_ = 32ULL;
v___x_2710_ = lean_uint64_shift_right(v___x_2708_, v___x_2709_);
v_fold_2711_ = lean_uint64_xor(v___x_2708_, v___x_2710_);
v___x_2712_ = 16ULL;
v___x_2713_ = lean_uint64_shift_right(v_fold_2711_, v___x_2712_);
v___x_2714_ = lean_uint64_xor(v_fold_2711_, v___x_2713_);
v___x_2715_ = lean_uint64_to_usize(v___x_2714_);
v___x_2716_ = lean_usize_of_nat(v___x_2707_);
v___x_2717_ = ((size_t)1ULL);
v___x_2718_ = lean_usize_sub(v___x_2716_, v___x_2717_);
v___x_2719_ = lean_usize_land(v___x_2715_, v___x_2718_);
v_bucket_2720_ = lean_array_uget_borrowed(v_buckets_2706_, v___x_2719_);
v___x_2721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2704_, v_bucket_2720_);
if (v___x_2721_ == 0)
{
lean_dec(v_a_2704_);
return v_m_2703_;
}
else
{
lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2732_; 
lean_inc(v_bucket_2720_);
lean_inc_ref(v_buckets_2706_);
lean_inc(v_size_2705_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_m_2703_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; 
v_unused_2733_ = lean_ctor_get(v_m_2703_, 1);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_m_2703_, 0);
lean_dec(v_unused_2734_);
v___x_2723_ = v_m_2703_;
v_isShared_2724_ = v_isSharedCheck_2732_;
goto v_resetjp_2722_;
}
else
{
lean_dec(v_m_2703_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2732_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v_buckets_2726_; lean_object* v_bucket_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2725_ = lean_box(0);
v_buckets_2726_ = lean_array_uset(v_buckets_2706_, v___x_2719_, v___x_2725_);
v_bucket_2727_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7_spec__13(v_a_2704_, v_bucket_2720_);
v___x_2728_ = lean_array_uset(v_buckets_2726_, v___x_2719_, v_bucket_2727_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 1, v___x_2728_);
v___x_2730_ = v___x_2723_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_size_2705_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg(lean_object* v___x_2735_, lean_object* v_as_2736_, size_t v_sz_2737_, size_t v_i_2738_, lean_object* v_b_2739_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_lt(v_i_2738_, v_sz_2737_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_b_2739_);
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; lean_object* v_a_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; size_t v___x_2747_; size_t v___x_2748_; 
v___x_2743_ = lean_unsigned_to_nat(0u);
v_a_2744_ = lean_array_uget_borrowed(v_as_2736_, v_i_2738_);
v___x_2745_ = lean_array_get_borrowed(v___x_2743_, v___x_2735_, v_a_2744_);
lean_inc(v___x_2745_);
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__7(v_b_2739_, v___x_2745_);
v___x_2747_ = ((size_t)1ULL);
v___x_2748_ = lean_usize_add(v_i_2738_, v___x_2747_);
v_i_2738_ = v___x_2748_;
v_b_2739_ = v___x_2746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg___boxed(lean_object* v___x_2750_, lean_object* v_as_2751_, lean_object* v_sz_2752_, lean_object* v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_){
_start:
{
size_t v_sz_boxed_2756_; size_t v_i_boxed_2757_; lean_object* v_res_2758_; 
v_sz_boxed_2756_ = lean_unbox_usize(v_sz_2752_);
lean_dec(v_sz_2752_);
v_i_boxed_2757_ = lean_unbox_usize(v_i_2753_);
lean_dec(v_i_2753_);
v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg(v___x_2750_, v_as_2751_, v_sz_boxed_2756_, v_i_boxed_2757_, v_b_2754_);
lean_dec_ref(v_as_2751_);
lean_dec_ref(v___x_2750_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3_spec__6(lean_object* v_snd_2759_, lean_object* v_a_2760_, lean_object* v_x_2761_){
_start:
{
if (lean_obj_tag(v_x_2761_) == 0)
{
lean_dec(v_a_2760_);
lean_dec_ref(v_snd_2759_);
return v_x_2761_;
}
else
{
lean_object* v_key_2762_; lean_object* v_value_2763_; lean_object* v_tail_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2777_; 
v_key_2762_ = lean_ctor_get(v_x_2761_, 0);
v_value_2763_ = lean_ctor_get(v_x_2761_, 1);
v_tail_2764_ = lean_ctor_get(v_x_2761_, 2);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_x_2761_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2766_ = v_x_2761_;
v_isShared_2767_ = v_isSharedCheck_2777_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_tail_2764_);
lean_inc(v_value_2763_);
lean_inc(v_key_2762_);
lean_dec(v_x_2761_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2777_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint8_t v___x_2768_; 
v___x_2768_ = lean_nat_dec_eq(v_key_2762_, v_a_2760_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3_spec__6(v_snd_2759_, v_a_2760_, v_tail_2764_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 2, v___x_2769_);
v___x_2771_ = v___x_2766_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_key_2762_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_value_2763_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec(v_key_2762_);
v___x_2773_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm(v_value_2763_, v_snd_2759_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v___x_2773_);
lean_ctor_set(v___x_2766_, 0, v_a_2760_);
v___x_2775_ = v___x_2766_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2760_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_tail_2764_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3(lean_object* v_snd_2778_, lean_object* v_m_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_size_2781_; lean_object* v_buckets_2782_; lean_object* v___x_2783_; uint64_t v___x_2784_; uint64_t v___x_2785_; uint64_t v___x_2786_; uint64_t v_fold_2787_; uint64_t v___x_2788_; uint64_t v___x_2789_; uint64_t v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; lean_object* v_bucket_2796_; uint8_t v___x_2797_; 
v_size_2781_ = lean_ctor_get(v_m_2779_, 0);
v_buckets_2782_ = lean_ctor_get(v_m_2779_, 1);
v___x_2783_ = lean_array_get_size(v_buckets_2782_);
v___x_2784_ = lean_uint64_of_nat(v_a_2780_);
v___x_2785_ = 32ULL;
v___x_2786_ = lean_uint64_shift_right(v___x_2784_, v___x_2785_);
v_fold_2787_ = lean_uint64_xor(v___x_2784_, v___x_2786_);
v___x_2788_ = 16ULL;
v___x_2789_ = lean_uint64_shift_right(v_fold_2787_, v___x_2788_);
v___x_2790_ = lean_uint64_xor(v_fold_2787_, v___x_2789_);
v___x_2791_ = lean_uint64_to_usize(v___x_2790_);
v___x_2792_ = lean_usize_of_nat(v___x_2783_);
v___x_2793_ = ((size_t)1ULL);
v___x_2794_ = lean_usize_sub(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_usize_land(v___x_2791_, v___x_2794_);
v_bucket_2796_ = lean_array_uget_borrowed(v_buckets_2782_, v___x_2795_);
v___x_2797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2780_, v_bucket_2796_);
if (v___x_2797_ == 0)
{
lean_dec(v_a_2780_);
lean_dec_ref(v_snd_2778_);
return v_m_2779_;
}
else
{
lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2808_; 
lean_inc(v_bucket_2796_);
lean_inc_ref(v_buckets_2782_);
lean_inc(v_size_2781_);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_m_2779_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; lean_object* v_unused_2810_; 
v_unused_2809_ = lean_ctor_get(v_m_2779_, 1);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_m_2779_, 0);
lean_dec(v_unused_2810_);
v___x_2799_ = v_m_2779_;
v_isShared_2800_ = v_isSharedCheck_2808_;
goto v_resetjp_2798_;
}
else
{
lean_dec(v_m_2779_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2808_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v_buckets_2802_; lean_object* v_bucket_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2801_ = lean_box(0);
v_buckets_2802_ = lean_array_uset(v_buckets_2782_, v___x_2795_, v___x_2801_);
v_bucket_2803_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3_spec__6(v_snd_2778_, v_a_2780_, v_bucket_2796_);
v___x_2804_ = lean_array_uset(v_buckets_2802_, v___x_2795_, v_bucket_2803_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v___x_2804_);
v___x_2806_ = v___x_2799_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_size_2781_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg(lean_object* v___x_2811_, lean_object* v_as_2812_, size_t v_sz_2813_, size_t v_i_2814_, lean_object* v_b_2815_){
_start:
{
uint8_t v___x_2817_; 
v___x_2817_ = lean_usize_dec_lt(v_i_2814_, v_sz_2813_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_b_2815_);
return v___x_2818_;
}
else
{
lean_object* v_a_2819_; lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; 
v_a_2819_ = lean_array_uget_borrowed(v_as_2812_, v_i_2814_);
v_fst_2820_ = lean_ctor_get(v_a_2819_, 0);
v_snd_2821_ = lean_ctor_get(v_a_2819_, 1);
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = lean_array_get_borrowed(v___x_2822_, v___x_2811_, v_fst_2820_);
lean_inc(v___x_2823_);
lean_inc(v_snd_2821_);
v___x_2824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3(v_snd_2821_, v_b_2815_, v___x_2823_);
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = lean_usize_add(v_i_2814_, v___x_2825_);
v_i_2814_ = v___x_2826_;
v_b_2815_ = v___x_2824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg___boxed(lean_object* v___x_2828_, lean_object* v_as_2829_, lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg(v___x_2828_, v_as_2829_, v_sz_boxed_2834_, v_i_boxed_2835_, v_b_2832_);
lean_dec_ref(v_as_2829_);
lean_dec_ref(v___x_2828_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg(lean_object* v_upperBound_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_nat_dec_lt(v_a_2838_, v_upperBound_2837_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
lean_dec(v_a_2838_);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2839_);
return v___x_2842_;
}
else
{
lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___x_2845_; lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2858_; 
v_fst_2843_ = lean_ctor_get(v_b_2839_, 0);
lean_inc(v_fst_2843_);
v_snd_2844_ = lean_ctor_get(v_b_2839_, 1);
lean_inc(v_snd_2844_);
lean_dec_ref(v_b_2839_);
lean_inc(v_a_2838_);
v___x_2845_ = l_Lean_UnionFind_find_x21(v_fst_2843_, v_a_2838_);
v_fst_2846_ = lean_ctor_get(v___x_2845_, 0);
v_snd_2847_ = lean_ctor_get(v___x_2845_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2849_ = v___x_2845_;
v_isShared_2850_ = v_isSharedCheck_2858_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snd_2847_);
lean_inc(v_fst_2846_);
lean_dec(v___x_2845_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2858_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2851_ = lean_array_push(v_snd_2844_, v_snd_2847_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_fst_2846_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_add(v_a_2838_, v___x_2854_);
lean_dec(v_a_2838_);
v_a_2838_ = v___x_2855_;
v_b_2839_ = v___x_2853_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg___boxed(lean_object* v_upperBound_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg(v_upperBound_2859_, v_a_2860_, v_b_2861_);
lean_dec(v_upperBound_2859_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__14(lean_object* v___x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
return v_x_2865_;
}
else
{
lean_object* v_key_2867_; lean_object* v_value_2868_; lean_object* v_tail_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_key_2867_ = lean_ctor_get(v_x_2866_, 0);
lean_inc(v_key_2867_);
v_value_2868_ = lean_ctor_get(v_x_2866_, 1);
lean_inc(v_value_2868_);
v_tail_2869_ = lean_ctor_get(v_x_2866_, 2);
lean_inc(v_tail_2869_);
lean_dec_ref_known(v_x_2866_, 3);
v___x_2870_ = lean_unsigned_to_nat(0u);
v___x_2871_ = lean_array_get_borrowed(v___x_2870_, v___x_2864_, v_value_2868_);
lean_dec(v_value_2868_);
lean_inc(v___x_2871_);
v___x_2872_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__1___redArg(v_x_2865_, v_key_2867_, v___x_2871_);
v_x_2865_ = v___x_2872_;
v_x_2866_ = v_tail_2869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__14___boxed(lean_object* v___x_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__14(v___x_2874_, v_x_2875_, v_x_2876_);
lean_dec_ref(v___x_2874_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__15(lean_object* v___x_2878_, lean_object* v_as_2879_, size_t v_i_2880_, size_t v_stop_2881_, lean_object* v_b_2882_){
_start:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_usize_dec_eq(v_i_2880_, v_stop_2881_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; size_t v___x_2886_; size_t v___x_2887_; 
v___x_2884_ = lean_array_uget_borrowed(v_as_2879_, v_i_2880_);
lean_inc(v___x_2884_);
v___x_2885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__14(v___x_2878_, v_b_2882_, v___x_2884_);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2880_, v___x_2886_);
v_i_2880_ = v___x_2887_;
v_b_2882_ = v___x_2885_;
goto _start;
}
else
{
return v_b_2882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__15___boxed(lean_object* v___x_2889_, lean_object* v_as_2890_, lean_object* v_i_2891_, lean_object* v_stop_2892_, lean_object* v_b_2893_){
_start:
{
size_t v_i_boxed_2894_; size_t v_stop_boxed_2895_; lean_object* v_res_2896_; 
v_i_boxed_2894_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_stop_boxed_2895_ = lean_unbox_usize(v_stop_2892_);
lean_dec(v_stop_2892_);
v_res_2896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__15(v___x_2889_, v_as_2890_, v_i_boxed_2894_, v_stop_boxed_2895_, v_b_2893_);
lean_dec_ref(v_as_2890_);
lean_dec_ref(v___x_2889_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__0(lean_object* v___x_2897_, size_t v_sz_2898_, size_t v_i_2899_, lean_object* v_bs_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_lt(v_i_2899_, v_sz_2898_);
if (v___x_2901_ == 0)
{
return v_bs_2900_;
}
else
{
lean_object* v___x_2902_; lean_object* v_v_2903_; lean_object* v_bs_x27_2904_; lean_object* v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; lean_object* v___x_2908_; 
v___x_2902_ = lean_unsigned_to_nat(0u);
v_v_2903_ = lean_array_uget(v_bs_2900_, v_i_2899_);
v_bs_x27_2904_ = lean_array_uset(v_bs_2900_, v_i_2899_, v___x_2902_);
v___x_2905_ = lean_array_get_borrowed(v___x_2902_, v___x_2897_, v_v_2903_);
lean_dec(v_v_2903_);
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_add(v_i_2899_, v___x_2906_);
lean_inc(v___x_2905_);
v___x_2908_ = lean_array_uset(v_bs_x27_2904_, v_i_2899_, v___x_2905_);
v_i_2899_ = v___x_2907_;
v_bs_2900_ = v___x_2908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__0___boxed(lean_object* v___x_2910_, lean_object* v_sz_2911_, lean_object* v_i_2912_, lean_object* v_bs_2913_){
_start:
{
size_t v_sz_boxed_2914_; size_t v_i_boxed_2915_; lean_object* v_res_2916_; 
v_sz_boxed_2914_ = lean_unbox_usize(v_sz_2911_);
lean_dec(v_sz_2911_);
v_i_boxed_2915_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__0(v___x_2910_, v_sz_boxed_2914_, v_i_boxed_2915_, v_bs_2913_);
lean_dec_ref(v___x_2910_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__13(lean_object* v___x_2917_, size_t v_sz_2918_, size_t v_i_2919_, lean_object* v_bs_2920_){
_start:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_usize_dec_lt(v_i_2919_, v_sz_2918_);
if (v___x_2921_ == 0)
{
return v_bs_2920_;
}
else
{
lean_object* v_v_2922_; lean_object* v___x_2923_; lean_object* v_bs_x27_2924_; size_t v_sz_2925_; size_t v___x_2926_; lean_object* v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v_v_2922_ = lean_array_uget(v_bs_2920_, v_i_2919_);
v___x_2923_ = lean_unsigned_to_nat(0u);
v_bs_x27_2924_ = lean_array_uset(v_bs_2920_, v_i_2919_, v___x_2923_);
v_sz_2925_ = lean_array_size(v_v_2922_);
v___x_2926_ = ((size_t)0ULL);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__0(v___x_2917_, v_sz_2925_, v___x_2926_, v_v_2922_);
v___x_2928_ = ((size_t)1ULL);
v___x_2929_ = lean_usize_add(v_i_2919_, v___x_2928_);
v___x_2930_ = lean_array_uset(v_bs_x27_2924_, v_i_2919_, v___x_2927_);
v_i_2919_ = v___x_2929_;
v_bs_2920_ = v___x_2930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__13___boxed(lean_object* v___x_2932_, lean_object* v_sz_2933_, lean_object* v_i_2934_, lean_object* v_bs_2935_){
_start:
{
size_t v_sz_boxed_2936_; size_t v_i_boxed_2937_; lean_object* v_res_2938_; 
v_sz_boxed_2936_ = lean_unbox_usize(v_sz_2933_);
lean_dec(v_sz_2933_);
v_i_boxed_2937_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__13(v___x_2932_, v_sz_boxed_2936_, v_i_boxed_2937_, v_bs_2935_);
lean_dec_ref(v___x_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4_spec__8(lean_object* v_snd_2939_, lean_object* v_a_2940_, lean_object* v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
lean_dec(v_a_2940_);
lean_dec_ref(v_snd_2939_);
return v_x_2941_;
}
else
{
lean_object* v_key_2942_; lean_object* v_value_2943_; lean_object* v_tail_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2971_; 
v_key_2942_ = lean_ctor_get(v_x_2941_, 0);
v_value_2943_ = lean_ctor_get(v_x_2941_, 1);
v_tail_2944_ = lean_ctor_get(v_x_2941_, 2);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_x_2941_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2946_ = v_x_2941_;
v_isShared_2947_ = v_isSharedCheck_2971_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_tail_2944_);
lean_inc(v_value_2943_);
lean_inc(v_key_2942_);
lean_dec(v_x_2941_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2971_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_nat_dec_eq(v_key_2942_, v_a_2940_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4_spec__8(v_snd_2939_, v_a_2940_, v_tail_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 2, v___x_2949_);
v___x_2951_ = v___x_2946_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_key_2942_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_value_2943_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
else
{
lean_object* v_sort_2953_; uint8_t v_full_2954_; lean_object* v_terms_2955_; lean_object* v_termSet_2956_; lean_object* v_exceptions_2957_; lean_object* v_avoid_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_key_2942_);
v_sort_2953_ = lean_ctor_get(v_value_2943_, 0);
v_full_2954_ = lean_ctor_get_uint8(v_value_2943_, sizeof(void*)*5);
v_terms_2955_ = lean_ctor_get(v_value_2943_, 1);
v_termSet_2956_ = lean_ctor_get(v_value_2943_, 2);
v_exceptions_2957_ = lean_ctor_get(v_value_2943_, 3);
v_avoid_2958_ = lean_ctor_get(v_value_2943_, 4);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_value_2943_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2960_ = v_value_2943_;
v_isShared_2961_ = v_isSharedCheck_2970_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_avoid_2958_);
lean_inc(v_exceptions_2957_);
lean_inc(v_termSet_2956_);
lean_inc(v_terms_2955_);
lean_inc(v_sort_2953_);
lean_dec(v_value_2943_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2970_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2962_ = lean_box(0);
v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1___redArg(v_exceptions_2957_, v_snd_2939_, v___x_2962_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 3, v___x_2963_);
v___x_2965_ = v___x_2960_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_sort_2953_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_terms_2955_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_termSet_2956_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_avoid_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, sizeof(void*)*5, v_full_2954_);
v___x_2965_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2967_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v___x_2965_);
lean_ctor_set(v___x_2946_, 0, v_a_2940_);
v___x_2967_ = v___x_2946_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2940_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_tail_2944_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4(lean_object* v_snd_2972_, lean_object* v_m_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_size_2975_; lean_object* v_buckets_2976_; lean_object* v___x_2977_; uint64_t v___x_2978_; uint64_t v___x_2979_; uint64_t v___x_2980_; uint64_t v_fold_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; uint64_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; size_t v___x_2989_; lean_object* v_bucket_2990_; uint8_t v___x_2991_; 
v_size_2975_ = lean_ctor_get(v_m_2973_, 0);
v_buckets_2976_ = lean_ctor_get(v_m_2973_, 1);
v___x_2977_ = lean_array_get_size(v_buckets_2976_);
v___x_2978_ = lean_uint64_of_nat(v_a_2974_);
v___x_2979_ = 32ULL;
v___x_2980_ = lean_uint64_shift_right(v___x_2978_, v___x_2979_);
v_fold_2981_ = lean_uint64_xor(v___x_2978_, v___x_2980_);
v___x_2982_ = 16ULL;
v___x_2983_ = lean_uint64_shift_right(v_fold_2981_, v___x_2982_);
v___x_2984_ = lean_uint64_xor(v_fold_2981_, v___x_2983_);
v___x_2985_ = lean_uint64_to_usize(v___x_2984_);
v___x_2986_ = lean_usize_of_nat(v___x_2977_);
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = lean_usize_sub(v___x_2986_, v___x_2987_);
v___x_2989_ = lean_usize_land(v___x_2985_, v___x_2988_);
v_bucket_2990_ = lean_array_uget_borrowed(v_buckets_2976_, v___x_2989_);
v___x_2991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_2974_, v_bucket_2990_);
if (v___x_2991_ == 0)
{
lean_dec(v_a_2974_);
lean_dec_ref(v_snd_2972_);
return v_m_2973_;
}
else
{
lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3002_; 
lean_inc(v_bucket_2990_);
lean_inc_ref(v_buckets_2976_);
lean_inc(v_size_2975_);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_m_2973_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; lean_object* v_unused_3004_; 
v_unused_3003_ = lean_ctor_get(v_m_2973_, 1);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_m_2973_, 0);
lean_dec(v_unused_3004_);
v___x_2993_ = v_m_2973_;
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
else
{
lean_dec(v_m_2973_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v_buckets_2996_; lean_object* v_bucket_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2995_ = lean_box(0);
v_buckets_2996_ = lean_array_uset(v_buckets_2976_, v___x_2989_, v___x_2995_);
v_bucket_2997_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4_spec__8(v_snd_2972_, v_a_2974_, v_bucket_2990_);
v___x_2998_ = lean_array_uset(v_buckets_2996_, v___x_2989_, v_bucket_2997_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v___x_2998_);
v___x_3000_ = v___x_2993_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_size_2975_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg(lean_object* v___x_3005_, lean_object* v_as_3006_, size_t v_sz_3007_, size_t v_i_3008_, lean_object* v_b_3009_){
_start:
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_usize_dec_lt(v_i_3008_, v_sz_3007_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_b_3009_);
return v___x_3012_;
}
else
{
lean_object* v_a_3013_; lean_object* v_fst_3014_; lean_object* v_snd_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; size_t v___x_3019_; size_t v___x_3020_; 
v_a_3013_ = lean_array_uget_borrowed(v_as_3006_, v_i_3008_);
v_fst_3014_ = lean_ctor_get(v_a_3013_, 0);
v_snd_3015_ = lean_ctor_get(v_a_3013_, 1);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_borrowed(v___x_3016_, v___x_3005_, v_fst_3014_);
lean_inc(v___x_3017_);
lean_inc(v_snd_3015_);
v___x_3018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__4(v_snd_3015_, v_b_3009_, v___x_3017_);
v___x_3019_ = ((size_t)1ULL);
v___x_3020_ = lean_usize_add(v_i_3008_, v___x_3019_);
v_i_3008_ = v___x_3020_;
v_b_3009_ = v___x_3018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg___boxed(lean_object* v___x_3022_, lean_object* v_as_3023_, lean_object* v_sz_3024_, lean_object* v_i_3025_, lean_object* v_b_3026_, lean_object* v___y_3027_){
_start:
{
size_t v_sz_boxed_3028_; size_t v_i_boxed_3029_; lean_object* v_res_3030_; 
v_sz_boxed_3028_ = lean_unbox_usize(v_sz_3024_);
lean_dec(v_sz_3024_);
v_i_boxed_3029_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg(v___x_3022_, v_as_3023_, v_sz_boxed_3028_, v_i_boxed_3029_, v_b_3026_);
lean_dec_ref(v_as_3023_);
lean_dec_ref(v___x_3022_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze(lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3037_; lean_object* v_uf_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3037_ = lean_st_ref_get(v_a_3031_);
v_uf_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc_ref(v_uf_3038_);
lean_dec(v___x_3037_);
v___x_3039_ = lean_array_get_size(v_uf_3038_);
v___x_3040_ = lean_mk_empty_array_with_capacity(v___x_3039_);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_uf_3038_);
lean_ctor_set(v___x_3042_, 1, v___x_3040_);
v___x_3043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg(v___x_3039_, v___x_3041_, v___x_3042_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_snd_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; size_t v_sz_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v_snd_3045_ = lean_ctor_get(v_a_3044_, 1);
lean_inc(v_snd_3045_);
lean_dec(v_a_3044_);
v___x_3046_ = lean_st_ref_get(v_a_3031_);
v___x_3047_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default___closed__1);
v_sz_3048_ = lean_array_size(v_snd_3045_);
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg(v___x_3046_, v_snd_3045_, v_sz_3048_, v___x_3049_, v___x_3047_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v_varClasses_3052_; lean_object* v_posClasses_3053_; lean_object* v_inserts_3054_; lean_object* v_exceptions_3055_; lean_object* v_avoids_3056_; lean_object* v_full_3057_; size_t v_sz_3058_; lean_object* v___x_3059_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v_varClasses_3052_ = lean_ctor_get(v___x_3046_, 2);
lean_inc_ref(v_varClasses_3052_);
v_posClasses_3053_ = lean_ctor_get(v___x_3046_, 3);
lean_inc_ref(v_posClasses_3053_);
v_inserts_3054_ = lean_ctor_get(v___x_3046_, 4);
lean_inc_ref(v_inserts_3054_);
v_exceptions_3055_ = lean_ctor_get(v___x_3046_, 5);
lean_inc_ref(v_exceptions_3055_);
v_avoids_3056_ = lean_ctor_get(v___x_3046_, 6);
lean_inc_ref(v_avoids_3056_);
v_full_3057_ = lean_ctor_get(v___x_3046_, 7);
lean_inc_ref(v_full_3057_);
lean_dec(v___x_3046_);
v_sz_3058_ = lean_array_size(v_inserts_3054_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg(v_snd_3045_, v_inserts_3054_, v_sz_3058_, v___x_3049_, v_a_3051_);
lean_dec_ref(v_inserts_3054_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; size_t v_sz_3061_; lean_object* v___x_3062_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v_sz_3061_ = lean_array_size(v_exceptions_3055_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg(v_snd_3045_, v_exceptions_3055_, v_sz_3061_, v___x_3049_, v_a_3060_);
lean_dec_ref(v_exceptions_3055_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; size_t v_sz_3064_; lean_object* v___x_3065_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v_sz_3064_ = lean_array_size(v_avoids_3056_);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg(v_snd_3045_, v_avoids_3056_, v_sz_3064_, v___x_3049_, v_a_3063_);
lean_dec_ref(v_avoids_3056_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; size_t v_sz_3067_; lean_object* v___x_3068_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v_sz_3067_ = lean_array_size(v_full_3057_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg(v_snd_3045_, v_full_3057_, v_sz_3067_, v___x_3049_, v_a_3066_);
lean_dec_ref(v_full_3057_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3086_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3086_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3086_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_buckets_3073_; size_t v_sz_3074_; lean_object* v___x_3075_; lean_object* v___y_3077_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_buckets_3073_ = lean_ctor_get(v_posClasses_3053_, 1);
lean_inc_ref(v_buckets_3073_);
lean_dec_ref(v_posClasses_3053_);
v_sz_3074_ = lean_array_size(v_varClasses_3052_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__13(v_snd_3045_, v_sz_3074_, v___x_3049_, v_varClasses_3052_);
v___x_3082_ = lean_array_get_size(v_buckets_3073_);
v___x_3083_ = lean_nat_dec_lt(v___x_3041_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_dec_ref(v_buckets_3073_);
lean_dec(v_snd_3045_);
v___y_3077_ = v___x_3047_;
goto v___jp_3076_;
}
else
{
size_t v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_usize_of_nat(v___x_3082_);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__15(v_snd_3045_, v_buckets_3073_, v___x_3049_, v___x_3084_, v___x_3047_);
lean_dec_ref(v_buckets_3073_);
lean_dec(v_snd_3045_);
v___y_3077_ = v___x_3085_;
goto v___jp_3076_;
}
v___jp_3076_:
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3078_, 0, v_a_3069_);
lean_ctor_set(v___x_3078_, 1, v___x_3075_);
lean_ctor_set(v___x_3078_, 2, v___y_3077_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3078_);
v___x_3080_ = v___x_3071_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v_posClasses_3053_);
lean_dec_ref(v_varClasses_3052_);
lean_dec(v_snd_3045_);
v_a_3087_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3068_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3068_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v_full_3057_);
lean_dec_ref(v_posClasses_3053_);
lean_dec_ref(v_varClasses_3052_);
lean_dec(v_snd_3045_);
v_a_3095_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3065_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3065_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v_full_3057_);
lean_dec_ref(v_avoids_3056_);
lean_dec_ref(v_posClasses_3053_);
lean_dec_ref(v_varClasses_3052_);
lean_dec(v_snd_3045_);
v_a_3103_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3062_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3062_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v_full_3057_);
lean_dec_ref(v_avoids_3056_);
lean_dec_ref(v_exceptions_3055_);
lean_dec_ref(v_posClasses_3053_);
lean_dec_ref(v_varClasses_3052_);
lean_dec(v_snd_3045_);
v_a_3111_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3059_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3059_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v___x_3046_);
lean_dec(v_snd_3045_);
v_a_3119_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3050_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3050_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
v_a_3127_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3043_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3043_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze___boxed(lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze(v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
return v_res_3141_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1(lean_object* v_00_u03b2_3142_, lean_object* v_m_3143_, lean_object* v_a_3144_){
_start:
{
uint8_t v___x_3145_; 
v___x_3145_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___redArg(v_m_3143_, v_a_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1___boxed(lean_object* v_00_u03b2_3146_, lean_object* v_m_3147_, lean_object* v_a_3148_){
_start:
{
uint8_t v_res_3149_; lean_object* v_r_3150_; 
v_res_3149_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1(v_00_u03b2_3146_, v_m_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_m_3147_);
v_r_3150_ = lean_box(v_res_3149_);
return v_r_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2(lean_object* v_00_u03b2_3151_, lean_object* v_m_3152_, lean_object* v_a_3153_, lean_object* v_b_3154_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2___redArg(v_m_3152_, v_a_3153_, v_b_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__5(lean_object* v_00_u03b2_3156_, lean_object* v_m_3157_, lean_object* v_a_3158_, lean_object* v_b_3159_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__5___redArg(v_m_3157_, v_a_3158_, v_b_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8(lean_object* v_val_3161_, lean_object* v_as_3162_, size_t v_sz_3163_, size_t v_i_3164_, lean_object* v_b_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___redArg(v_val_3161_, v_as_3162_, v_sz_3163_, v_i_3164_, v_b_3165_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8___boxed(lean_object* v_val_3173_, lean_object* v_as_3174_, lean_object* v_sz_3175_, lean_object* v_i_3176_, lean_object* v_b_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
size_t v_sz_boxed_3184_; size_t v_i_boxed_3185_; lean_object* v_res_3186_; 
v_sz_boxed_3184_ = lean_unbox_usize(v_sz_3175_);
lean_dec(v_sz_3175_);
v_i_boxed_3185_ = lean_unbox_usize(v_i_3176_);
lean_dec(v_i_3176_);
v_res_3186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__8(v_val_3173_, v_as_3174_, v_sz_boxed_3184_, v_i_boxed_3185_, v_b_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v_as_3174_);
lean_dec_ref(v_val_3173_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9(lean_object* v___x_3187_, lean_object* v_as_3188_, size_t v_sz_3189_, size_t v_i_3190_, lean_object* v_b_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___redArg(v___x_3187_, v_as_3188_, v_sz_3189_, v_i_3190_, v_b_3191_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9___boxed(lean_object* v___x_3199_, lean_object* v_as_3200_, lean_object* v_sz_3201_, lean_object* v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
size_t v_sz_boxed_3210_; size_t v_i_boxed_3211_; lean_object* v_res_3212_; 
v_sz_boxed_3210_ = lean_unbox_usize(v_sz_3201_);
lean_dec(v_sz_3201_);
v_i_boxed_3211_ = lean_unbox_usize(v_i_3202_);
lean_dec(v_i_3202_);
v_res_3212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__9(v___x_3199_, v_as_3200_, v_sz_boxed_3210_, v_i_boxed_3211_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v_as_3200_);
lean_dec_ref(v___x_3199_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10(lean_object* v___x_3213_, lean_object* v_as_3214_, size_t v_sz_3215_, size_t v_i_3216_, lean_object* v_b_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___redArg(v___x_3213_, v_as_3214_, v_sz_3215_, v_i_3216_, v_b_3217_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10___boxed(lean_object* v___x_3225_, lean_object* v_as_3226_, lean_object* v_sz_3227_, lean_object* v_i_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
size_t v_sz_boxed_3236_; size_t v_i_boxed_3237_; lean_object* v_res_3238_; 
v_sz_boxed_3236_ = lean_unbox_usize(v_sz_3227_);
lean_dec(v_sz_3227_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3228_);
lean_dec(v_i_3228_);
v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__10(v___x_3225_, v_as_3226_, v_sz_boxed_3236_, v_i_boxed_3237_, v_b_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v_as_3226_);
lean_dec_ref(v___x_3225_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11(lean_object* v___x_3239_, lean_object* v_as_3240_, size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___redArg(v___x_3239_, v_as_3240_, v_sz_3241_, v_i_3242_, v_b_3243_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11___boxed(lean_object* v___x_3251_, lean_object* v_as_3252_, lean_object* v_sz_3253_, lean_object* v_i_3254_, lean_object* v_b_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
size_t v_sz_boxed_3262_; size_t v_i_boxed_3263_; lean_object* v_res_3264_; 
v_sz_boxed_3262_ = lean_unbox_usize(v_sz_3253_);
lean_dec(v_sz_3253_);
v_i_boxed_3263_ = lean_unbox_usize(v_i_3254_);
lean_dec(v_i_3254_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__11(v___x_3251_, v_as_3252_, v_sz_boxed_3262_, v_i_boxed_3263_, v_b_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v_as_3252_);
lean_dec_ref(v___x_3251_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12(lean_object* v___x_3265_, lean_object* v_as_3266_, size_t v_sz_3267_, size_t v_i_3268_, lean_object* v_b_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___redArg(v___x_3265_, v_as_3266_, v_sz_3267_, v_i_3268_, v_b_3269_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12___boxed(lean_object* v___x_3277_, lean_object* v_as_3278_, lean_object* v_sz_3279_, lean_object* v_i_3280_, lean_object* v_b_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
size_t v_sz_boxed_3288_; size_t v_i_boxed_3289_; lean_object* v_res_3290_; 
v_sz_boxed_3288_ = lean_unbox_usize(v_sz_3279_);
lean_dec(v_sz_3279_);
v_i_boxed_3289_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__12(v___x_3277_, v_as_3278_, v_sz_boxed_3288_, v_i_boxed_3289_, v_b_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v_as_3278_);
lean_dec_ref(v___x_3277_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16(lean_object* v_upperBound_3291_, lean_object* v_inst_3292_, lean_object* v_R_3293_, lean_object* v_a_3294_, lean_object* v_b_3295_, lean_object* v_c_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___redArg(v_upperBound_3291_, v_a_3294_, v_b_3295_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16___boxed(lean_object* v_upperBound_3304_, lean_object* v_inst_3305_, lean_object* v_R_3306_, lean_object* v_a_3307_, lean_object* v_b_3308_, lean_object* v_c_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__16(v_upperBound_3304_, v_inst_3305_, v_R_3306_, v_a_3307_, v_b_3308_, v_c_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec(v_upperBound_3304_);
return v_res_3316_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1(lean_object* v_00_u03b2_3317_, lean_object* v_a_3318_, lean_object* v_x_3319_){
_start:
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___redArg(v_a_3318_, v_x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3321_, lean_object* v_a_3322_, lean_object* v_x_3323_){
_start:
{
uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_res_3324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__1_spec__1(v_00_u03b2_3321_, v_a_3322_, v_x_3323_);
lean_dec(v_x_3323_);
lean_dec(v_a_3322_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3(lean_object* v_00_u03b2_3326_, lean_object* v_data_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3___redArg(v_data_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4(lean_object* v_00_u03b2_3329_, lean_object* v_a_3330_, lean_object* v_b_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__4___redArg(v_a_3330_, v_b_3331_, v_x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3334_, lean_object* v_i_3335_, lean_object* v_source_3336_, lean_object* v_target_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4___redArg(v_i_3335_, v_source_3336_, v_target_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4_spec__19(lean_object* v_00_u03b2_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__2_spec__3_spec__4_spec__19___redArg(v_x_3340_, v_x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go_spec__0(lean_object* v_problem_3343_, lean_object* v_as_3344_, size_t v_i_3345_, size_t v_stop_3346_, lean_object* v_b_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = lean_usize_dec_eq(v_i_3345_, v_stop_3346_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_array_uget_borrowed(v_as_3344_, v_i_3345_);
lean_inc(v___x_3355_);
lean_inc_ref(v_problem_3343_);
v___x_3356_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_analyzeQuantifiedFact(v_problem_3343_, v___x_3355_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; size_t v___x_3358_; size_t v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = ((size_t)1ULL);
v___x_3359_ = lean_usize_add(v_i_3345_, v___x_3358_);
v_i_3345_ = v___x_3359_;
v_b_3347_ = v_a_3357_;
goto _start;
}
else
{
lean_dec_ref(v_problem_3343_);
return v___x_3356_;
}
}
else
{
lean_object* v___x_3361_; 
lean_dec_ref(v_problem_3343_);
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_b_3347_);
return v___x_3361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go_spec__0___boxed(lean_object* v_problem_3362_, lean_object* v_as_3363_, lean_object* v_i_3364_, lean_object* v_stop_3365_, lean_object* v_b_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
size_t v_i_boxed_3373_; size_t v_stop_boxed_3374_; lean_object* v_res_3375_; 
v_i_boxed_3373_ = lean_unbox_usize(v_i_3364_);
lean_dec(v_i_3364_);
v_stop_boxed_3374_ = lean_unbox_usize(v_stop_3365_);
lean_dec(v_stop_3365_);
v_res_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go_spec__0(v_problem_3362_, v_as_3363_, v_i_boxed_3373_, v_stop_boxed_3374_, v_b_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v_as_3363_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go(lean_object* v_problem_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_quantifiedFacts_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_quantifiedFacts_3383_ = lean_ctor_get(v_problem_3376_, 4);
lean_inc_ref(v_quantifiedFacts_3383_);
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = lean_array_get_size(v_quantifiedFacts_3383_);
v___x_3386_ = lean_nat_dec_lt(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_dec_ref(v_quantifiedFacts_3383_);
lean_dec_ref(v_problem_3376_);
v___x_3387_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze(v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; size_t v___x_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v___x_3388_ = lean_box(0);
v___x_3389_ = ((size_t)0ULL);
v___x_3390_ = lean_usize_of_nat(v___x_3385_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go_spec__0(v_problem_3376_, v_quantifiedFacts_3383_, v___x_3389_, v___x_3390_, v___x_3388_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec_ref(v_quantifiedFacts_3383_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref_known(v___x_3391_, 1);
v___x_3392_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze(v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
return v___x_3392_;
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
v_a_3393_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3391_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3391_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go___boxed(lean_object* v_problem_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go(v_problem_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
return v_res_3408_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__0(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_unsigned_to_nat(0u);
v___x_3410_ = l_Lean_UnionFind_emptyWithCapacity(v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__2(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_box(0);
v___x_3414_ = lean_unsigned_to_nat(16u);
v___x_3415_ = lean_mk_array(v___x_3414_, v___x_3413_);
return v___x_3415_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__3(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__2);
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___x_3416_);
return v___x_3418_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__4(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__3, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__3);
v___x_3420_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__1));
v___x_3421_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__0, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__0);
v___x_3422_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3420_);
lean_ctor_set(v___x_3422_, 2, v___x_3420_);
lean_ctor_set(v___x_3422_, 3, v___x_3419_);
lean_ctor_set(v___x_3422_, 4, v___x_3420_);
lean_ctor_set(v___x_3422_, 5, v___x_3420_);
lean_ctor_set(v___x_3422_, 6, v___x_3420_);
lean_ctor_set(v___x_3422_, 7, v___x_3420_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build(lean_object* v_problem_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__4, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___closed__4);
v___x_3430_ = lean_st_mk_ref(v___x_3429_);
v___x_3431_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_build_go(v_problem_3423_, v___x_3430_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3440_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3440_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3440_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_st_ref_get(v___x_3430_);
lean_dec(v___x_3430_);
lean_dec(v___x_3436_);
if (v_isShared_3435_ == 0)
{
v___x_3438_ = v___x_3434_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3432_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
else
{
lean_dec(v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build___boxed(lean_object* v_problem_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_build(v_problem_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg(lean_object* v_upperBound_3448_, lean_object* v_fst_3449_, lean_object* v_snd_3450_, lean_object* v_a_3451_, lean_object* v_b_3452_){
_start:
{
lean_object* v_a_3454_; uint8_t v___x_3458_; 
v___x_3458_ = lean_nat_dec_lt(v_a_3451_, v_upperBound_3448_);
if (v___x_3458_ == 0)
{
lean_dec(v_a_3451_);
lean_dec_ref(v_fst_3449_);
return v_b_3452_;
}
else
{
lean_object* v_classes_3459_; lean_object* v_varRoots_3460_; lean_object* v_posRoot_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_classes_3459_ = lean_ctor_get(v_b_3452_, 0);
v_varRoots_3460_ = lean_ctor_get(v_b_3452_, 1);
v_posRoot_3461_ = lean_ctor_get(v_b_3452_, 2);
lean_inc(v_a_3451_);
lean_inc_ref(v_fst_3449_);
v___x_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3462_, 0, v_fst_3449_);
lean_ctor_set(v___x_3462_, 1, v_a_3451_);
v___x_3463_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_posClass_spec__0___redArg(v_posRoot_3461_, v___x_3462_);
lean_dec_ref_known(v___x_3462_, 2);
if (lean_obj_tag(v___x_3463_) == 1)
{
lean_object* v_val_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_val_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_val_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v___x_3465_ = lean_array_fget_borrowed(v_snd_3450_, v_a_3451_);
v___x_3466_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f(v___x_3465_);
if (lean_obj_tag(v___x_3466_) == 1)
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3475_; 
lean_inc_ref(v_posRoot_3461_);
lean_inc_ref(v_varRoots_3460_);
lean_inc_ref(v_classes_3459_);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_b_3452_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; lean_object* v_unused_3477_; lean_object* v_unused_3478_; 
v_unused_3476_ = lean_ctor_get(v_b_3452_, 2);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_b_3452_, 1);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_b_3452_, 0);
lean_dec(v_unused_3478_);
v___x_3468_ = v_b_3452_;
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v_b_3452_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_val_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v_val_3470_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_val_3470_);
lean_dec_ref_known(v___x_3466_, 1);
v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_freeze_spec__3(v_val_3470_, v_classes_3459_, v_val_3464_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3471_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_varRoots_3460_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_posRoot_3461_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
v_a_3454_ = v___x_3473_;
goto v___jp_3453_;
}
}
}
else
{
lean_dec(v___x_3466_);
lean_dec(v_val_3464_);
v_a_3454_ = v_b_3452_;
goto v___jp_3453_;
}
}
else
{
lean_dec(v___x_3463_);
v_a_3454_ = v_b_3452_;
goto v___jp_3453_;
}
}
v___jp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = lean_nat_add(v_a_3451_, v___x_3455_);
lean_dec(v_a_3451_);
v_a_3451_ = v___x_3456_;
v_b_3452_ = v_a_3454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg___boxed(lean_object* v_upperBound_3479_, lean_object* v_fst_3480_, lean_object* v_snd_3481_, lean_object* v_a_3482_, lean_object* v_b_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg(v_upperBound_3479_, v_fst_3480_, v_snd_3481_, v_a_3482_, v_b_3483_);
lean_dec_ref(v_snd_3481_);
lean_dec(v_upperBound_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp(lean_object* v_sets_3485_, lean_object* v_app_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredApp_x3f(v_app_3486_);
if (lean_obj_tag(v___x_3487_) == 1)
{
lean_object* v_val_3488_; lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_val_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v_fst_3489_ = lean_ctor_get(v_val_3488_, 0);
lean_inc(v_fst_3489_);
v_snd_3490_ = lean_ctor_get(v_val_3488_, 1);
lean_inc(v_snd_3490_);
lean_dec(v_val_3488_);
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = lean_array_get_size(v_snd_3490_);
v___x_3493_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg(v___x_3492_, v_fst_3489_, v_snd_3490_, v___x_3491_, v_sets_3485_);
lean_dec(v_snd_3490_);
return v___x_3493_;
}
else
{
lean_dec(v___x_3487_);
return v_sets_3485_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0(lean_object* v_upperBound_3494_, lean_object* v_fst_3495_, lean_object* v_snd_3496_, lean_object* v_inst_3497_, lean_object* v_R_3498_, lean_object* v_a_3499_, lean_object* v_b_3500_, lean_object* v_c_3501_){
_start:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___redArg(v_upperBound_3494_, v_fst_3495_, v_snd_3496_, v_a_3499_, v_b_3500_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0___boxed(lean_object* v_upperBound_3503_, lean_object* v_fst_3504_, lean_object* v_snd_3505_, lean_object* v_inst_3506_, lean_object* v_R_3507_, lean_object* v_a_3508_, lean_object* v_b_3509_, lean_object* v_c_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp_spec__0(v_upperBound_3503_, v_fst_3504_, v_snd_3505_, v_inst_3506_, v_R_3507_, v_a_3508_, v_b_3509_, v_c_3510_);
lean_dec_ref(v_snd_3505_);
lean_dec(v_upperBound_3503_);
return v_res_3511_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__0(lean_object* v_e_3512_){
_start:
{
lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3513_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_toBvAuxArg_x3f___closed__6));
v___x_3514_ = l_Lean_Expr_isAppOf(v_e_3512_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Meta_Tactic_BVDecide_EPR_toBvPredAppArity_x3f(v_e_3512_);
if (lean_obj_tag(v___x_3515_) == 0)
{
return v___x_3514_;
}
else
{
uint8_t v___x_3516_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = 1;
return v___x_3516_;
}
}
else
{
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__0___boxed(lean_object* v_e_3517_){
_start:
{
uint8_t v_res_3518_; lean_object* v_r_3519_; 
v_res_3518_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__0(v_e_3517_);
lean_dec_ref(v_e_3517_);
v_r_3519_ = lean_box(v_res_3518_);
return v_r_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__1(lean_object* v_app_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3527_ = lean_st_ref_take(v___y_3521_);
v___x_3528_ = lean_box(0);
v___x_3529_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGroundApp(v___x_3527_, v_app_3520_);
v___x_3530_ = lean_st_ref_put(v___y_3521_, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3528_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__1___boxed(lean_object* v_app_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___lam__1(v_app_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg(lean_object* v_e_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v___x_3543_; lean_object* v_visited_3544_; size_t v___x_3545_; size_t v___x_3546_; size_t v___x_3547_; lean_object* v___x_3548_; size_t v___x_3549_; uint8_t v___x_3550_; 
v___x_3543_ = lean_st_ref_get(v_a_3541_);
v_visited_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc_ref(v_visited_3544_);
lean_dec(v___x_3543_);
v___x_3545_ = lean_ptr_addr(v_e_3540_);
v___x_3546_ = ((size_t)8191ULL);
v___x_3547_ = lean_usize_mod(v___x_3545_, v___x_3546_);
v___x_3548_ = lean_array_uget(v_visited_3544_, v___x_3547_);
lean_dec_ref(v_visited_3544_);
v___x_3549_ = lean_ptr_addr(v___x_3548_);
lean_dec(v___x_3548_);
v___x_3550_ = lean_usize_dec_eq(v___x_3549_, v___x_3545_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v_visited_3552_; lean_object* v_checked_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3564_; 
v___x_3551_ = lean_st_ref_take(v_a_3541_);
v_visited_3552_ = lean_ctor_get(v___x_3551_, 0);
v_checked_3553_ = lean_ctor_get(v___x_3551_, 1);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3555_ = v___x_3551_;
v_isShared_3556_ = v_isSharedCheck_3564_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_checked_3553_);
lean_inc(v_visited_3552_);
lean_dec(v___x_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3564_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_array_uset(v_visited_3552_, v___x_3547_, v_e_3540_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_checked_3553_);
v___x_3559_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_st_ref_put(v_a_3541_, v___x_3559_);
v___x_3561_ = lean_box(v___x_3550_);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
return v___x_3562_;
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec_ref(v_e_3540_);
v___x_3565_ = lean_box(v___x_3550_);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_e_3567_, lean_object* v_a_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg(v_e_3567_, v_a_3568_);
lean_dec(v_a_3568_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg(lean_object* v_e_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v_checked_3575_; uint8_t v___x_3576_; 
v___x_3574_ = lean_st_ref_get(v_a_3572_);
v_checked_3575_ = lean_ctor_get(v___x_3574_, 1);
lean_inc_ref(v_checked_3575_);
lean_dec(v___x_3574_);
v___x_3576_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__0___redArg(v_checked_3575_, v_e_3571_);
lean_dec_ref(v_checked_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v_visited_3578_; lean_object* v_checked_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3591_; 
v___x_3577_ = lean_st_ref_take(v_a_3572_);
v_visited_3578_ = lean_ctor_get(v___x_3577_, 0);
v_checked_3579_ = lean_ctor_get(v___x_3577_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3581_ = v___x_3577_;
v_isShared_3582_ = v_isSharedCheck_3591_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_checked_3579_);
lean_inc(v_visited_3578_);
lean_dec(v___x_3577_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3591_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3583_ = lean_box(0);
v___x_3584_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstClass_insertTerm_spec__1___redArg(v_checked_3579_, v_e_3571_, v___x_3583_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3584_);
v___x_3586_ = v___x_3581_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_visited_3578_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3587_ = lean_st_ref_put(v_a_3572_, v___x_3586_);
v___x_3588_ = lean_box(v___x_3576_);
v___x_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
}
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec_ref(v_e_3571_);
v___x_3592_ = lean_box(v___x_3576_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_e_3594_, lean_object* v_a_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg(v_e_3594_, v_a_3595_);
lean_dec(v_a_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(lean_object* v_p_3598_, lean_object* v_f_3599_, uint8_t v_stopWhenVisited_3600_, lean_object* v_e_3601_, lean_object* v_a_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v_d_3615_; lean_object* v_b_3616_; lean_object* v___y_3617_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___x_3647_; 
lean_inc_ref(v_e_3601_);
v___x_3647_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg(v_e_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3680_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3680_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3680_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_unbox(v_a_3648_);
lean_dec(v_a_3648_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
lean_del_object(v___x_3650_);
lean_inc_ref(v_p_3598_);
lean_inc_ref(v_e_3601_);
v___x_3653_ = lean_apply_1(v_p_3598_, v_e_3601_);
v___x_3654_ = lean_unbox(v___x_3653_);
if (v___x_3654_ == 0)
{
v___y_3621_ = v_a_3602_;
v___y_3622_ = v___y_3603_;
v___y_3623_ = v___y_3604_;
v___y_3624_ = v___y_3605_;
v___y_3625_ = v___y_3606_;
v___y_3626_ = v___y_3607_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3655_; 
lean_inc_ref(v_e_3601_);
v___x_3655_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg(v_e_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; uint8_t v___x_3657_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v___x_3657_ = lean_unbox(v_a_3656_);
lean_dec(v_a_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
lean_inc_ref(v_f_3599_);
lean_inc(v___y_3607_);
lean_inc_ref(v___y_3606_);
lean_inc(v___y_3605_);
lean_inc_ref(v___y_3604_);
lean_inc(v___y_3603_);
lean_inc_ref(v_e_3601_);
v___x_3658_ = lean_apply_7(v_f_3599_, v_e_3601_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, lean_box(0));
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3666_; 
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; 
v_unused_3667_ = lean_ctor_get(v___x_3658_, 0);
lean_dec(v_unused_3667_);
v___x_3660_ = v___x_3658_;
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
else
{
lean_dec(v___x_3658_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
if (v_stopWhenVisited_3600_ == 0)
{
lean_del_object(v___x_3660_);
v___y_3621_ = v_a_3602_;
v___y_3622_ = v___y_3603_;
v___y_3623_ = v___y_3604_;
v___y_3624_ = v___y_3605_;
v___y_3625_ = v___y_3606_;
v___y_3626_ = v___y_3607_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_dec_ref(v_e_3601_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
v___x_3662_ = lean_box(0);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3662_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_dec_ref(v_e_3601_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
return v___x_3658_;
}
}
else
{
v___y_3621_ = v_a_3602_;
v___y_3622_ = v___y_3603_;
v___y_3623_ = v___y_3604_;
v___y_3624_ = v___y_3605_;
v___y_3625_ = v___y_3606_;
v___y_3626_ = v___y_3607_;
goto v___jp_3620_;
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref(v_e_3601_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
v_a_3668_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3655_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3655_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_dec_ref(v_e_3601_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
v___x_3676_ = lean_box(0);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3676_);
v___x_3678_ = v___x_3650_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_e_3601_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
v_a_3681_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3647_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3647_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
v___jp_3609_:
{
lean_object* v___x_3618_; 
lean_inc_ref(v_f_3599_);
lean_inc_ref(v_p_3598_);
v___x_3618_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(v_p_3598_, v_f_3599_, v_stopWhenVisited_3600_, v_d_3615_, v___y_3617_, v___y_3614_, v___y_3612_, v___y_3611_, v___y_3610_, v___y_3613_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_dec_ref_known(v___x_3618_, 1);
v_e_3601_ = v_b_3616_;
v_a_3602_ = v___y_3617_;
v___y_3603_ = v___y_3614_;
v___y_3604_ = v___y_3612_;
v___y_3605_ = v___y_3611_;
v___y_3606_ = v___y_3610_;
v___y_3607_ = v___y_3613_;
goto _start;
}
else
{
lean_dec_ref(v_b_3616_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
return v___x_3618_;
}
}
v___jp_3620_:
{
switch(lean_obj_tag(v_e_3601_))
{
case 7:
{
lean_object* v_binderType_3627_; lean_object* v_body_3628_; 
v_binderType_3627_ = lean_ctor_get(v_e_3601_, 1);
lean_inc_ref(v_binderType_3627_);
v_body_3628_ = lean_ctor_get(v_e_3601_, 2);
lean_inc_ref(v_body_3628_);
lean_dec_ref_known(v_e_3601_, 3);
v___y_3610_ = v___y_3625_;
v___y_3611_ = v___y_3624_;
v___y_3612_ = v___y_3623_;
v___y_3613_ = v___y_3626_;
v___y_3614_ = v___y_3622_;
v_d_3615_ = v_binderType_3627_;
v_b_3616_ = v_body_3628_;
v___y_3617_ = v___y_3621_;
goto v___jp_3609_;
}
case 6:
{
lean_object* v_binderType_3629_; lean_object* v_body_3630_; 
v_binderType_3629_ = lean_ctor_get(v_e_3601_, 1);
lean_inc_ref(v_binderType_3629_);
v_body_3630_ = lean_ctor_get(v_e_3601_, 2);
lean_inc_ref(v_body_3630_);
lean_dec_ref_known(v_e_3601_, 3);
v___y_3610_ = v___y_3625_;
v___y_3611_ = v___y_3624_;
v___y_3612_ = v___y_3623_;
v___y_3613_ = v___y_3626_;
v___y_3614_ = v___y_3622_;
v_d_3615_ = v_binderType_3629_;
v_b_3616_ = v_body_3630_;
v___y_3617_ = v___y_3621_;
goto v___jp_3609_;
}
case 8:
{
lean_object* v_type_3631_; lean_object* v_value_3632_; lean_object* v_body_3633_; lean_object* v___x_3634_; 
v_type_3631_ = lean_ctor_get(v_e_3601_, 1);
lean_inc_ref(v_type_3631_);
v_value_3632_ = lean_ctor_get(v_e_3601_, 2);
lean_inc_ref(v_value_3632_);
v_body_3633_ = lean_ctor_get(v_e_3601_, 3);
lean_inc_ref(v_body_3633_);
lean_dec_ref_known(v_e_3601_, 4);
lean_inc_ref(v_f_3599_);
lean_inc_ref(v_p_3598_);
v___x_3634_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(v_p_3598_, v_f_3599_, v_stopWhenVisited_3600_, v_type_3631_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v___x_3635_; 
lean_dec_ref_known(v___x_3634_, 1);
lean_inc_ref(v_f_3599_);
lean_inc_ref(v_p_3598_);
v___x_3635_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(v_p_3598_, v_f_3599_, v_stopWhenVisited_3600_, v_value_3632_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_dec_ref_known(v___x_3635_, 1);
v_e_3601_ = v_body_3633_;
v_a_3602_ = v___y_3621_;
v___y_3603_ = v___y_3622_;
v___y_3604_ = v___y_3623_;
v___y_3605_ = v___y_3624_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3626_;
goto _start;
}
else
{
lean_dec_ref(v_body_3633_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
return v___x_3635_;
}
}
else
{
lean_dec_ref(v_body_3633_);
lean_dec_ref(v_value_3632_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
return v___x_3634_;
}
}
case 5:
{
lean_object* v_fn_3637_; lean_object* v_arg_3638_; lean_object* v___x_3639_; 
v_fn_3637_ = lean_ctor_get(v_e_3601_, 0);
lean_inc_ref(v_fn_3637_);
v_arg_3638_ = lean_ctor_get(v_e_3601_, 1);
lean_inc_ref(v_arg_3638_);
lean_dec_ref_known(v_e_3601_, 2);
lean_inc_ref(v_f_3599_);
lean_inc_ref(v_p_3598_);
v___x_3639_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(v_p_3598_, v_f_3599_, v_stopWhenVisited_3600_, v_fn_3637_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_dec_ref_known(v___x_3639_, 1);
v_e_3601_ = v_arg_3638_;
v_a_3602_ = v___y_3621_;
v___y_3603_ = v___y_3622_;
v___y_3604_ = v___y_3623_;
v___y_3605_ = v___y_3624_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3626_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3638_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
return v___x_3639_;
}
}
case 10:
{
lean_object* v_expr_3641_; 
v_expr_3641_ = lean_ctor_get(v_e_3601_, 1);
lean_inc_ref(v_expr_3641_);
lean_dec_ref_known(v_e_3601_, 2);
v_e_3601_ = v_expr_3641_;
v_a_3602_ = v___y_3621_;
v___y_3603_ = v___y_3622_;
v___y_3604_ = v___y_3623_;
v___y_3605_ = v___y_3624_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3626_;
goto _start;
}
case 11:
{
lean_object* v_struct_3643_; 
v_struct_3643_ = lean_ctor_get(v_e_3601_, 2);
lean_inc_ref(v_struct_3643_);
lean_dec_ref_known(v_e_3601_, 3);
v_e_3601_ = v_struct_3643_;
v_a_3602_ = v___y_3621_;
v___y_3603_ = v___y_3622_;
v___y_3604_ = v___y_3623_;
v___y_3605_ = v___y_3624_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3626_;
goto _start;
}
default: 
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_dec_ref(v_e_3601_);
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_p_3598_);
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0___boxed(lean_object* v_p_3689_, lean_object* v_f_3690_, lean_object* v_stopWhenVisited_3691_, lean_object* v_e_3692_, lean_object* v_a_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v_stopWhenVisited_boxed_3700_; lean_object* v_res_3701_; 
v_stopWhenVisited_boxed_3700_ = lean_unbox(v_stopWhenVisited_3691_);
v_res_3701_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(v_p_3689_, v_f_3690_, v_stopWhenVisited_boxed_3700_, v_e_3692_, v_a_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec(v_a_3693_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0(lean_object* v_p_3702_, lean_object* v_f_3703_, lean_object* v_e_3704_, uint8_t v_stopWhenVisited_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = l_Lean_ForEachExprWhere_initCache;
v___x_3713_ = lean_st_mk_ref(v___x_3712_);
v___x_3714_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0(v_p_3702_, v_f_3703_, v_stopWhenVisited_3705_, v_e_3704_, v___x_3713_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3723_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3723_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3723_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = lean_st_ref_get(v___x_3713_);
lean_dec(v___x_3713_);
lean_dec(v___x_3719_);
if (v_isShared_3718_ == 0)
{
v___x_3721_ = v___x_3717_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3715_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
else
{
lean_dec(v___x_3713_);
return v___x_3714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0___boxed(lean_object* v_p_3724_, lean_object* v_f_3725_, lean_object* v_e_3726_, lean_object* v_stopWhenVisited_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_stopWhenVisited_boxed_3734_; lean_object* v_res_3735_; 
v_stopWhenVisited_boxed_3734_ = lean_unbox(v_stopWhenVisited_3727_);
v_res_3735_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0(v_p_3724_, v_f_3725_, v_e_3726_, v_stopWhenVisited_boxed_3734_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround(lean_object* v_sets_3738_, lean_object* v_e_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_stop_3745_; lean_object* v___f_3746_; uint8_t v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_stop_3745_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__0));
v___f_3746_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___closed__1));
v___x_3747_ = 1;
v___x_3748_ = lean_st_mk_ref(v_sets_3738_);
v___x_3749_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0(v_stop_3745_, v___f_3746_, v_e_3739_, v___x_3747_, v___x_3748_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3757_; 
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v___x_3749_, 0);
lean_dec(v_unused_3758_);
v___x_3751_ = v___x_3749_;
v_isShared_3752_ = v_isSharedCheck_3757_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v___x_3749_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3757_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3753_ = lean_st_ref_get(v___x_3748_);
lean_dec(v___x_3748_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 0, v___x_3753_);
v___x_3755_ = v___x_3751_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v___x_3748_);
v_a_3759_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3749_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3749_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround___boxed(lean_object* v_sets_3767_, lean_object* v_e_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround(v_sets_3767_, v_e_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1(lean_object* v_e_3775_, lean_object* v_a_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___redArg(v_e_3775_, v_a_3776_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1___boxed(lean_object* v_e_3784_, lean_object* v_a_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__1(v_e_3784_, v_a_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec(v_a_3785_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2(lean_object* v_e_3793_, lean_object* v_a_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___redArg(v_e_3793_, v_a_3794_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2___boxed(lean_object* v_e_3802_, lean_object* v_a_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_addGround_spec__0_spec__0_spec__2(v_e_3802_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec(v_a_3803_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2(lean_object* v_msgData_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; lean_object* v_env_3818_; uint8_t v___x_3819_; lean_object* v_env_3820_; lean_object* v___x_3821_; lean_object* v_toCold_3822_; lean_object* v_mctx_3823_; lean_object* v_lctx_3824_; lean_object* v_options_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3817_ = lean_st_ref_get(v___y_3815_);
v_env_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc_ref(v_env_3818_);
lean_dec(v___x_3817_);
v___x_3819_ = 0;
v_env_3820_ = l_Lean_Environment_setRecordingDeps(v_env_3818_, v___x_3819_);
v___x_3821_ = lean_st_ref_get(v___y_3813_);
v_toCold_3822_ = lean_ctor_get(v___y_3814_, 0);
v_mctx_3823_ = lean_ctor_get(v___x_3821_, 0);
lean_inc_ref(v_mctx_3823_);
lean_dec(v___x_3821_);
v_lctx_3824_ = lean_ctor_get(v___y_3812_, 2);
v_options_3825_ = lean_ctor_get(v_toCold_3822_, 2);
lean_inc_ref(v_options_3825_);
lean_inc_ref(v_lctx_3824_);
v___x_3826_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3826_, 0, v_env_3820_);
lean_ctor_set(v___x_3826_, 1, v_mctx_3823_);
lean_ctor_set(v___x_3826_, 2, v_lctx_3824_);
lean_ctor_set(v___x_3826_, 3, v_options_3825_);
v___x_3827_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
lean_ctor_set(v___x_3827_, 1, v_msgData_3811_);
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2___boxed(lean_object* v_msgData_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2(v_msgData_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3835_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3836_; double v___x_3837_; 
v___x_3836_ = lean_unsigned_to_nat(0u);
v___x_3837_ = lean_float_of_nat(v___x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(lean_object* v_cls_3841_, lean_object* v_msg_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_ref_3848_; lean_object* v___x_3849_; lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3895_; 
v_ref_3848_ = lean_ctor_get(v___y_3845_, 2);
v___x_3849_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2(v_msg_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3852_ = v___x_3849_;
v_isShared_3853_ = v_isSharedCheck_3895_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3895_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v_traceState_3855_; lean_object* v_env_3856_; lean_object* v_nextMacroScope_3857_; lean_object* v_ngen_3858_; lean_object* v_auxDeclNGen_3859_; lean_object* v_cache_3860_; lean_object* v_recordedDeps_3861_; lean_object* v_messages_3862_; lean_object* v_infoState_3863_; lean_object* v_snapshotTasks_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3894_; 
v___x_3854_ = lean_st_ref_take(v___y_3846_);
v_traceState_3855_ = lean_ctor_get(v___x_3854_, 4);
v_env_3856_ = lean_ctor_get(v___x_3854_, 0);
v_nextMacroScope_3857_ = lean_ctor_get(v___x_3854_, 1);
v_ngen_3858_ = lean_ctor_get(v___x_3854_, 2);
v_auxDeclNGen_3859_ = lean_ctor_get(v___x_3854_, 3);
v_cache_3860_ = lean_ctor_get(v___x_3854_, 5);
v_recordedDeps_3861_ = lean_ctor_get(v___x_3854_, 6);
v_messages_3862_ = lean_ctor_get(v___x_3854_, 7);
v_infoState_3863_ = lean_ctor_get(v___x_3854_, 8);
v_snapshotTasks_3864_ = lean_ctor_get(v___x_3854_, 9);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3866_ = v___x_3854_;
v_isShared_3867_ = v_isSharedCheck_3894_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_snapshotTasks_3864_);
lean_inc(v_infoState_3863_);
lean_inc(v_messages_3862_);
lean_inc(v_recordedDeps_3861_);
lean_inc(v_cache_3860_);
lean_inc(v_traceState_3855_);
lean_inc(v_auxDeclNGen_3859_);
lean_inc(v_ngen_3858_);
lean_inc(v_nextMacroScope_3857_);
lean_inc(v_env_3856_);
lean_dec(v___x_3854_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3894_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
uint64_t v_tid_3868_; lean_object* v_traces_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3893_; 
v_tid_3868_ = lean_ctor_get_uint64(v_traceState_3855_, sizeof(void*)*1);
v_traces_3869_ = lean_ctor_get(v_traceState_3855_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_traceState_3855_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3871_ = v_traceState_3855_;
v_isShared_3872_ = v_isSharedCheck_3893_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_traces_3869_);
lean_dec(v_traceState_3855_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3893_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; double v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3873_ = lean_box(0);
v___x_3874_ = lean_box(0);
v___x_3875_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0);
v___x_3876_ = 0;
v___x_3877_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1));
v___x_3878_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3878_, 0, v_cls_3841_);
lean_ctor_set(v___x_3878_, 1, v___x_3874_);
lean_ctor_set(v___x_3878_, 2, v___x_3877_);
lean_ctor_set_float(v___x_3878_, sizeof(void*)*3, v___x_3875_);
lean_ctor_set_float(v___x_3878_, sizeof(void*)*3 + 8, v___x_3875_);
lean_ctor_set_uint8(v___x_3878_, sizeof(void*)*3 + 16, v___x_3876_);
v___x_3879_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__2));
v___x_3880_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v_a_3850_);
lean_ctor_set(v___x_3880_, 2, v___x_3879_);
lean_inc(v_ref_3848_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_ref_3848_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_PersistentArray_push___redArg(v_traces_3869_, v___x_3881_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3882_);
v___x_3884_ = v___x_3871_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3882_);
lean_ctor_set_uint64(v_reuseFailAlloc_3892_, sizeof(void*)*1, v_tid_3868_);
v___x_3884_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3886_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 4, v___x_3884_);
v___x_3886_ = v___x_3866_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_env_3856_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_nextMacroScope_3857_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_ngen_3858_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_auxDeclNGen_3859_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3891_, 5, v_cache_3860_);
lean_ctor_set(v_reuseFailAlloc_3891_, 6, v_recordedDeps_3861_);
lean_ctor_set(v_reuseFailAlloc_3891_, 7, v_messages_3862_);
lean_ctor_set(v_reuseFailAlloc_3891_, 8, v_infoState_3863_);
lean_ctor_set(v_reuseFailAlloc_3891_, 9, v_snapshotTasks_3864_);
v___x_3886_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = lean_st_ref_put(v___y_3846_, v___x_3886_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3873_);
v___x_3889_ = v___x_3852_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3873_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___boxed(lean_object* v_cls_3896_, lean_object* v_msg_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(v_cls_3896_, v_msg_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg(lean_object* v_hi_3904_, lean_object* v_pivot_3905_, lean_object* v_as_3906_, lean_object* v_i_3907_, lean_object* v_k_3908_){
_start:
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_nat_dec_lt(v_k_3908_, v_hi_3904_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec(v_k_3908_);
v___x_3910_ = lean_array_fswap(v_as_3906_, v_i_3907_, v_hi_3904_);
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v_i_3907_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; uint8_t v___x_3913_; 
v___x_3912_ = lean_array_fget_borrowed(v_as_3906_, v_k_3908_);
v___x_3913_ = lean_nat_dec_lt(v___x_3912_, v_pivot_3905_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_nat_add(v_k_3908_, v___x_3914_);
lean_dec(v_k_3908_);
v_k_3908_ = v___x_3915_;
goto _start;
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3917_ = lean_array_fswap(v_as_3906_, v_i_3907_, v_k_3908_);
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = lean_nat_add(v_i_3907_, v___x_3918_);
lean_dec(v_i_3907_);
v___x_3920_ = lean_nat_add(v_k_3908_, v___x_3918_);
lean_dec(v_k_3908_);
v_as_3906_ = v___x_3917_;
v_i_3907_ = v___x_3919_;
v_k_3908_ = v___x_3920_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg___boxed(lean_object* v_hi_3922_, lean_object* v_pivot_3923_, lean_object* v_as_3924_, lean_object* v_i_3925_, lean_object* v_k_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg(v_hi_3922_, v_pivot_3923_, v_as_3924_, v_i_3925_, v_k_3926_);
lean_dec(v_pivot_3923_);
lean_dec(v_hi_3922_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg(lean_object* v_n_3928_, lean_object* v_as_3929_, lean_object* v_lo_3930_, lean_object* v_hi_3931_){
_start:
{
lean_object* v___y_3933_; uint8_t v___x_3943_; 
v___x_3943_ = lean_nat_dec_lt(v_lo_3930_, v_hi_3931_);
if (v___x_3943_ == 0)
{
lean_dec(v_lo_3930_);
return v_as_3929_;
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v_mid_3946_; lean_object* v___y_3948_; lean_object* v___y_3954_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3944_ = lean_nat_add(v_lo_3930_, v_hi_3931_);
v___x_3945_ = lean_unsigned_to_nat(1u);
v_mid_3946_ = lean_nat_shiftr(v___x_3944_, v___x_3945_);
lean_dec(v___x_3944_);
v___x_3959_ = lean_array_fget_borrowed(v_as_3929_, v_mid_3946_);
v___x_3960_ = lean_array_fget_borrowed(v_as_3929_, v_lo_3930_);
v___x_3961_ = lean_nat_dec_lt(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
v___y_3954_ = v_as_3929_;
goto v___jp_3953_;
}
else
{
lean_object* v___x_3962_; 
v___x_3962_ = lean_array_fswap(v_as_3929_, v_lo_3930_, v_mid_3946_);
v___y_3954_ = v___x_3962_;
goto v___jp_3953_;
}
v___jp_3947_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = lean_array_fget_borrowed(v___y_3948_, v_mid_3946_);
v___x_3950_ = lean_array_fget_borrowed(v___y_3948_, v_hi_3931_);
v___x_3951_ = lean_nat_dec_lt(v___x_3949_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_dec(v_mid_3946_);
v___y_3933_ = v___y_3948_;
goto v___jp_3932_;
}
else
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_array_fswap(v___y_3948_, v_mid_3946_, v_hi_3931_);
lean_dec(v_mid_3946_);
v___y_3933_ = v___x_3952_;
goto v___jp_3932_;
}
}
v___jp_3953_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3955_ = lean_array_fget_borrowed(v___y_3954_, v_hi_3931_);
v___x_3956_ = lean_array_fget_borrowed(v___y_3954_, v_lo_3930_);
v___x_3957_ = lean_nat_dec_lt(v___x_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
v___y_3948_ = v___y_3954_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_array_fswap(v___y_3954_, v_lo_3930_, v_hi_3931_);
v___y_3948_ = v___x_3958_;
goto v___jp_3947_;
}
}
}
v___jp_3932_:
{
lean_object* v_pivot_3934_; lean_object* v___x_3935_; lean_object* v_fst_3936_; lean_object* v_snd_3937_; uint8_t v___x_3938_; 
v_pivot_3934_ = lean_array_fget(v___y_3933_, v_hi_3931_);
lean_inc_n(v_lo_3930_, 2);
v___x_3935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg(v_hi_3931_, v_pivot_3934_, v___y_3933_, v_lo_3930_, v_lo_3930_);
lean_dec(v_pivot_3934_);
v_fst_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_fst_3936_);
v_snd_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_snd_3937_);
lean_dec_ref(v___x_3935_);
v___x_3938_ = lean_nat_dec_le(v_hi_3931_, v_fst_3936_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg(v_n_3928_, v_snd_3937_, v_lo_3930_, v_fst_3936_);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_nat_add(v_fst_3936_, v___x_3940_);
lean_dec(v_fst_3936_);
v_as_3929_ = v___x_3939_;
v_lo_3930_ = v___x_3941_;
goto _start;
}
else
{
lean_dec(v_fst_3936_);
lean_dec(v_lo_3930_);
return v_snd_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg___boxed(lean_object* v_n_3963_, lean_object* v_as_3964_, lean_object* v_lo_3965_, lean_object* v_hi_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg(v_n_3963_, v_as_3964_, v_lo_3965_, v_hi_3966_);
lean_dec(v_hi_3966_);
lean_dec(v_n_3963_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__4(lean_object* v_x_3968_, lean_object* v_x_3969_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 0)
{
return v_x_3968_;
}
else
{
lean_object* v_key_3970_; lean_object* v_tail_3971_; lean_object* v___x_3972_; 
v_key_3970_ = lean_ctor_get(v_x_3969_, 0);
lean_inc(v_key_3970_);
v_tail_3971_ = lean_ctor_get(v_x_3969_, 2);
lean_inc(v_tail_3971_);
lean_dec_ref_known(v_x_3969_, 3);
v___x_3972_ = lean_array_push(v_x_3968_, v_key_3970_);
v_x_3968_ = v___x_3972_;
v_x_3969_ = v_tail_3971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__5(lean_object* v_as_3974_, size_t v_i_3975_, size_t v_stop_3976_, lean_object* v_b_3977_){
_start:
{
uint8_t v___x_3978_; 
v___x_3978_ = lean_usize_dec_eq(v_i_3975_, v_stop_3976_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; size_t v___x_3981_; size_t v___x_3982_; 
v___x_3979_ = lean_array_uget_borrowed(v_as_3974_, v_i_3975_);
lean_inc(v___x_3979_);
v___x_3980_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__4(v_b_3977_, v___x_3979_);
v___x_3981_ = ((size_t)1ULL);
v___x_3982_ = lean_usize_add(v_i_3975_, v___x_3981_);
v_i_3975_ = v___x_3982_;
v_b_3977_ = v___x_3980_;
goto _start;
}
else
{
return v_b_3977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__5___boxed(lean_object* v_as_3984_, lean_object* v_i_3985_, lean_object* v_stop_3986_, lean_object* v_b_3987_){
_start:
{
size_t v_i_boxed_3988_; size_t v_stop_boxed_3989_; lean_object* v_res_3990_; 
v_i_boxed_3988_ = lean_unbox_usize(v_i_3985_);
lean_dec(v_i_3985_);
v_stop_boxed_3989_ = lean_unbox_usize(v_stop_3986_);
lean_dec(v_stop_3986_);
v_res_3990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__5(v_as_3984_, v_i_boxed_3988_, v_stop_boxed_3989_, v_b_3987_);
lean_dec_ref(v_as_3984_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__1(lean_object* v_a_3991_, lean_object* v_a_3992_){
_start:
{
if (lean_obj_tag(v_a_3991_) == 0)
{
lean_object* v___x_3993_; 
v___x_3993_ = l_List_reverse___redArg(v_a_3992_);
return v___x_3993_;
}
else
{
lean_object* v_head_3994_; lean_object* v_tail_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4006_; 
v_head_3994_ = lean_ctor_get(v_a_3991_, 0);
v_tail_3995_ = lean_ctor_get(v_a_3991_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_a_3991_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3997_ = v_a_3991_;
v_isShared_3998_ = v_isSharedCheck_4006_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_tail_3995_);
lean_inc(v_head_3994_);
lean_dec(v_a_3991_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4006_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_3999_ = l_Nat_reprFast(v_head_3994_);
v___x_4000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
v___x_4001_ = l_Lean_MessageData_ofFormat(v___x_4000_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 1, v_a_3992_);
lean_ctor_set(v___x_3997_, 0, v___x_4001_);
v___x_4003_ = v___x_3997_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_a_3992_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
v_a_3991_ = v_tail_3995_;
v_a_3992_ = v___x_4003_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__7(lean_object* v_x_4007_, lean_object* v_x_4008_){
_start:
{
if (lean_obj_tag(v_x_4008_) == 0)
{
return v_x_4007_;
}
else
{
lean_object* v_key_4009_; lean_object* v_tail_4010_; lean_object* v___x_4011_; 
v_key_4009_ = lean_ctor_get(v_x_4008_, 0);
lean_inc(v_key_4009_);
v_tail_4010_ = lean_ctor_get(v_x_4008_, 2);
lean_inc(v_tail_4010_);
lean_dec_ref_known(v_x_4008_, 3);
v___x_4011_ = lean_array_push(v_x_4007_, v_key_4009_);
v_x_4007_ = v___x_4011_;
v_x_4008_ = v_tail_4010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__8(lean_object* v_as_4013_, size_t v_i_4014_, size_t v_stop_4015_, lean_object* v_b_4016_){
_start:
{
uint8_t v___x_4017_; 
v___x_4017_ = lean_usize_dec_eq(v_i_4014_, v_stop_4015_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; lean_object* v___x_4019_; size_t v___x_4020_; size_t v___x_4021_; 
v___x_4018_ = lean_array_uget_borrowed(v_as_4013_, v_i_4014_);
lean_inc(v___x_4018_);
v___x_4019_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__7(v_b_4016_, v___x_4018_);
v___x_4020_ = ((size_t)1ULL);
v___x_4021_ = lean_usize_add(v_i_4014_, v___x_4020_);
v_i_4014_ = v___x_4021_;
v_b_4016_ = v___x_4019_;
goto _start;
}
else
{
return v_b_4016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__8___boxed(lean_object* v_as_4023_, lean_object* v_i_4024_, lean_object* v_stop_4025_, lean_object* v_b_4026_){
_start:
{
size_t v_i_boxed_4027_; size_t v_stop_boxed_4028_; lean_object* v_res_4029_; 
v_i_boxed_4027_ = lean_unbox_usize(v_i_4024_);
lean_dec(v_i_4024_);
v_stop_boxed_4028_ = lean_unbox_usize(v_stop_4025_);
lean_dec(v_stop_4025_);
v_res_4029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__8(v_as_4023_, v_i_boxed_4027_, v_stop_boxed_4028_, v_b_4026_);
lean_dec_ref(v_as_4023_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__0(lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
if (lean_obj_tag(v_a_4030_) == 0)
{
lean_object* v___x_4032_; 
v___x_4032_ = l_List_reverse___redArg(v_a_4031_);
return v___x_4032_;
}
else
{
lean_object* v_head_4033_; lean_object* v_tail_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4043_; 
v_head_4033_ = lean_ctor_get(v_a_4030_, 0);
v_tail_4034_ = lean_ctor_get(v_a_4030_, 1);
v_isSharedCheck_4043_ = !lean_is_exclusive(v_a_4030_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4036_ = v_a_4030_;
v_isShared_4037_ = v_isSharedCheck_4043_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_tail_4034_);
lean_inc(v_head_4033_);
lean_dec(v_a_4030_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4043_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4038_ = l_Lean_MessageData_ofExpr(v_head_4033_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v_a_4031_);
lean_ctor_set(v___x_4036_, 0, v___x_4038_);
v___x_4040_ = v___x_4036_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_a_4031_);
v___x_4040_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
v_a_4030_ = v_tail_4034_;
v_a_4031_ = v___x_4040_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg(lean_object* v_hi_4044_, lean_object* v_pivot_4045_, lean_object* v_as_4046_, lean_object* v_i_4047_, lean_object* v_k_4048_){
_start:
{
uint8_t v___x_4049_; 
v___x_4049_ = lean_nat_dec_lt(v_k_4048_, v_hi_4044_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
lean_dec(v_k_4048_);
v___x_4050_ = lean_array_fswap(v_as_4046_, v_i_4047_, v_hi_4044_);
v___x_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4051_, 0, v_i_4047_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
return v___x_4051_;
}
else
{
lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4052_ = lean_array_fget_borrowed(v_as_4046_, v_k_4048_);
v___x_4053_ = lean_expr_lt(v___x_4052_, v_pivot_4045_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_unsigned_to_nat(1u);
v___x_4055_ = lean_nat_add(v_k_4048_, v___x_4054_);
lean_dec(v_k_4048_);
v_k_4048_ = v___x_4055_;
goto _start;
}
else
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4057_ = lean_array_fswap(v_as_4046_, v_i_4047_, v_k_4048_);
v___x_4058_ = lean_unsigned_to_nat(1u);
v___x_4059_ = lean_nat_add(v_i_4047_, v___x_4058_);
lean_dec(v_i_4047_);
v___x_4060_ = lean_nat_add(v_k_4048_, v___x_4058_);
lean_dec(v_k_4048_);
v_as_4046_ = v___x_4057_;
v_i_4047_ = v___x_4059_;
v_k_4048_ = v___x_4060_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg___boxed(lean_object* v_hi_4062_, lean_object* v_pivot_4063_, lean_object* v_as_4064_, lean_object* v_i_4065_, lean_object* v_k_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg(v_hi_4062_, v_pivot_4063_, v_as_4064_, v_i_4065_, v_k_4066_);
lean_dec_ref(v_pivot_4063_);
lean_dec(v_hi_4062_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg(lean_object* v_n_4068_, lean_object* v_as_4069_, lean_object* v_lo_4070_, lean_object* v_hi_4071_){
_start:
{
lean_object* v___y_4073_; uint8_t v___x_4083_; 
v___x_4083_ = lean_nat_dec_lt(v_lo_4070_, v_hi_4071_);
if (v___x_4083_ == 0)
{
lean_dec(v_lo_4070_);
return v_as_4069_;
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v_mid_4086_; lean_object* v___y_4088_; lean_object* v___y_4094_; lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4084_ = lean_nat_add(v_lo_4070_, v_hi_4071_);
v___x_4085_ = lean_unsigned_to_nat(1u);
v_mid_4086_ = lean_nat_shiftr(v___x_4084_, v___x_4085_);
lean_dec(v___x_4084_);
v___x_4099_ = lean_array_fget_borrowed(v_as_4069_, v_mid_4086_);
v___x_4100_ = lean_array_fget_borrowed(v_as_4069_, v_lo_4070_);
v___x_4101_ = lean_expr_lt(v___x_4099_, v___x_4100_);
if (v___x_4101_ == 0)
{
v___y_4094_ = v_as_4069_;
goto v___jp_4093_;
}
else
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_array_fswap(v_as_4069_, v_lo_4070_, v_mid_4086_);
v___y_4094_ = v___x_4102_;
goto v___jp_4093_;
}
v___jp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v___x_4089_ = lean_array_fget_borrowed(v___y_4088_, v_mid_4086_);
v___x_4090_ = lean_array_fget_borrowed(v___y_4088_, v_hi_4071_);
v___x_4091_ = lean_expr_lt(v___x_4089_, v___x_4090_);
if (v___x_4091_ == 0)
{
lean_dec(v_mid_4086_);
v___y_4073_ = v___y_4088_;
goto v___jp_4072_;
}
else
{
lean_object* v___x_4092_; 
v___x_4092_ = lean_array_fswap(v___y_4088_, v_mid_4086_, v_hi_4071_);
lean_dec(v_mid_4086_);
v___y_4073_ = v___x_4092_;
goto v___jp_4072_;
}
}
v___jp_4093_:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; 
v___x_4095_ = lean_array_fget_borrowed(v___y_4094_, v_hi_4071_);
v___x_4096_ = lean_array_fget_borrowed(v___y_4094_, v_lo_4070_);
v___x_4097_ = lean_expr_lt(v___x_4095_, v___x_4096_);
if (v___x_4097_ == 0)
{
v___y_4088_ = v___y_4094_;
goto v___jp_4087_;
}
else
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_array_fswap(v___y_4094_, v_lo_4070_, v_hi_4071_);
v___y_4088_ = v___x_4098_;
goto v___jp_4087_;
}
}
}
v___jp_4072_:
{
lean_object* v_pivot_4074_; lean_object* v___x_4075_; lean_object* v_fst_4076_; lean_object* v_snd_4077_; uint8_t v___x_4078_; 
v_pivot_4074_ = lean_array_fget(v___y_4073_, v_hi_4071_);
lean_inc_n(v_lo_4070_, 2);
v___x_4075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg(v_hi_4071_, v_pivot_4074_, v___y_4073_, v_lo_4070_, v_lo_4070_);
lean_dec(v_pivot_4074_);
v_fst_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_fst_4076_);
v_snd_4077_ = lean_ctor_get(v___x_4075_, 1);
lean_inc(v_snd_4077_);
lean_dec_ref(v___x_4075_);
v___x_4078_ = lean_nat_dec_le(v_hi_4071_, v_fst_4076_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg(v_n_4068_, v_snd_4077_, v_lo_4070_, v_fst_4076_);
v___x_4080_ = lean_unsigned_to_nat(1u);
v___x_4081_ = lean_nat_add(v_fst_4076_, v___x_4080_);
lean_dec(v_fst_4076_);
v_as_4069_ = v___x_4079_;
v_lo_4070_ = v___x_4081_;
goto _start;
}
else
{
lean_dec(v_fst_4076_);
lean_dec(v_lo_4070_);
return v_snd_4077_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg___boxed(lean_object* v_n_4103_, lean_object* v_as_4104_, lean_object* v_lo_4105_, lean_object* v_hi_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg(v_n_4103_, v_as_4104_, v_lo_4105_, v_hi_4106_);
lean_dec(v_hi_4106_);
lean_dec(v_n_4103_);
return v_res_4107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7(void){
_start:
{
lean_object* v_cls_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_cls_4121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_4122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__6));
v___x_4123_ = l_Lean_Name_append(v___x_4122_, v_cls_4121_);
return v___x_4123_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__8));
v___x_4126_ = l_Lean_stringToMessageData(v___x_4125_);
return v___x_4126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__11(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__10));
v___x_4129_ = l_Lean_stringToMessageData(v___x_4128_);
return v___x_4129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__13(void){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__12));
v___x_4132_ = l_Lean_stringToMessageData(v___x_4131_);
return v___x_4132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__15(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__14));
v___x_4135_ = l_Lean_stringToMessageData(v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass(lean_object* v_root_4137_, lean_object* v_cls_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
uint8_t v_full_4147_; lean_object* v_terms_4148_; lean_object* v_exceptions_4149_; lean_object* v_avoid_4150_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4256_; 
v_full_4147_ = lean_ctor_get_uint8(v_cls_4138_, sizeof(void*)*5);
v_terms_4148_ = lean_ctor_get(v_cls_4138_, 1);
lean_inc_ref(v_terms_4148_);
v_exceptions_4149_ = lean_ctor_get(v_cls_4138_, 3);
lean_inc_ref(v_exceptions_4149_);
v_avoid_4150_ = lean_ctor_get(v_cls_4138_, 4);
lean_inc_ref(v_avoid_4150_);
lean_dec_ref(v_cls_4138_);
if (v_full_4147_ == 0)
{
lean_object* v___x_4266_; 
v___x_4266_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1));
v___y_4256_ = v___x_4266_;
goto v___jp_4255_;
}
else
{
lean_object* v___x_4267_; 
v___x_4267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__16));
v___y_4256_ = v___x_4267_;
goto v___jp_4255_;
}
v___jp_4144_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = lean_box(0);
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
v___jp_4151_:
{
lean_object* v_toCold_4155_; lean_object* v_options_4156_; uint8_t v_hasTrace_4157_; 
v_toCold_4155_ = lean_ctor_get(v_a_4141_, 0);
v_options_4156_ = lean_ctor_get(v_toCold_4155_, 2);
v_hasTrace_4157_ = lean_ctor_get_uint8(v_options_4156_, sizeof(void*)*1);
if (v_hasTrace_4157_ == 0)
{
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_terms_4148_);
lean_dec(v_root_4137_);
goto v___jp_4144_;
}
else
{
lean_object* v_inheritedTraceOptions_4158_; lean_object* v_cls_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_inheritedTraceOptions_4158_ = lean_ctor_get(v_toCold_4155_, 11);
v_cls_4159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_4160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7);
v___x_4161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4158_, v_options_4156_, v___x_4160_);
if (v___x_4161_ == 0)
{
lean_dec_ref(v___y_4154_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_terms_4148_);
lean_dec(v_root_4137_);
goto v___jp_4144_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9);
v___x_4163_ = l_Nat_reprFast(v_root_4137_);
v___x_4164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
v___x_4165_ = l_Lean_MessageData_ofFormat(v___x_4164_);
v___x_4166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4162_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__11);
v___x_4168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = lean_array_to_list(v_terms_4148_);
v___x_4170_ = lean_box(0);
v___x_4171_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__0(v___x_4169_, v___x_4170_);
v___x_4172_ = l_Lean_MessageData_ofList(v___x_4171_);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4168_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__13, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__13_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__13);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = lean_array_to_list(v___y_4152_);
v___x_4177_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__0(v___x_4176_, v___x_4170_);
v___x_4178_ = l_Lean_MessageData_ofList(v___x_4177_);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4175_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__15);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = lean_array_to_list(v___y_4154_);
v___x_4183_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__1(v___x_4182_, v___x_4170_);
v___x_4184_ = l_Lean_MessageData_ofList(v___x_4183_);
v___x_4185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4181_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
lean_inc_ref(v___y_4153_);
v___x_4186_ = l_Lean_stringToMessageData(v___y_4153_);
v___x_4187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4185_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(v_cls_4159_, v___x_4187_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
return v___x_4188_;
}
}
}
v___jp_4189_:
{
lean_object* v___x_4196_; 
v___x_4196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg(v___y_4190_, v___y_4194_, v___y_4191_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec(v___y_4190_);
v___y_4152_ = v___y_4192_;
v___y_4153_ = v___y_4193_;
v___y_4154_ = v___x_4196_;
goto v___jp_4151_;
}
v___jp_4197_:
{
uint8_t v___x_4204_; 
v___x_4204_ = lean_nat_dec_le(v___y_4203_, v___y_4198_);
if (v___x_4204_ == 0)
{
lean_dec(v___y_4198_);
lean_inc(v___y_4203_);
v___y_4190_ = v___y_4199_;
v___y_4191_ = v___y_4203_;
v___y_4192_ = v___y_4200_;
v___y_4193_ = v___y_4201_;
v___y_4194_ = v___y_4202_;
v___y_4195_ = v___y_4203_;
goto v___jp_4189_;
}
else
{
v___y_4190_ = v___y_4199_;
v___y_4191_ = v___y_4203_;
v___y_4192_ = v___y_4200_;
v___y_4193_ = v___y_4201_;
v___y_4194_ = v___y_4202_;
v___y_4195_ = v___y_4198_;
goto v___jp_4189_;
}
}
v___jp_4205_:
{
lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4211_ = lean_array_get_size(v___y_4210_);
v___x_4212_ = lean_nat_dec_eq(v___x_4211_, v___y_4208_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; uint8_t v___x_4214_; 
v___x_4213_ = lean_nat_sub(v___x_4211_, v___y_4206_);
v___x_4214_ = lean_nat_dec_le(v___y_4208_, v___x_4213_);
if (v___x_4214_ == 0)
{
lean_dec(v___y_4208_);
lean_inc(v___x_4213_);
v___y_4198_ = v___x_4213_;
v___y_4199_ = v___x_4211_;
v___y_4200_ = v___y_4207_;
v___y_4201_ = v___y_4209_;
v___y_4202_ = v___y_4210_;
v___y_4203_ = v___x_4213_;
goto v___jp_4197_;
}
else
{
v___y_4198_ = v___x_4213_;
v___y_4199_ = v___x_4211_;
v___y_4200_ = v___y_4207_;
v___y_4201_ = v___y_4209_;
v___y_4202_ = v___y_4210_;
v___y_4203_ = v___y_4208_;
goto v___jp_4197_;
}
}
else
{
lean_dec(v___y_4208_);
v___y_4152_ = v___y_4207_;
v___y_4153_ = v___y_4209_;
v___y_4154_ = v___y_4210_;
goto v___jp_4151_;
}
}
v___jp_4215_:
{
lean_object* v_size_4220_; lean_object* v_buckets_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v_size_4220_ = lean_ctor_get(v_avoid_4150_, 0);
lean_inc(v_size_4220_);
v_buckets_4221_ = lean_ctor_get(v_avoid_4150_, 1);
lean_inc_ref(v_buckets_4221_);
lean_dec_ref(v_avoid_4150_);
v___x_4222_ = lean_mk_empty_array_with_capacity(v_size_4220_);
lean_dec(v_size_4220_);
v___x_4223_ = lean_array_get_size(v_buckets_4221_);
v___x_4224_ = lean_nat_dec_lt(v___y_4217_, v___x_4223_);
if (v___x_4224_ == 0)
{
lean_dec_ref(v_buckets_4221_);
v___y_4206_ = v___y_4216_;
v___y_4207_ = v___y_4219_;
v___y_4208_ = v___y_4217_;
v___y_4209_ = v___y_4218_;
v___y_4210_ = v___x_4222_;
goto v___jp_4205_;
}
else
{
size_t v___x_4225_; size_t v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = ((size_t)0ULL);
v___x_4226_ = lean_usize_of_nat(v___x_4223_);
v___x_4227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__5(v_buckets_4221_, v___x_4225_, v___x_4226_, v___x_4222_);
lean_dec_ref(v_buckets_4221_);
v___y_4206_ = v___y_4216_;
v___y_4207_ = v___y_4219_;
v___y_4208_ = v___y_4217_;
v___y_4209_ = v___y_4218_;
v___y_4210_ = v___x_4227_;
goto v___jp_4205_;
}
}
v___jp_4228_:
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg(v___y_4232_, v___y_4229_, v___y_4231_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec(v___y_4232_);
v___y_4216_ = v___y_4230_;
v___y_4217_ = v___y_4233_;
v___y_4218_ = v___y_4234_;
v___y_4219_ = v___x_4236_;
goto v___jp_4215_;
}
v___jp_4237_:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_nat_dec_le(v___y_4244_, v___y_4238_);
if (v___x_4245_ == 0)
{
lean_dec(v___y_4238_);
lean_inc(v___y_4244_);
v___y_4229_ = v___y_4239_;
v___y_4230_ = v___y_4240_;
v___y_4231_ = v___y_4244_;
v___y_4232_ = v___y_4241_;
v___y_4233_ = v___y_4242_;
v___y_4234_ = v___y_4243_;
v___y_4235_ = v___y_4244_;
goto v___jp_4228_;
}
else
{
v___y_4229_ = v___y_4239_;
v___y_4230_ = v___y_4240_;
v___y_4231_ = v___y_4244_;
v___y_4232_ = v___y_4241_;
v___y_4233_ = v___y_4242_;
v___y_4234_ = v___y_4243_;
v___y_4235_ = v___y_4238_;
goto v___jp_4228_;
}
}
v___jp_4246_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = lean_unsigned_to_nat(1u);
v___x_4251_ = lean_array_get_size(v___y_4248_);
v___x_4252_ = lean_nat_dec_eq(v___x_4251_, v___x_4249_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; uint8_t v___x_4254_; 
v___x_4253_ = lean_nat_sub(v___x_4251_, v___x_4250_);
v___x_4254_ = lean_nat_dec_le(v___x_4249_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_inc(v___x_4253_);
v___y_4238_ = v___x_4253_;
v___y_4239_ = v___y_4248_;
v___y_4240_ = v___x_4250_;
v___y_4241_ = v___x_4251_;
v___y_4242_ = v___x_4249_;
v___y_4243_ = v___y_4247_;
v___y_4244_ = v___x_4253_;
goto v___jp_4237_;
}
else
{
v___y_4238_ = v___x_4253_;
v___y_4239_ = v___y_4248_;
v___y_4240_ = v___x_4250_;
v___y_4241_ = v___x_4251_;
v___y_4242_ = v___x_4249_;
v___y_4243_ = v___y_4247_;
v___y_4244_ = v___x_4249_;
goto v___jp_4237_;
}
}
else
{
v___y_4216_ = v___x_4250_;
v___y_4217_ = v___x_4249_;
v___y_4218_ = v___y_4247_;
v___y_4219_ = v___y_4248_;
goto v___jp_4215_;
}
}
v___jp_4255_:
{
lean_object* v_size_4257_; lean_object* v_buckets_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_size_4257_ = lean_ctor_get(v_exceptions_4149_, 0);
lean_inc(v_size_4257_);
v_buckets_4258_ = lean_ctor_get(v_exceptions_4149_, 1);
lean_inc_ref(v_buckets_4258_);
lean_dec_ref(v_exceptions_4149_);
v___x_4259_ = lean_mk_empty_array_with_capacity(v_size_4257_);
lean_dec(v_size_4257_);
v___x_4260_ = lean_unsigned_to_nat(0u);
v___x_4261_ = lean_array_get_size(v_buckets_4258_);
v___x_4262_ = lean_nat_dec_lt(v___x_4260_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_dec_ref(v_buckets_4258_);
v___y_4247_ = v___y_4256_;
v___y_4248_ = v___x_4259_;
goto v___jp_4246_;
}
else
{
size_t v___x_4263_; size_t v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = ((size_t)0ULL);
v___x_4264_ = lean_usize_of_nat(v___x_4261_);
v___x_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__8(v_buckets_4258_, v___x_4263_, v___x_4264_, v___x_4259_);
lean_dec_ref(v_buckets_4258_);
v___y_4247_ = v___y_4256_;
v___y_4248_ = v___x_4265_;
goto v___jp_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___boxed(lean_object* v_root_4268_, lean_object* v_cls_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass(v_root_4268_, v_cls_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3(lean_object* v_n_4276_, lean_object* v_as_4277_, lean_object* v_lo_4278_, lean_object* v_hi_4279_, lean_object* v_w_4280_, lean_object* v_hlo_4281_, lean_object* v_hhi_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___redArg(v_n_4276_, v_as_4277_, v_lo_4278_, v_hi_4279_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3___boxed(lean_object* v_n_4284_, lean_object* v_as_4285_, lean_object* v_lo_4286_, lean_object* v_hi_4287_, lean_object* v_w_4288_, lean_object* v_hlo_4289_, lean_object* v_hhi_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3(v_n_4284_, v_as_4285_, v_lo_4286_, v_hi_4287_, v_w_4288_, v_hlo_4289_, v_hhi_4290_);
lean_dec(v_hi_4287_);
lean_dec(v_n_4284_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6(lean_object* v_n_4292_, lean_object* v_as_4293_, lean_object* v_lo_4294_, lean_object* v_hi_4295_, lean_object* v_w_4296_, lean_object* v_hlo_4297_, lean_object* v_hhi_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___redArg(v_n_4292_, v_as_4293_, v_lo_4294_, v_hi_4295_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6___boxed(lean_object* v_n_4300_, lean_object* v_as_4301_, lean_object* v_lo_4302_, lean_object* v_hi_4303_, lean_object* v_w_4304_, lean_object* v_hlo_4305_, lean_object* v_hhi_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6(v_n_4300_, v_as_4301_, v_lo_4302_, v_hi_4303_, v_w_4304_, v_hlo_4305_, v_hhi_4306_);
lean_dec(v_hi_4303_);
lean_dec(v_n_4300_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4(lean_object* v_n_4308_, lean_object* v_lo_4309_, lean_object* v_hi_4310_, lean_object* v_hhi_4311_, lean_object* v_pivot_4312_, lean_object* v_as_4313_, lean_object* v_i_4314_, lean_object* v_k_4315_, lean_object* v_ilo_4316_, lean_object* v_ik_4317_, lean_object* v_w_4318_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___redArg(v_hi_4310_, v_pivot_4312_, v_as_4313_, v_i_4314_, v_k_4315_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4___boxed(lean_object* v_n_4320_, lean_object* v_lo_4321_, lean_object* v_hi_4322_, lean_object* v_hhi_4323_, lean_object* v_pivot_4324_, lean_object* v_as_4325_, lean_object* v_i_4326_, lean_object* v_k_4327_, lean_object* v_ilo_4328_, lean_object* v_ik_4329_, lean_object* v_w_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__3_spec__4(v_n_4320_, v_lo_4321_, v_hi_4322_, v_hhi_4323_, v_pivot_4324_, v_as_4325_, v_i_4326_, v_k_4327_, v_ilo_4328_, v_ik_4329_, v_w_4330_);
lean_dec(v_pivot_4324_);
lean_dec(v_hi_4322_);
lean_dec(v_lo_4321_);
lean_dec(v_n_4320_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8(lean_object* v_n_4332_, lean_object* v_lo_4333_, lean_object* v_hi_4334_, lean_object* v_hhi_4335_, lean_object* v_pivot_4336_, lean_object* v_as_4337_, lean_object* v_i_4338_, lean_object* v_k_4339_, lean_object* v_ilo_4340_, lean_object* v_ik_4341_, lean_object* v_w_4342_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___redArg(v_hi_4334_, v_pivot_4336_, v_as_4337_, v_i_4338_, v_k_4339_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8___boxed(lean_object* v_n_4344_, lean_object* v_lo_4345_, lean_object* v_hi_4346_, lean_object* v_hhi_4347_, lean_object* v_pivot_4348_, lean_object* v_as_4349_, lean_object* v_i_4350_, lean_object* v_k_4351_, lean_object* v_ilo_4352_, lean_object* v_ik_4353_, lean_object* v_w_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__6_spec__8(v_n_4344_, v_lo_4345_, v_hi_4346_, v_hhi_4347_, v_pivot_4348_, v_as_4349_, v_i_4350_, v_k_4351_, v_ilo_4352_, v_ik_4353_, v_w_4354_);
lean_dec_ref(v_pivot_4348_);
lean_dec(v_hi_4346_);
lean_dec(v_lo_4345_);
lean_dec(v_n_4344_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__0(lean_object* v_as_4356_, size_t v_sz_4357_, size_t v_i_4358_, lean_object* v_b_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
uint8_t v___x_4365_; 
v___x_4365_ = lean_usize_dec_lt(v_i_4358_, v_sz_4357_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
v___x_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4366_, 0, v_b_4359_);
return v___x_4366_;
}
else
{
lean_object* v_a_4367_; lean_object* v_fst_4368_; lean_object* v_snd_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_a_4367_ = lean_array_uget_borrowed(v_as_4356_, v_i_4358_);
v_fst_4368_ = lean_ctor_get(v_a_4367_, 0);
v_snd_4369_ = lean_ctor_get(v_a_4367_, 1);
v___x_4370_ = lean_box(0);
lean_inc(v_snd_4369_);
lean_inc(v_fst_4368_);
v___x_4371_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass(v_fst_4368_, v_snd_4369_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4371_) == 0)
{
size_t v___x_4372_; size_t v___x_4373_; 
lean_dec_ref_known(v___x_4371_, 1);
v___x_4372_ = ((size_t)1ULL);
v___x_4373_ = lean_usize_add(v_i_4358_, v___x_4372_);
v_i_4358_ = v___x_4373_;
v_b_4359_ = v___x_4370_;
goto _start;
}
else
{
return v___x_4371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__0___boxed(lean_object* v_as_4375_, lean_object* v_sz_4376_, lean_object* v_i_4377_, lean_object* v_b_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
size_t v_sz_boxed_4384_; size_t v_i_boxed_4385_; lean_object* v_res_4386_; 
v_sz_boxed_4384_ = lean_unbox_usize(v_sz_4376_);
lean_dec(v_sz_4376_);
v_i_boxed_4385_ = lean_unbox_usize(v_i_4377_);
lean_dec(v_i_4377_);
v_res_4386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__0(v_as_4375_, v_sz_boxed_4384_, v_i_boxed_4385_, v_b_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec_ref(v_as_4375_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__2(lean_object* v_x_4387_, lean_object* v_x_4388_){
_start:
{
if (lean_obj_tag(v_x_4388_) == 0)
{
return v_x_4387_;
}
else
{
lean_object* v_key_4389_; lean_object* v_value_4390_; lean_object* v_tail_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_key_4389_ = lean_ctor_get(v_x_4388_, 0);
v_value_4390_ = lean_ctor_get(v_x_4388_, 1);
v_tail_4391_ = lean_ctor_get(v_x_4388_, 2);
lean_inc(v_value_4390_);
lean_inc(v_key_4389_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_key_4389_);
lean_ctor_set(v___x_4392_, 1, v_value_4390_);
v___x_4393_ = lean_array_push(v_x_4387_, v___x_4392_);
v_x_4387_ = v___x_4393_;
v_x_4388_ = v_tail_4391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__2___boxed(lean_object* v_x_4395_, lean_object* v_x_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__2(v_x_4395_, v_x_4396_);
lean_dec(v_x_4396_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3(lean_object* v_as_4398_, size_t v_i_4399_, size_t v_stop_4400_, lean_object* v_b_4401_){
_start:
{
uint8_t v___x_4402_; 
v___x_4402_ = lean_usize_dec_eq(v_i_4399_, v_stop_4400_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; lean_object* v___x_4404_; size_t v___x_4405_; size_t v___x_4406_; 
v___x_4403_ = lean_array_uget_borrowed(v_as_4398_, v_i_4399_);
v___x_4404_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__2(v_b_4401_, v___x_4403_);
v___x_4405_ = ((size_t)1ULL);
v___x_4406_ = lean_usize_add(v_i_4399_, v___x_4405_);
v_i_4399_ = v___x_4406_;
v_b_4401_ = v___x_4404_;
goto _start;
}
else
{
return v_b_4401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3___boxed(lean_object* v_as_4408_, lean_object* v_i_4409_, lean_object* v_stop_4410_, lean_object* v_b_4411_){
_start:
{
size_t v_i_boxed_4412_; size_t v_stop_boxed_4413_; lean_object* v_res_4414_; 
v_i_boxed_4412_ = lean_unbox_usize(v_i_4409_);
lean_dec(v_i_4409_);
v_stop_boxed_4413_ = lean_unbox_usize(v_stop_4410_);
lean_dec(v_stop_4410_);
v_res_4414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3(v_as_4408_, v_i_boxed_4412_, v_stop_boxed_4413_, v_b_4411_);
lean_dec_ref(v_as_4408_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg(lean_object* v_hi_4415_, lean_object* v_pivot_4416_, lean_object* v_as_4417_, lean_object* v_i_4418_, lean_object* v_k_4419_){
_start:
{
uint8_t v___x_4420_; 
v___x_4420_ = lean_nat_dec_lt(v_k_4419_, v_hi_4415_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
lean_dec(v_k_4419_);
v___x_4421_ = lean_array_fswap(v_as_4417_, v_i_4418_, v_hi_4415_);
v___x_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_i_4418_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
return v___x_4422_;
}
else
{
lean_object* v___x_4423_; lean_object* v_fst_4424_; lean_object* v_fst_4425_; uint8_t v___x_4426_; 
v___x_4423_ = lean_array_fget_borrowed(v_as_4417_, v_k_4419_);
v_fst_4424_ = lean_ctor_get(v___x_4423_, 0);
v_fst_4425_ = lean_ctor_get(v_pivot_4416_, 0);
v___x_4426_ = lean_nat_dec_lt(v_fst_4424_, v_fst_4425_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_unsigned_to_nat(1u);
v___x_4428_ = lean_nat_add(v_k_4419_, v___x_4427_);
lean_dec(v_k_4419_);
v_k_4419_ = v___x_4428_;
goto _start;
}
else
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4430_ = lean_array_fswap(v_as_4417_, v_i_4418_, v_k_4419_);
v___x_4431_ = lean_unsigned_to_nat(1u);
v___x_4432_ = lean_nat_add(v_i_4418_, v___x_4431_);
lean_dec(v_i_4418_);
v___x_4433_ = lean_nat_add(v_k_4419_, v___x_4431_);
lean_dec(v_k_4419_);
v_as_4417_ = v___x_4430_;
v_i_4418_ = v___x_4432_;
v_k_4419_ = v___x_4433_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg___boxed(lean_object* v_hi_4435_, lean_object* v_pivot_4436_, lean_object* v_as_4437_, lean_object* v_i_4438_, lean_object* v_k_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg(v_hi_4435_, v_pivot_4436_, v_as_4437_, v_i_4438_, v_k_4439_);
lean_dec_ref(v_pivot_4436_);
lean_dec(v_hi_4435_);
return v_res_4440_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0(lean_object* v_x1_4441_, lean_object* v_x2_4442_){
_start:
{
lean_object* v_fst_4443_; lean_object* v_fst_4444_; uint8_t v___x_4445_; 
v_fst_4443_ = lean_ctor_get(v_x1_4441_, 0);
v_fst_4444_ = lean_ctor_get(v_x2_4442_, 0);
v___x_4445_ = lean_nat_dec_lt(v_fst_4443_, v_fst_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0___boxed(lean_object* v_x1_4446_, lean_object* v_x2_4447_){
_start:
{
uint8_t v_res_4448_; lean_object* v_r_4449_; 
v_res_4448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0(v_x1_4446_, v_x2_4447_);
lean_dec_ref(v_x2_4447_);
lean_dec_ref(v_x1_4446_);
v_r_4449_ = lean_box(v_res_4448_);
return v_r_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(lean_object* v_n_4450_, lean_object* v_as_4451_, lean_object* v_lo_4452_, lean_object* v_hi_4453_){
_start:
{
lean_object* v___y_4455_; uint8_t v___x_4465_; 
v___x_4465_ = lean_nat_dec_lt(v_lo_4452_, v_hi_4453_);
if (v___x_4465_ == 0)
{
lean_dec(v_lo_4452_);
return v_as_4451_;
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v_mid_4468_; lean_object* v___y_4470_; lean_object* v___y_4476_; lean_object* v___x_4481_; lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4466_ = lean_nat_add(v_lo_4452_, v_hi_4453_);
v___x_4467_ = lean_unsigned_to_nat(1u);
v_mid_4468_ = lean_nat_shiftr(v___x_4466_, v___x_4467_);
lean_dec(v___x_4466_);
v___x_4481_ = lean_array_fget_borrowed(v_as_4451_, v_mid_4468_);
v___x_4482_ = lean_array_fget_borrowed(v_as_4451_, v_lo_4452_);
v___x_4483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0(v___x_4481_, v___x_4482_);
if (v___x_4483_ == 0)
{
v___y_4476_ = v_as_4451_;
goto v___jp_4475_;
}
else
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_array_fswap(v_as_4451_, v_lo_4452_, v_mid_4468_);
v___y_4476_ = v___x_4484_;
goto v___jp_4475_;
}
v___jp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; uint8_t v___x_4473_; 
v___x_4471_ = lean_array_fget_borrowed(v___y_4470_, v_mid_4468_);
v___x_4472_ = lean_array_fget_borrowed(v___y_4470_, v_hi_4453_);
v___x_4473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0(v___x_4471_, v___x_4472_);
if (v___x_4473_ == 0)
{
lean_dec(v_mid_4468_);
v___y_4455_ = v___y_4470_;
goto v___jp_4454_;
}
else
{
lean_object* v___x_4474_; 
v___x_4474_ = lean_array_fswap(v___y_4470_, v_mid_4468_, v_hi_4453_);
lean_dec(v_mid_4468_);
v___y_4455_ = v___x_4474_;
goto v___jp_4454_;
}
}
v___jp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4477_ = lean_array_fget_borrowed(v___y_4476_, v_hi_4453_);
v___x_4478_ = lean_array_fget_borrowed(v___y_4476_, v_lo_4452_);
v___x_4479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___lam__0(v___x_4477_, v___x_4478_);
if (v___x_4479_ == 0)
{
v___y_4470_ = v___y_4476_;
goto v___jp_4469_;
}
else
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_array_fswap(v___y_4476_, v_lo_4452_, v_hi_4453_);
v___y_4470_ = v___x_4480_;
goto v___jp_4469_;
}
}
}
v___jp_4454_:
{
lean_object* v_pivot_4456_; lean_object* v___x_4457_; lean_object* v_fst_4458_; lean_object* v_snd_4459_; uint8_t v___x_4460_; 
v_pivot_4456_ = lean_array_fget(v___y_4455_, v_hi_4453_);
lean_inc_n(v_lo_4452_, 2);
v___x_4457_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg(v_hi_4453_, v_pivot_4456_, v___y_4455_, v_lo_4452_, v_lo_4452_);
lean_dec(v_pivot_4456_);
v_fst_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_fst_4458_);
v_snd_4459_ = lean_ctor_get(v___x_4457_, 1);
lean_inc(v_snd_4459_);
lean_dec_ref(v___x_4457_);
v___x_4460_ = lean_nat_dec_le(v_hi_4453_, v_fst_4458_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(v_n_4450_, v_snd_4459_, v_lo_4452_, v_fst_4458_);
v___x_4462_ = lean_unsigned_to_nat(1u);
v___x_4463_ = lean_nat_add(v_fst_4458_, v___x_4462_);
lean_dec(v_fst_4458_);
v_as_4451_ = v___x_4461_;
v_lo_4452_ = v___x_4463_;
goto _start;
}
else
{
lean_dec(v_fst_4458_);
lean_dec(v_lo_4452_);
return v_snd_4459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg___boxed(lean_object* v_n_4485_, lean_object* v_as_4486_, lean_object* v_lo_4487_, lean_object* v_hi_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(v_n_4485_, v_as_4486_, v_lo_4487_, v_hi_4488_);
lean_dec(v_hi_4488_);
lean_dec(v_n_4485_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses(lean_object* v_sets_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v___y_4497_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4523_; lean_object* v_classes_4530_; lean_object* v_size_4531_; lean_object* v_buckets_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; 
v_classes_4530_ = lean_ctor_get(v_sets_4490_, 0);
v_size_4531_ = lean_ctor_get(v_classes_4530_, 0);
v_buckets_4532_ = lean_ctor_get(v_classes_4530_, 1);
v___x_4533_ = lean_mk_empty_array_with_capacity(v_size_4531_);
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = lean_array_get_size(v_buckets_4532_);
v___x_4536_ = lean_nat_dec_lt(v___x_4534_, v___x_4535_);
if (v___x_4536_ == 0)
{
v___y_4523_ = v___x_4533_;
goto v___jp_4522_;
}
else
{
size_t v___x_4537_; size_t v___x_4538_; lean_object* v___x_4539_; 
v___x_4537_ = ((size_t)0ULL);
v___x_4538_ = lean_usize_of_nat(v___x_4535_);
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3(v_buckets_4532_, v___x_4537_, v___x_4538_, v___x_4533_);
v___y_4523_ = v___x_4539_;
goto v___jp_4522_;
}
v___jp_4496_:
{
lean_object* v___x_4498_; size_t v_sz_4499_; size_t v___x_4500_; lean_object* v___x_4501_; 
v___x_4498_ = lean_box(0);
v_sz_4499_ = lean_array_size(v___y_4497_);
v___x_4500_ = ((size_t)0ULL);
v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__0(v___y_4497_, v_sz_4499_, v___x_4500_, v___x_4498_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
lean_dec_ref(v___y_4497_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v___x_4501_, 0);
lean_dec(v_unused_4509_);
v___x_4503_ = v___x_4501_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_dec(v___x_4501_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4498_);
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4498_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
else
{
return v___x_4501_;
}
}
v___jp_4510_:
{
lean_object* v___x_4515_; 
v___x_4515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(v___y_4512_, v___y_4511_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec(v___y_4512_);
v___y_4497_ = v___x_4515_;
goto v___jp_4496_;
}
v___jp_4516_:
{
uint8_t v___x_4521_; 
v___x_4521_ = lean_nat_dec_le(v___y_4520_, v___y_4519_);
if (v___x_4521_ == 0)
{
lean_dec(v___y_4519_);
lean_inc(v___y_4520_);
v___y_4511_ = v___y_4517_;
v___y_4512_ = v___y_4518_;
v___y_4513_ = v___y_4520_;
v___y_4514_ = v___y_4520_;
goto v___jp_4510_;
}
else
{
v___y_4511_ = v___y_4517_;
v___y_4512_ = v___y_4518_;
v___y_4513_ = v___y_4520_;
v___y_4514_ = v___y_4519_;
goto v___jp_4510_;
}
}
v___jp_4522_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4524_ = lean_array_get_size(v___y_4523_);
v___x_4525_ = lean_unsigned_to_nat(0u);
v___x_4526_ = lean_nat_dec_eq(v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4527_ = lean_unsigned_to_nat(1u);
v___x_4528_ = lean_nat_sub(v___x_4524_, v___x_4527_);
v___x_4529_ = lean_nat_dec_le(v___x_4525_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_inc(v___x_4528_);
v___y_4517_ = v___y_4523_;
v___y_4518_ = v___x_4524_;
v___y_4519_ = v___x_4528_;
v___y_4520_ = v___x_4528_;
goto v___jp_4516_;
}
else
{
v___y_4517_ = v___y_4523_;
v___y_4518_ = v___x_4524_;
v___y_4519_ = v___x_4528_;
v___y_4520_ = v___x_4525_;
goto v___jp_4516_;
}
}
else
{
v___y_4497_ = v___y_4523_;
goto v___jp_4496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses___boxed(lean_object* v_sets_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses(v_sets_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec_ref(v_sets_4540_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1(lean_object* v_n_4547_, lean_object* v_as_4548_, lean_object* v_lo_4549_, lean_object* v_hi_4550_, lean_object* v_w_4551_, lean_object* v_hlo_4552_, lean_object* v_hhi_4553_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(v_n_4547_, v_as_4548_, v_lo_4549_, v_hi_4550_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___boxed(lean_object* v_n_4555_, lean_object* v_as_4556_, lean_object* v_lo_4557_, lean_object* v_hi_4558_, lean_object* v_w_4559_, lean_object* v_hlo_4560_, lean_object* v_hhi_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1(v_n_4555_, v_as_4556_, v_lo_4557_, v_hi_4558_, v_w_4559_, v_hlo_4560_, v_hhi_4561_);
lean_dec(v_hi_4558_);
lean_dec(v_n_4555_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1(lean_object* v_n_4563_, lean_object* v_lo_4564_, lean_object* v_hi_4565_, lean_object* v_hhi_4566_, lean_object* v_pivot_4567_, lean_object* v_as_4568_, lean_object* v_i_4569_, lean_object* v_k_4570_, lean_object* v_ilo_4571_, lean_object* v_ik_4572_, lean_object* v_w_4573_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___redArg(v_hi_4565_, v_pivot_4567_, v_as_4568_, v_i_4569_, v_k_4570_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1___boxed(lean_object* v_n_4575_, lean_object* v_lo_4576_, lean_object* v_hi_4577_, lean_object* v_hhi_4578_, lean_object* v_pivot_4579_, lean_object* v_as_4580_, lean_object* v_i_4581_, lean_object* v_k_4582_, lean_object* v_ilo_4583_, lean_object* v_ik_4584_, lean_object* v_w_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1_spec__1(v_n_4575_, v_lo_4576_, v_hi_4577_, v_hhi_4578_, v_pivot_4579_, v_as_4580_, v_i_4581_, v_k_4582_, v_ilo_4583_, v_ik_4584_, v_w_4585_);
lean_dec_ref(v_pivot_4579_);
lean_dec(v_hi_4577_);
lean_dec(v_lo_4576_);
lean_dec(v_n_4575_);
return v_res_4586_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = lean_unsigned_to_nat(32u);
v___x_4588_ = lean_mk_empty_array_with_capacity(v___x_4587_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4590_ = ((size_t)5ULL);
v___x_4591_ = lean_unsigned_to_nat(0u);
v___x_4592_ = lean_unsigned_to_nat(32u);
v___x_4593_ = lean_mk_empty_array_with_capacity(v___x_4592_);
v___x_4594_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__0);
v___x_4595_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
lean_ctor_set(v___x_4595_, 1, v___x_4593_);
lean_ctor_set(v___x_4595_, 2, v___x_4591_);
lean_ctor_set(v___x_4595_, 3, v___x_4591_);
lean_ctor_set_usize(v___x_4595_, 4, v___x_4590_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg(lean_object* v___y_4596_){
_start:
{
lean_object* v___x_4598_; lean_object* v_traceState_4599_; lean_object* v_traces_4600_; lean_object* v___x_4601_; lean_object* v_traceState_4602_; lean_object* v_env_4603_; lean_object* v_nextMacroScope_4604_; lean_object* v_ngen_4605_; lean_object* v_auxDeclNGen_4606_; lean_object* v_cache_4607_; lean_object* v_recordedDeps_4608_; lean_object* v_messages_4609_; lean_object* v_infoState_4610_; lean_object* v_snapshotTasks_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4630_; 
v___x_4598_ = lean_st_ref_get(v___y_4596_);
v_traceState_4599_ = lean_ctor_get(v___x_4598_, 4);
lean_inc_ref(v_traceState_4599_);
lean_dec(v___x_4598_);
v_traces_4600_ = lean_ctor_get(v_traceState_4599_, 0);
lean_inc_ref(v_traces_4600_);
lean_dec_ref(v_traceState_4599_);
v___x_4601_ = lean_st_ref_take(v___y_4596_);
v_traceState_4602_ = lean_ctor_get(v___x_4601_, 4);
v_env_4603_ = lean_ctor_get(v___x_4601_, 0);
v_nextMacroScope_4604_ = lean_ctor_get(v___x_4601_, 1);
v_ngen_4605_ = lean_ctor_get(v___x_4601_, 2);
v_auxDeclNGen_4606_ = lean_ctor_get(v___x_4601_, 3);
v_cache_4607_ = lean_ctor_get(v___x_4601_, 5);
v_recordedDeps_4608_ = lean_ctor_get(v___x_4601_, 6);
v_messages_4609_ = lean_ctor_get(v___x_4601_, 7);
v_infoState_4610_ = lean_ctor_get(v___x_4601_, 8);
v_snapshotTasks_4611_ = lean_ctor_get(v___x_4601_, 9);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4613_ = v___x_4601_;
v_isShared_4614_ = v_isSharedCheck_4630_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_snapshotTasks_4611_);
lean_inc(v_infoState_4610_);
lean_inc(v_messages_4609_);
lean_inc(v_recordedDeps_4608_);
lean_inc(v_cache_4607_);
lean_inc(v_traceState_4602_);
lean_inc(v_auxDeclNGen_4606_);
lean_inc(v_ngen_4605_);
lean_inc(v_nextMacroScope_4604_);
lean_inc(v_env_4603_);
lean_dec(v___x_4601_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4630_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint64_t v_tid_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4628_; 
v_tid_4615_ = lean_ctor_get_uint64(v_traceState_4602_, sizeof(void*)*1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_traceState_4602_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v_traceState_4602_, 0);
lean_dec(v_unused_4629_);
v___x_4617_ = v_traceState_4602_;
v_isShared_4618_ = v_isSharedCheck_4628_;
goto v_resetjp_4616_;
}
else
{
lean_dec(v_traceState_4602_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4628_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4619_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___closed__1);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4621_ = v___x_4617_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4619_);
lean_ctor_set_uint64(v_reuseFailAlloc_4627_, sizeof(void*)*1, v_tid_4615_);
v___x_4621_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4623_; 
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 4, v___x_4621_);
v___x_4623_ = v___x_4613_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_env_4603_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v_nextMacroScope_4604_);
lean_ctor_set(v_reuseFailAlloc_4626_, 2, v_ngen_4605_);
lean_ctor_set(v_reuseFailAlloc_4626_, 3, v_auxDeclNGen_4606_);
lean_ctor_set(v_reuseFailAlloc_4626_, 4, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4626_, 5, v_cache_4607_);
lean_ctor_set(v_reuseFailAlloc_4626_, 6, v_recordedDeps_4608_);
lean_ctor_set(v_reuseFailAlloc_4626_, 7, v_messages_4609_);
lean_ctor_set(v_reuseFailAlloc_4626_, 8, v_infoState_4610_);
lean_ctor_set(v_reuseFailAlloc_4626_, 9, v_snapshotTasks_4611_);
v___x_4623_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = lean_st_ref_put(v___y_4596_, v___x_4623_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_traces_4600_);
return v___x_4625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg___boxed(lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg(v___y_4631_);
lean_dec(v___y_4631_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6(lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg(v___y_4637_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___boxed(lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6(v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
return v_res_4645_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(lean_object* v_opts_4646_, lean_object* v_opt_4647_){
_start:
{
lean_object* v_name_4648_; lean_object* v_defValue_4649_; lean_object* v_map_4650_; lean_object* v___x_4651_; 
v_name_4648_ = lean_ctor_get(v_opt_4647_, 0);
v_defValue_4649_ = lean_ctor_get(v_opt_4647_, 1);
v_map_4650_ = lean_ctor_get(v_opts_4646_, 0);
v___x_4651_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4650_, v_name_4648_);
if (lean_obj_tag(v___x_4651_) == 0)
{
uint8_t v___x_4652_; 
v___x_4652_ = lean_unbox(v_defValue_4649_);
return v___x_4652_;
}
else
{
lean_object* v_val_4653_; 
v_val_4653_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_val_4653_);
lean_dec_ref_known(v___x_4651_, 1);
if (lean_obj_tag(v_val_4653_) == 1)
{
uint8_t v_v_4654_; 
v_v_4654_ = lean_ctor_get_uint8(v_val_4653_, 0);
lean_dec_ref_known(v_val_4653_, 0);
return v_v_4654_;
}
else
{
uint8_t v___x_4655_; 
lean_dec(v_val_4653_);
v___x_4655_ = lean_unbox(v_defValue_4649_);
return v___x_4655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7___boxed(lean_object* v_opts_4656_, lean_object* v_opt_4657_){
_start:
{
uint8_t v_res_4658_; lean_object* v_r_4659_; 
v_res_4658_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(v_opts_4656_, v_opt_4657_);
lean_dec_ref(v_opt_4657_);
lean_dec_ref(v_opts_4656_);
v_r_4659_ = lean_box(v_res_4658_);
return v_r_4659_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__0));
v___x_4662_ = l_Lean_stringToMessageData(v___x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0(lean_object* v_x_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___closed__1);
v___x_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4669_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0___boxed(lean_object* v_x_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___lam__0(v_x_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec_ref(v_x_4671_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__2(lean_object* v_x_4678_, lean_object* v_x_4679_){
_start:
{
if (lean_obj_tag(v_x_4679_) == 0)
{
return v_x_4678_;
}
else
{
lean_object* v_key_4680_; lean_object* v_value_4681_; lean_object* v_tail_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v_key_4680_ = lean_ctor_get(v_x_4679_, 0);
v_value_4681_ = lean_ctor_get(v_x_4679_, 1);
v_tail_4682_ = lean_ctor_get(v_x_4679_, 2);
lean_inc(v_value_4681_);
lean_inc(v_key_4680_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v_key_4680_);
lean_ctor_set(v___x_4683_, 1, v_value_4681_);
v___x_4684_ = lean_array_push(v_x_4678_, v___x_4683_);
v_x_4678_ = v___x_4684_;
v_x_4679_ = v_tail_4682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__2___boxed(lean_object* v_x_4686_, lean_object* v_x_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__2(v_x_4686_, v_x_4687_);
lean_dec(v_x_4687_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3(lean_object* v_as_4689_, size_t v_i_4690_, size_t v_stop_4691_, lean_object* v_b_4692_){
_start:
{
uint8_t v___x_4693_; 
v___x_4693_ = lean_usize_dec_eq(v_i_4690_, v_stop_4691_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; size_t v___x_4696_; size_t v___x_4697_; 
v___x_4694_ = lean_array_uget_borrowed(v_as_4689_, v_i_4690_);
v___x_4695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__2(v_b_4692_, v___x_4694_);
v___x_4696_ = ((size_t)1ULL);
v___x_4697_ = lean_usize_add(v_i_4690_, v___x_4696_);
v_i_4690_ = v___x_4697_;
v_b_4692_ = v___x_4695_;
goto _start;
}
else
{
return v_b_4692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3___boxed(lean_object* v_as_4699_, lean_object* v_i_4700_, lean_object* v_stop_4701_, lean_object* v_b_4702_){
_start:
{
size_t v_i_boxed_4703_; size_t v_stop_boxed_4704_; lean_object* v_res_4705_; 
v_i_boxed_4703_ = lean_unbox_usize(v_i_4700_);
lean_dec(v_i_4700_);
v_stop_boxed_4704_ = lean_unbox_usize(v_stop_4701_);
lean_dec(v_stop_4701_);
v_res_4705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3(v_as_4699_, v_i_boxed_4703_, v_stop_boxed_4704_, v_b_4702_);
lean_dec_ref(v_as_4699_);
return v_res_4705_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__0));
v___x_4708_ = l_Lean_stringToMessageData(v___x_4707_);
return v___x_4708_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__2));
v___x_4711_ = l_Lean_stringToMessageData(v___x_4710_);
return v___x_4711_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5(void){
_start:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__4));
v___x_4714_ = l_Lean_stringToMessageData(v___x_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0(lean_object* v_as_4715_, size_t v_sz_4716_, size_t v_i_4717_, lean_object* v_b_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v_a_4725_; uint8_t v___x_4729_; 
v___x_4729_ = lean_usize_dec_lt(v_i_4717_, v_sz_4716_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4730_, 0, v_b_4718_);
return v___x_4730_;
}
else
{
lean_object* v_a_4731_; lean_object* v_fst_4732_; lean_object* v_toCold_4733_; lean_object* v_options_4734_; lean_object* v_snd_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4771_; 
v_a_4731_ = lean_array_uget(v_as_4715_, v_i_4717_);
v_fst_4732_ = lean_ctor_get(v_a_4731_, 0);
lean_inc(v_fst_4732_);
v_toCold_4733_ = lean_ctor_get(v___y_4721_, 0);
v_options_4734_ = lean_ctor_get(v_toCold_4733_, 2);
v_snd_4735_ = lean_ctor_get(v_a_4731_, 1);
v_isSharedCheck_4771_ = !lean_is_exclusive(v_a_4731_);
if (v_isSharedCheck_4771_ == 0)
{
lean_object* v_unused_4772_; 
v_unused_4772_ = lean_ctor_get(v_a_4731_, 0);
lean_dec(v_unused_4772_);
v___x_4737_ = v_a_4731_;
v_isShared_4738_ = v_isSharedCheck_4771_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_snd_4735_);
lean_dec(v_a_4731_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4771_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v_fst_4739_; lean_object* v_snd_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4770_; 
v_fst_4739_ = lean_ctor_get(v_fst_4732_, 0);
v_snd_4740_ = lean_ctor_get(v_fst_4732_, 1);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_fst_4732_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4742_ = v_fst_4732_;
v_isShared_4743_ = v_isSharedCheck_4770_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_snd_4740_);
lean_inc(v_fst_4739_);
lean_dec(v_fst_4732_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4770_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_inheritedTraceOptions_4744_; uint8_t v_hasTrace_4745_; lean_object* v___x_4746_; 
v_inheritedTraceOptions_4744_ = lean_ctor_get(v_toCold_4733_, 11);
v_hasTrace_4745_ = lean_ctor_get_uint8(v_options_4734_, sizeof(void*)*1);
v___x_4746_ = lean_box(0);
if (v_hasTrace_4745_ == 0)
{
lean_del_object(v___x_4742_);
lean_dec(v_snd_4740_);
lean_dec(v_fst_4739_);
lean_del_object(v___x_4737_);
lean_dec(v_snd_4735_);
v_a_4725_ = v___x_4746_;
goto v___jp_4724_;
}
else
{
lean_object* v_cls_4747_; lean_object* v___x_4748_; uint8_t v___x_4749_; 
v_cls_4747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_4748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7);
v___x_4749_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4744_, v_options_4734_, v___x_4748_);
if (v___x_4749_ == 0)
{
lean_del_object(v___x_4742_);
lean_dec(v_snd_4740_);
lean_dec(v_fst_4739_);
lean_del_object(v___x_4737_);
lean_dec(v_snd_4735_);
v_a_4725_ = v___x_4746_;
goto v___jp_4724_;
}
else
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
v___x_4750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__1);
v___x_4751_ = l_Lean_MessageData_ofExpr(v_fst_4739_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set_tag(v___x_4742_, 7);
lean_ctor_set(v___x_4742_, 1, v___x_4751_);
lean_ctor_set(v___x_4742_, 0, v___x_4750_);
v___x_4753_ = v___x_4742_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v___x_4751_);
v___x_4753_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__3);
if (v_isShared_4738_ == 0)
{
lean_ctor_set_tag(v___x_4737_, 7);
lean_ctor_set(v___x_4737_, 1, v___x_4754_);
lean_ctor_set(v___x_4737_, 0, v___x_4753_);
v___x_4756_ = v___x_4737_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4753_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4757_ = l_Nat_reprFast(v_snd_4740_);
v___x_4758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
v___x_4759_ = l_Lean_MessageData_ofFormat(v___x_4758_);
v___x_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4756_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
v___x_4761_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5);
v___x_4762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4760_);
lean_ctor_set(v___x_4762_, 1, v___x_4761_);
v___x_4763_ = l_Nat_reprFast(v_snd_4735_);
v___x_4764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
v___x_4765_ = l_Lean_MessageData_ofFormat(v___x_4764_);
v___x_4766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4762_);
lean_ctor_set(v___x_4766_, 1, v___x_4765_);
v___x_4767_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(v_cls_4747_, v___x_4766_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
if (lean_obj_tag(v___x_4767_) == 0)
{
lean_dec_ref_known(v___x_4767_, 1);
v_a_4725_ = v___x_4746_;
goto v___jp_4724_;
}
else
{
return v___x_4767_;
}
}
}
}
}
}
}
}
v___jp_4724_:
{
size_t v___x_4726_; size_t v___x_4727_; 
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4717_, v___x_4726_);
v_i_4717_ = v___x_4727_;
v_b_4718_ = v_a_4725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___boxed(lean_object* v_as_4773_, lean_object* v_sz_4774_, lean_object* v_i_4775_, lean_object* v_b_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
size_t v_sz_boxed_4782_; size_t v_i_boxed_4783_; lean_object* v_res_4784_; 
v_sz_boxed_4782_ = lean_unbox_usize(v_sz_4774_);
lean_dec(v_sz_4774_);
v_i_boxed_4783_ = lean_unbox_usize(v_i_4775_);
lean_dec(v_i_4775_);
v_res_4784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0(v_as_4773_, v_sz_boxed_4782_, v_i_boxed_4783_, v_b_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec_ref(v_as_4773_);
return v_res_4784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__11(lean_object* v_e_4785_){
_start:
{
if (lean_obj_tag(v_e_4785_) == 0)
{
uint8_t v___x_4786_; 
v___x_4786_ = 2;
return v___x_4786_;
}
else
{
uint8_t v___x_4787_; 
v___x_4787_ = 0;
return v___x_4787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__11___boxed(lean_object* v_e_4788_){
_start:
{
uint8_t v_res_4789_; lean_object* v_r_4790_; 
v_res_4789_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__11(v_e_4788_);
lean_dec_ref(v_e_4788_);
v_r_4790_ = lean_box(v_res_4789_);
return v_r_4790_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg(lean_object* v_x_4791_){
_start:
{
if (lean_obj_tag(v_x_4791_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
v_a_4793_ = lean_ctor_get(v_x_4791_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_x_4791_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v_x_4791_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v_x_4791_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
lean_ctor_set_tag(v___x_4795_, 1);
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
v_a_4801_ = lean_ctor_get(v_x_4791_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_x_4791_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v_x_4791_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v_x_4791_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 0);
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg___boxed(lean_object* v_x_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg(v_x_4809_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12(lean_object* v_opts_4812_, lean_object* v_opt_4813_){
_start:
{
lean_object* v_name_4814_; lean_object* v_defValue_4815_; lean_object* v_map_4816_; lean_object* v___x_4817_; 
v_name_4814_ = lean_ctor_get(v_opt_4813_, 0);
v_defValue_4815_ = lean_ctor_get(v_opt_4813_, 1);
v_map_4816_ = lean_ctor_get(v_opts_4812_, 0);
v___x_4817_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4816_, v_name_4814_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_inc(v_defValue_4815_);
return v_defValue_4815_;
}
else
{
lean_object* v_val_4818_; 
v_val_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_val_4818_);
lean_dec_ref_known(v___x_4817_, 1);
if (lean_obj_tag(v_val_4818_) == 3)
{
lean_object* v_v_4819_; 
v_v_4819_ = lean_ctor_get(v_val_4818_, 0);
lean_inc(v_v_4819_);
lean_dec_ref_known(v_val_4818_, 1);
return v_v_4819_;
}
else
{
lean_dec(v_val_4818_);
lean_inc(v_defValue_4815_);
return v_defValue_4815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12___boxed(lean_object* v_opts_4820_, lean_object* v_opt_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12(v_opts_4820_, v_opt_4821_);
lean_dec_ref(v_opt_4821_);
lean_dec_ref(v_opts_4820_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9_spec__10(size_t v_sz_4823_, size_t v_i_4824_, lean_object* v_bs_4825_){
_start:
{
uint8_t v___x_4826_; 
v___x_4826_ = lean_usize_dec_lt(v_i_4824_, v_sz_4823_);
if (v___x_4826_ == 0)
{
return v_bs_4825_;
}
else
{
lean_object* v_v_4827_; lean_object* v_msg_4828_; lean_object* v___x_4829_; lean_object* v_bs_x27_4830_; size_t v___x_4831_; size_t v___x_4832_; lean_object* v___x_4833_; 
v_v_4827_ = lean_array_uget_borrowed(v_bs_4825_, v_i_4824_);
v_msg_4828_ = lean_ctor_get(v_v_4827_, 1);
lean_inc_ref(v_msg_4828_);
v___x_4829_ = lean_unsigned_to_nat(0u);
v_bs_x27_4830_ = lean_array_uset(v_bs_4825_, v_i_4824_, v___x_4829_);
v___x_4831_ = ((size_t)1ULL);
v___x_4832_ = lean_usize_add(v_i_4824_, v___x_4831_);
v___x_4833_ = lean_array_uset(v_bs_x27_4830_, v_i_4824_, v_msg_4828_);
v_i_4824_ = v___x_4832_;
v_bs_4825_ = v___x_4833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9_spec__10___boxed(lean_object* v_sz_4835_, lean_object* v_i_4836_, lean_object* v_bs_4837_){
_start:
{
size_t v_sz_boxed_4838_; size_t v_i_boxed_4839_; lean_object* v_res_4840_; 
v_sz_boxed_4838_ = lean_unbox_usize(v_sz_4835_);
lean_dec(v_sz_4835_);
v_i_boxed_4839_ = lean_unbox_usize(v_i_4836_);
lean_dec(v_i_4836_);
v_res_4840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9_spec__10(v_sz_boxed_4838_, v_i_boxed_4839_, v_bs_4837_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9(lean_object* v_oldTraces_4841_, lean_object* v_data_4842_, lean_object* v_ref_4843_, lean_object* v_msg_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_toCold_4850_; lean_object* v_currRecDepth_4851_; lean_object* v_ref_4852_; uint16_t v_optionFlags_4853_; uint8_t v_suppressElabErrors_4854_; uint8_t v_checkDeprecated_4855_; uint8_t v_isRecordingDeps_4856_; lean_object* v_ref_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v_traceState_4860_; lean_object* v_traces_4861_; lean_object* v___x_4862_; size_t v_sz_4863_; size_t v___x_4864_; lean_object* v___x_4865_; lean_object* v_msg_4866_; lean_object* v___x_4867_; lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4906_; 
v_toCold_4850_ = lean_ctor_get(v___y_4847_, 0);
v_currRecDepth_4851_ = lean_ctor_get(v___y_4847_, 1);
v_ref_4852_ = lean_ctor_get(v___y_4847_, 2);
v_optionFlags_4853_ = lean_ctor_get_uint16(v___y_4847_, sizeof(void*)*3);
v_suppressElabErrors_4854_ = lean_ctor_get_uint8(v___y_4847_, sizeof(void*)*3 + 2);
v_checkDeprecated_4855_ = lean_ctor_get_uint8(v___y_4847_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4856_ = lean_ctor_get_uint8(v___y_4847_, sizeof(void*)*3 + 4);
v_ref_4857_ = l_Lean_replaceRef(v_ref_4843_, v_ref_4852_);
lean_inc(v_currRecDepth_4851_);
lean_inc_ref(v_toCold_4850_);
v___x_4858_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4858_, 0, v_toCold_4850_);
lean_ctor_set(v___x_4858_, 1, v_currRecDepth_4851_);
lean_ctor_set(v___x_4858_, 2, v_ref_4857_);
lean_ctor_set_uint16(v___x_4858_, sizeof(void*)*3, v_optionFlags_4853_);
lean_ctor_set_uint8(v___x_4858_, sizeof(void*)*3 + 2, v_suppressElabErrors_4854_);
lean_ctor_set_uint8(v___x_4858_, sizeof(void*)*3 + 3, v_checkDeprecated_4855_);
lean_ctor_set_uint8(v___x_4858_, sizeof(void*)*3 + 4, v_isRecordingDeps_4856_);
v___x_4859_ = lean_st_ref_get(v___y_4848_);
v_traceState_4860_ = lean_ctor_get(v___x_4859_, 4);
lean_inc_ref(v_traceState_4860_);
lean_dec(v___x_4859_);
v_traces_4861_ = lean_ctor_get(v_traceState_4860_, 0);
lean_inc_ref(v_traces_4861_);
lean_dec_ref(v_traceState_4860_);
v___x_4862_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4861_);
lean_dec_ref(v_traces_4861_);
v_sz_4863_ = lean_array_size(v___x_4862_);
v___x_4864_ = ((size_t)0ULL);
v___x_4865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9_spec__10(v_sz_4863_, v___x_4864_, v___x_4862_);
v_msg_4866_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4866_, 0, v_data_4842_);
lean_ctor_set(v_msg_4866_, 1, v_msg_4844_);
lean_ctor_set(v_msg_4866_, 2, v___x_4865_);
v___x_4867_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2_spec__2(v_msg_4866_, v___y_4845_, v___y_4846_, v___x_4858_, v___y_4848_);
lean_dec_ref_known(v___x_4858_, 3);
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4906_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4906_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v_traceState_4873_; lean_object* v_env_4874_; lean_object* v_nextMacroScope_4875_; lean_object* v_ngen_4876_; lean_object* v_auxDeclNGen_4877_; lean_object* v_cache_4878_; lean_object* v_recordedDeps_4879_; lean_object* v_messages_4880_; lean_object* v_infoState_4881_; lean_object* v_snapshotTasks_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4905_; 
v___x_4872_ = lean_st_ref_take(v___y_4848_);
v_traceState_4873_ = lean_ctor_get(v___x_4872_, 4);
v_env_4874_ = lean_ctor_get(v___x_4872_, 0);
v_nextMacroScope_4875_ = lean_ctor_get(v___x_4872_, 1);
v_ngen_4876_ = lean_ctor_get(v___x_4872_, 2);
v_auxDeclNGen_4877_ = lean_ctor_get(v___x_4872_, 3);
v_cache_4878_ = lean_ctor_get(v___x_4872_, 5);
v_recordedDeps_4879_ = lean_ctor_get(v___x_4872_, 6);
v_messages_4880_ = lean_ctor_get(v___x_4872_, 7);
v_infoState_4881_ = lean_ctor_get(v___x_4872_, 8);
v_snapshotTasks_4882_ = lean_ctor_get(v___x_4872_, 9);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4884_ = v___x_4872_;
v_isShared_4885_ = v_isSharedCheck_4905_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_snapshotTasks_4882_);
lean_inc(v_infoState_4881_);
lean_inc(v_messages_4880_);
lean_inc(v_recordedDeps_4879_);
lean_inc(v_cache_4878_);
lean_inc(v_traceState_4873_);
lean_inc(v_auxDeclNGen_4877_);
lean_inc(v_ngen_4876_);
lean_inc(v_nextMacroScope_4875_);
lean_inc(v_env_4874_);
lean_dec(v___x_4872_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4905_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
uint64_t v_tid_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4903_; 
v_tid_4886_ = lean_ctor_get_uint64(v_traceState_4873_, sizeof(void*)*1);
v_isSharedCheck_4903_ = !lean_is_exclusive(v_traceState_4873_);
if (v_isSharedCheck_4903_ == 0)
{
lean_object* v_unused_4904_; 
v_unused_4904_ = lean_ctor_get(v_traceState_4873_, 0);
lean_dec(v_unused_4904_);
v___x_4888_ = v_traceState_4873_;
v_isShared_4889_ = v_isSharedCheck_4903_;
goto v_resetjp_4887_;
}
else
{
lean_dec(v_traceState_4873_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4903_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4894_; 
v___x_4890_ = lean_box(0);
v___x_4891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4891_, 0, v_ref_4843_);
lean_ctor_set(v___x_4891_, 1, v_a_4868_);
v___x_4892_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4841_, v___x_4891_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v___x_4892_);
v___x_4894_ = v___x_4888_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4892_);
lean_ctor_set_uint64(v_reuseFailAlloc_4902_, sizeof(void*)*1, v_tid_4886_);
v___x_4894_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
lean_object* v___x_4896_; 
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 4, v___x_4894_);
v___x_4896_ = v___x_4884_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_env_4874_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_nextMacroScope_4875_);
lean_ctor_set(v_reuseFailAlloc_4901_, 2, v_ngen_4876_);
lean_ctor_set(v_reuseFailAlloc_4901_, 3, v_auxDeclNGen_4877_);
lean_ctor_set(v_reuseFailAlloc_4901_, 4, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4901_, 5, v_cache_4878_);
lean_ctor_set(v_reuseFailAlloc_4901_, 6, v_recordedDeps_4879_);
lean_ctor_set(v_reuseFailAlloc_4901_, 7, v_messages_4880_);
lean_ctor_set(v_reuseFailAlloc_4901_, 8, v_infoState_4881_);
lean_ctor_set(v_reuseFailAlloc_4901_, 9, v_snapshotTasks_4882_);
v___x_4896_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
lean_object* v___x_4897_; lean_object* v___x_4899_; 
v___x_4897_ = lean_st_ref_put(v___y_4848_, v___x_4896_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4890_);
v___x_4899_ = v___x_4870_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4890_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9___boxed(lean_object* v_oldTraces_4907_, lean_object* v_data_4908_, lean_object* v_ref_4909_, lean_object* v_msg_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9(v_oldTraces_4907_, v_data_4908_, v_ref_4909_, v_msg_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
return v_res_4916_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__0));
v___x_4919_ = l_Lean_stringToMessageData(v___x_4918_);
return v___x_4919_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__2(void){
_start:
{
lean_object* v___x_4920_; double v___x_4921_; 
v___x_4920_ = lean_unsigned_to_nat(1000u);
v___x_4921_ = lean_float_of_nat(v___x_4920_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(lean_object* v_cls_4922_, uint8_t v_collapsed_4923_, lean_object* v_tag_4924_, lean_object* v_opts_4925_, uint8_t v_clsEnabled_4926_, lean_object* v_oldTraces_4927_, lean_object* v_msg_4928_, lean_object* v_resStartStop_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v_fst_4935_; lean_object* v_snd_4936_; lean_object* v___y_4938_; lean_object* v___y_4939_; lean_object* v_data_4940_; lean_object* v_fst_4943_; lean_object* v_snd_4944_; lean_object* v___x_4945_; uint8_t v___x_4946_; lean_object* v___y_4948_; lean_object* v_a_4949_; uint8_t v___y_4964_; double v___y_4996_; 
v_fst_4935_ = lean_ctor_get(v_resStartStop_4929_, 0);
lean_inc(v_fst_4935_);
v_snd_4936_ = lean_ctor_get(v_resStartStop_4929_, 1);
lean_inc(v_snd_4936_);
lean_dec_ref(v_resStartStop_4929_);
v_fst_4943_ = lean_ctor_get(v_snd_4936_, 0);
lean_inc(v_fst_4943_);
v_snd_4944_ = lean_ctor_get(v_snd_4936_, 1);
lean_inc(v_snd_4944_);
lean_dec(v_snd_4936_);
v___x_4945_ = l_Lean_trace_profiler;
v___x_4946_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(v_opts_4925_, v___x_4945_);
if (v___x_4946_ == 0)
{
v___y_4964_ = v___x_4946_;
goto v___jp_4963_;
}
else
{
lean_object* v___x_5001_; uint8_t v___x_5002_; 
v___x_5001_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5002_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(v_opts_4925_, v___x_5001_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; lean_object* v___x_5004_; double v___x_5005_; double v___x_5006_; double v___x_5007_; 
v___x_5003_ = l_Lean_trace_profiler_threshold;
v___x_5004_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12(v_opts_4925_, v___x_5003_);
v___x_5005_ = lean_float_of_nat(v___x_5004_);
v___x_5006_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__2);
v___x_5007_ = lean_float_div(v___x_5005_, v___x_5006_);
v___y_4996_ = v___x_5007_;
goto v___jp_4995_;
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; double v___x_5010_; 
v___x_5008_ = l_Lean_trace_profiler_threshold;
v___x_5009_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__12(v_opts_4925_, v___x_5008_);
v___x_5010_ = lean_float_of_nat(v___x_5009_);
v___y_4996_ = v___x_5010_;
goto v___jp_4995_;
}
}
v___jp_4937_:
{
lean_object* v___x_4941_; 
lean_inc(v___y_4938_);
v___x_4941_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__9(v_oldTraces_4927_, v_data_4940_, v___y_4938_, v___y_4939_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v___x_4942_; 
lean_dec_ref_known(v___x_4941_, 1);
v___x_4942_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg(v_fst_4935_);
return v___x_4942_;
}
else
{
lean_dec(v_fst_4935_);
return v___x_4941_;
}
}
v___jp_4947_:
{
uint8_t v_result_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; double v___x_4953_; lean_object* v_data_4954_; 
v_result_4950_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__11(v_fst_4935_);
v___x_4951_ = lean_box(v_result_4950_);
v___x_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
v___x_4953_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__0);
lean_inc_ref(v_tag_4924_);
lean_inc_ref(v___x_4952_);
lean_inc(v_cls_4922_);
v_data_4954_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4954_, 0, v_cls_4922_);
lean_ctor_set(v_data_4954_, 1, v___x_4952_);
lean_ctor_set(v_data_4954_, 2, v_tag_4924_);
lean_ctor_set_float(v_data_4954_, sizeof(void*)*3, v___x_4953_);
lean_ctor_set_float(v_data_4954_, sizeof(void*)*3 + 8, v___x_4953_);
lean_ctor_set_uint8(v_data_4954_, sizeof(void*)*3 + 16, v_collapsed_4923_);
if (v___x_4946_ == 0)
{
lean_dec_ref_known(v___x_4952_, 1);
lean_dec(v_snd_4944_);
lean_dec(v_fst_4943_);
lean_dec_ref(v_tag_4924_);
lean_dec(v_cls_4922_);
v___y_4938_ = v___y_4948_;
v___y_4939_ = v_a_4949_;
v_data_4940_ = v_data_4954_;
goto v___jp_4937_;
}
else
{
lean_object* v_data_4955_; double v___x_4956_; double v___x_4957_; 
lean_dec_ref_known(v_data_4954_, 3);
v_data_4955_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4955_, 0, v_cls_4922_);
lean_ctor_set(v_data_4955_, 1, v___x_4952_);
lean_ctor_set(v_data_4955_, 2, v_tag_4924_);
v___x_4956_ = lean_unbox_float(v_fst_4943_);
lean_dec(v_fst_4943_);
lean_ctor_set_float(v_data_4955_, sizeof(void*)*3, v___x_4956_);
v___x_4957_ = lean_unbox_float(v_snd_4944_);
lean_dec(v_snd_4944_);
lean_ctor_set_float(v_data_4955_, sizeof(void*)*3 + 8, v___x_4957_);
lean_ctor_set_uint8(v_data_4955_, sizeof(void*)*3 + 16, v_collapsed_4923_);
v___y_4938_ = v___y_4948_;
v___y_4939_ = v_a_4949_;
v_data_4940_ = v_data_4955_;
goto v___jp_4937_;
}
}
v___jp_4958_:
{
lean_object* v_ref_4959_; lean_object* v___x_4960_; 
v_ref_4959_ = lean_ctor_get(v___y_4932_, 2);
lean_inc(v___y_4933_);
lean_inc_ref(v___y_4932_);
lean_inc(v___y_4931_);
lean_inc_ref(v___y_4930_);
lean_inc(v_fst_4935_);
v___x_4960_ = lean_apply_6(v_msg_4928_, v_fst_4935_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, lean_box(0));
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___y_4948_ = v_ref_4959_;
v_a_4949_ = v_a_4961_;
goto v___jp_4947_;
}
else
{
lean_object* v___x_4962_; 
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___closed__1);
v___y_4948_ = v_ref_4959_;
v_a_4949_ = v___x_4962_;
goto v___jp_4947_;
}
}
v___jp_4963_:
{
if (v_clsEnabled_4926_ == 0)
{
if (v___y_4964_ == 0)
{
lean_object* v___x_4965_; lean_object* v_traceState_4966_; lean_object* v_env_4967_; lean_object* v_nextMacroScope_4968_; lean_object* v_ngen_4969_; lean_object* v_auxDeclNGen_4970_; lean_object* v_cache_4971_; lean_object* v_recordedDeps_4972_; lean_object* v_messages_4973_; lean_object* v_infoState_4974_; lean_object* v_snapshotTasks_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4994_; 
lean_dec(v_snd_4944_);
lean_dec(v_fst_4943_);
lean_dec_ref(v_msg_4928_);
lean_dec_ref(v_tag_4924_);
lean_dec(v_cls_4922_);
v___x_4965_ = lean_st_ref_take(v___y_4933_);
v_traceState_4966_ = lean_ctor_get(v___x_4965_, 4);
v_env_4967_ = lean_ctor_get(v___x_4965_, 0);
v_nextMacroScope_4968_ = lean_ctor_get(v___x_4965_, 1);
v_ngen_4969_ = lean_ctor_get(v___x_4965_, 2);
v_auxDeclNGen_4970_ = lean_ctor_get(v___x_4965_, 3);
v_cache_4971_ = lean_ctor_get(v___x_4965_, 5);
v_recordedDeps_4972_ = lean_ctor_get(v___x_4965_, 6);
v_messages_4973_ = lean_ctor_get(v___x_4965_, 7);
v_infoState_4974_ = lean_ctor_get(v___x_4965_, 8);
v_snapshotTasks_4975_ = lean_ctor_get(v___x_4965_, 9);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4977_ = v___x_4965_;
v_isShared_4978_ = v_isSharedCheck_4994_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_snapshotTasks_4975_);
lean_inc(v_infoState_4974_);
lean_inc(v_messages_4973_);
lean_inc(v_recordedDeps_4972_);
lean_inc(v_cache_4971_);
lean_inc(v_traceState_4966_);
lean_inc(v_auxDeclNGen_4970_);
lean_inc(v_ngen_4969_);
lean_inc(v_nextMacroScope_4968_);
lean_inc(v_env_4967_);
lean_dec(v___x_4965_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4994_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
uint64_t v_tid_4979_; lean_object* v_traces_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4993_; 
v_tid_4979_ = lean_ctor_get_uint64(v_traceState_4966_, sizeof(void*)*1);
v_traces_4980_ = lean_ctor_get(v_traceState_4966_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v_traceState_4966_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4982_ = v_traceState_4966_;
v_isShared_4983_ = v_isSharedCheck_4993_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_traces_4980_);
lean_dec(v_traceState_4966_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4993_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4984_; lean_object* v___x_4986_; 
v___x_4984_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4927_, v_traces_4980_);
lean_dec_ref(v_traces_4980_);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_4984_);
v___x_4986_ = v___x_4982_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4984_);
lean_ctor_set_uint64(v_reuseFailAlloc_4992_, sizeof(void*)*1, v_tid_4979_);
v___x_4986_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4988_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 4, v___x_4986_);
v___x_4988_ = v___x_4977_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_env_4967_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_nextMacroScope_4968_);
lean_ctor_set(v_reuseFailAlloc_4991_, 2, v_ngen_4969_);
lean_ctor_set(v_reuseFailAlloc_4991_, 3, v_auxDeclNGen_4970_);
lean_ctor_set(v_reuseFailAlloc_4991_, 4, v___x_4986_);
lean_ctor_set(v_reuseFailAlloc_4991_, 5, v_cache_4971_);
lean_ctor_set(v_reuseFailAlloc_4991_, 6, v_recordedDeps_4972_);
lean_ctor_set(v_reuseFailAlloc_4991_, 7, v_messages_4973_);
lean_ctor_set(v_reuseFailAlloc_4991_, 8, v_infoState_4974_);
lean_ctor_set(v_reuseFailAlloc_4991_, 9, v_snapshotTasks_4975_);
v___x_4988_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = lean_st_ref_put(v___y_4933_, v___x_4988_);
v___x_4990_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg(v_fst_4935_);
return v___x_4990_;
}
}
}
}
}
else
{
goto v___jp_4958_;
}
}
else
{
goto v___jp_4958_;
}
}
v___jp_4995_:
{
double v___x_4997_; double v___x_4998_; double v___x_4999_; uint8_t v___x_5000_; 
v___x_4997_ = lean_unbox_float(v_snd_4944_);
v___x_4998_ = lean_unbox_float(v_fst_4943_);
v___x_4999_ = lean_float_sub(v___x_4997_, v___x_4998_);
v___x_5000_ = lean_float_decLt(v___y_4996_, v___x_4999_);
v___y_4964_ = v___x_5000_;
goto v___jp_4963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8___boxed(lean_object* v_cls_5011_, lean_object* v_collapsed_5012_, lean_object* v_tag_5013_, lean_object* v_opts_5014_, lean_object* v_clsEnabled_5015_, lean_object* v_oldTraces_5016_, lean_object* v_msg_5017_, lean_object* v_resStartStop_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
uint8_t v_collapsed_boxed_5024_; uint8_t v_clsEnabled_boxed_5025_; lean_object* v_res_5026_; 
v_collapsed_boxed_5024_ = lean_unbox(v_collapsed_5012_);
v_clsEnabled_boxed_5025_ = lean_unbox(v_clsEnabled_5015_);
v_res_5026_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(v_cls_5011_, v_collapsed_boxed_5024_, v_tag_5013_, v_opts_5014_, v_clsEnabled_boxed_5025_, v_oldTraces_5016_, v_msg_5017_, v_resStartStop_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec_ref(v_opts_5014_);
return v_res_5026_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5028_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__0));
v___x_5029_ = l_Lean_stringToMessageData(v___x_5028_);
return v___x_5029_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__2));
v___x_5032_ = l_Lean_stringToMessageData(v___x_5031_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg(lean_object* v_upperBound_5033_, lean_object* v_next_5034_, lean_object* v___x_5035_, lean_object* v_a_5036_, lean_object* v_b_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_){
_start:
{
lean_object* v_a_5044_; uint8_t v___x_5048_; 
v___x_5048_ = lean_nat_dec_lt(v_a_5036_, v_upperBound_5033_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; 
lean_dec(v_a_5036_);
lean_dec(v_next_5034_);
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v_b_5037_);
return v___x_5049_;
}
else
{
lean_object* v_toCold_5050_; lean_object* v_options_5051_; lean_object* v_inheritedTraceOptions_5052_; uint8_t v_hasTrace_5053_; lean_object* v___x_5054_; 
v_toCold_5050_ = lean_ctor_get(v___y_5040_, 0);
v_options_5051_ = lean_ctor_get(v_toCold_5050_, 2);
v_inheritedTraceOptions_5052_ = lean_ctor_get(v_toCold_5050_, 11);
v_hasTrace_5053_ = lean_ctor_get_uint8(v_options_5051_, sizeof(void*)*1);
v___x_5054_ = lean_box(0);
if (v_hasTrace_5053_ == 0)
{
v_a_5044_ = v___x_5054_;
goto v___jp_5043_;
}
else
{
lean_object* v_cls_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v_cls_5055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_5056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7);
v___x_5057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5052_, v_options_5051_, v___x_5056_);
if (v___x_5057_ == 0)
{
v_a_5044_ = v___x_5054_;
goto v___jp_5043_;
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5058_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__1);
lean_inc(v_next_5034_);
v___x_5059_ = l_Nat_reprFast(v_next_5034_);
v___x_5060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5059_);
v___x_5061_ = l_Lean_MessageData_ofFormat(v___x_5060_);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5058_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
v___x_5063_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___closed__3);
v___x_5064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5062_);
lean_ctor_set(v___x_5064_, 1, v___x_5063_);
lean_inc(v_a_5036_);
v___x_5065_ = l_Nat_reprFast(v_a_5036_);
v___x_5066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
v___x_5067_ = l_Lean_MessageData_ofFormat(v___x_5066_);
v___x_5068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5064_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0___closed__5);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5068_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = lean_array_fget_borrowed(v___x_5035_, v_a_5036_);
lean_inc(v___x_5071_);
v___x_5072_ = l_Nat_reprFast(v___x_5071_);
v___x_5073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
v___x_5074_ = l_Lean_MessageData_ofFormat(v___x_5073_);
v___x_5075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5070_);
lean_ctor_set(v___x_5075_, 1, v___x_5074_);
v___x_5076_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(v_cls_5055_, v___x_5075_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_dec_ref_known(v___x_5076_, 1);
v_a_5044_ = v___x_5054_;
goto v___jp_5043_;
}
else
{
lean_dec(v_a_5036_);
lean_dec(v_next_5034_);
return v___x_5076_;
}
}
}
}
v___jp_5043_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5045_ = lean_unsigned_to_nat(1u);
v___x_5046_ = lean_nat_add(v_a_5036_, v___x_5045_);
lean_dec(v_a_5036_);
v_a_5036_ = v___x_5046_;
v_b_5037_ = v_a_5044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg___boxed(lean_object* v_upperBound_5077_, lean_object* v_next_5078_, lean_object* v___x_5079_, lean_object* v_a_5080_, lean_object* v_b_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg(v_upperBound_5077_, v_next_5078_, v___x_5079_, v_a_5080_, v_b_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec_ref(v___x_5079_);
lean_dec(v_upperBound_5077_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg(lean_object* v_upperBound_5088_, lean_object* v___x_5089_, lean_object* v_a_5090_, lean_object* v_b_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
uint8_t v___x_5097_; 
v___x_5097_ = lean_nat_dec_lt(v_a_5090_, v_upperBound_5088_);
if (v___x_5097_ == 0)
{
lean_object* v___x_5098_; 
lean_dec(v_a_5090_);
v___x_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5098_, 0, v_b_5091_);
return v___x_5098_;
}
else
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5099_ = lean_unsigned_to_nat(0u);
v___x_5100_ = lean_box(0);
v___x_5101_ = lean_array_fget_borrowed(v___x_5089_, v_a_5090_);
v___x_5102_ = lean_array_get_size(v___x_5101_);
lean_inc(v_a_5090_);
v___x_5103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg(v___x_5102_, v_a_5090_, v___x_5101_, v___x_5099_, v___x_5100_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
lean_dec_ref_known(v___x_5103_, 1);
v___x_5104_ = lean_unsigned_to_nat(1u);
v___x_5105_ = lean_nat_add(v_a_5090_, v___x_5104_);
lean_dec(v_a_5090_);
v_a_5090_ = v___x_5105_;
v_b_5091_ = v___x_5100_;
goto _start;
}
else
{
lean_dec(v_a_5090_);
return v___x_5103_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg___boxed(lean_object* v_upperBound_5107_, lean_object* v___x_5108_, lean_object* v_a_5109_, lean_object* v_b_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg(v_upperBound_5107_, v___x_5108_, v_a_5109_, v_b_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec_ref(v___x_5108_);
lean_dec(v_upperBound_5107_);
return v_res_5116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0(uint8_t v___x_5117_, lean_object* v_x_5118_, lean_object* v_x_5119_){
_start:
{
lean_object* v_fst_5120_; lean_object* v_fst_5121_; lean_object* v_fst_5122_; lean_object* v_snd_5123_; lean_object* v_fst_5124_; lean_object* v_snd_5125_; uint8_t v___x_5126_; 
v_fst_5120_ = lean_ctor_get(v_x_5118_, 0);
v_fst_5121_ = lean_ctor_get(v_x_5119_, 0);
v_fst_5122_ = lean_ctor_get(v_fst_5120_, 0);
v_snd_5123_ = lean_ctor_get(v_fst_5120_, 1);
v_fst_5124_ = lean_ctor_get(v_fst_5121_, 0);
v_snd_5125_ = lean_ctor_get(v_fst_5121_, 1);
v___x_5126_ = lean_expr_lt(v_fst_5122_, v_fst_5124_);
if (v___x_5126_ == 0)
{
uint8_t v___x_5127_; 
v___x_5127_ = lean_expr_eqv(v_fst_5122_, v_fst_5124_);
if (v___x_5127_ == 0)
{
return v___x_5127_;
}
else
{
uint8_t v___x_5128_; 
v___x_5128_ = lean_nat_dec_lt(v_snd_5123_, v_snd_5125_);
return v___x_5128_;
}
}
else
{
return v___x_5117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0___boxed(lean_object* v___x_5129_, lean_object* v_x_5130_, lean_object* v_x_5131_){
_start:
{
uint8_t v___x_31075__boxed_5132_; uint8_t v_res_5133_; lean_object* v_r_5134_; 
v___x_31075__boxed_5132_ = lean_unbox(v___x_5129_);
v_res_5133_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0(v___x_31075__boxed_5132_, v_x_5130_, v_x_5131_);
lean_dec_ref(v_x_5131_);
lean_dec_ref(v_x_5130_);
v_r_5134_ = lean_box(v_res_5133_);
return v_r_5134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg(uint8_t v___x_5135_, lean_object* v_hi_5136_, lean_object* v_pivot_5137_, lean_object* v_as_5138_, lean_object* v_i_5139_, lean_object* v_k_5140_){
_start:
{
uint8_t v___y_5146_; uint8_t v___x_5152_; 
v___x_5152_ = lean_nat_dec_lt(v_k_5140_, v_hi_5136_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
lean_dec(v_k_5140_);
v___x_5153_ = lean_array_fswap(v_as_5138_, v_i_5139_, v_hi_5136_);
v___x_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5154_, 0, v_i_5139_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
return v___x_5154_;
}
else
{
lean_object* v___x_5155_; lean_object* v_fst_5156_; lean_object* v_fst_5157_; lean_object* v_fst_5158_; lean_object* v_snd_5159_; lean_object* v_fst_5160_; lean_object* v_snd_5161_; uint8_t v___x_5162_; 
v___x_5155_ = lean_array_fget_borrowed(v_as_5138_, v_k_5140_);
v_fst_5156_ = lean_ctor_get(v___x_5155_, 0);
v_fst_5157_ = lean_ctor_get(v_pivot_5137_, 0);
v_fst_5158_ = lean_ctor_get(v_fst_5156_, 0);
v_snd_5159_ = lean_ctor_get(v_fst_5156_, 1);
v_fst_5160_ = lean_ctor_get(v_fst_5157_, 0);
v_snd_5161_ = lean_ctor_get(v_fst_5157_, 1);
v___x_5162_ = lean_expr_lt(v_fst_5158_, v_fst_5160_);
if (v___x_5162_ == 0)
{
uint8_t v___x_5163_; 
v___x_5163_ = lean_expr_eqv(v_fst_5158_, v_fst_5160_);
if (v___x_5163_ == 0)
{
goto v___jp_5141_;
}
else
{
uint8_t v___x_5164_; 
v___x_5164_ = lean_nat_dec_lt(v_snd_5159_, v_snd_5161_);
v___y_5146_ = v___x_5164_;
goto v___jp_5145_;
}
}
else
{
v___y_5146_ = v___x_5135_;
goto v___jp_5145_;
}
}
v___jp_5141_:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5142_ = lean_unsigned_to_nat(1u);
v___x_5143_ = lean_nat_add(v_k_5140_, v___x_5142_);
lean_dec(v_k_5140_);
v_k_5140_ = v___x_5143_;
goto _start;
}
v___jp_5145_:
{
if (v___y_5146_ == 0)
{
goto v___jp_5141_;
}
else
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; 
v___x_5147_ = lean_array_fswap(v_as_5138_, v_i_5139_, v_k_5140_);
v___x_5148_ = lean_unsigned_to_nat(1u);
v___x_5149_ = lean_nat_add(v_i_5139_, v___x_5148_);
lean_dec(v_i_5139_);
v___x_5150_ = lean_nat_add(v_k_5140_, v___x_5148_);
lean_dec(v_k_5140_);
v_as_5138_ = v___x_5147_;
v_i_5139_ = v___x_5149_;
v_k_5140_ = v___x_5150_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg___boxed(lean_object* v___x_5165_, lean_object* v_hi_5166_, lean_object* v_pivot_5167_, lean_object* v_as_5168_, lean_object* v_i_5169_, lean_object* v_k_5170_){
_start:
{
uint8_t v___x_31102__boxed_5171_; lean_object* v_res_5172_; 
v___x_31102__boxed_5171_ = lean_unbox(v___x_5165_);
v_res_5172_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg(v___x_31102__boxed_5171_, v_hi_5166_, v_pivot_5167_, v_as_5168_, v_i_5169_, v_k_5170_);
lean_dec_ref(v_pivot_5167_);
lean_dec(v_hi_5166_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(uint8_t v___x_5173_, lean_object* v_n_5174_, lean_object* v_as_5175_, lean_object* v_lo_5176_, lean_object* v_hi_5177_){
_start:
{
lean_object* v___y_5179_; uint8_t v___x_5189_; 
v___x_5189_ = lean_nat_dec_lt(v_lo_5176_, v_hi_5177_);
if (v___x_5189_ == 0)
{
lean_dec(v_lo_5176_);
return v_as_5175_;
}
else
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v_mid_5192_; lean_object* v___y_5194_; lean_object* v___y_5200_; lean_object* v___x_5205_; lean_object* v___x_5206_; uint8_t v___x_5207_; 
v___x_5190_ = lean_nat_add(v_lo_5176_, v_hi_5177_);
v___x_5191_ = lean_unsigned_to_nat(1u);
v_mid_5192_ = lean_nat_shiftr(v___x_5190_, v___x_5191_);
lean_dec(v___x_5190_);
v___x_5205_ = lean_array_fget_borrowed(v_as_5175_, v_mid_5192_);
v___x_5206_ = lean_array_fget_borrowed(v_as_5175_, v_lo_5176_);
v___x_5207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0(v___x_5173_, v___x_5205_, v___x_5206_);
if (v___x_5207_ == 0)
{
v___y_5200_ = v_as_5175_;
goto v___jp_5199_;
}
else
{
lean_object* v___x_5208_; 
v___x_5208_ = lean_array_fswap(v_as_5175_, v_lo_5176_, v_mid_5192_);
v___y_5200_ = v___x_5208_;
goto v___jp_5199_;
}
v___jp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5195_ = lean_array_fget_borrowed(v___y_5194_, v_mid_5192_);
v___x_5196_ = lean_array_fget_borrowed(v___y_5194_, v_hi_5177_);
v___x_5197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0(v___x_5173_, v___x_5195_, v___x_5196_);
if (v___x_5197_ == 0)
{
lean_dec(v_mid_5192_);
v___y_5179_ = v___y_5194_;
goto v___jp_5178_;
}
else
{
lean_object* v___x_5198_; 
v___x_5198_ = lean_array_fswap(v___y_5194_, v_mid_5192_, v_hi_5177_);
lean_dec(v_mid_5192_);
v___y_5179_ = v___x_5198_;
goto v___jp_5178_;
}
}
v___jp_5199_:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; 
v___x_5201_ = lean_array_fget_borrowed(v___y_5200_, v_hi_5177_);
v___x_5202_ = lean_array_fget_borrowed(v___y_5200_, v_lo_5176_);
v___x_5203_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___lam__0(v___x_5173_, v___x_5201_, v___x_5202_);
if (v___x_5203_ == 0)
{
v___y_5194_ = v___y_5200_;
goto v___jp_5193_;
}
else
{
lean_object* v___x_5204_; 
v___x_5204_ = lean_array_fswap(v___y_5200_, v_lo_5176_, v_hi_5177_);
v___y_5194_ = v___x_5204_;
goto v___jp_5193_;
}
}
}
v___jp_5178_:
{
lean_object* v_pivot_5180_; lean_object* v___x_5181_; lean_object* v_fst_5182_; lean_object* v_snd_5183_; uint8_t v___x_5184_; 
v_pivot_5180_ = lean_array_fget(v___y_5179_, v_hi_5177_);
lean_inc_n(v_lo_5176_, 2);
v___x_5181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg(v___x_5173_, v_hi_5177_, v_pivot_5180_, v___y_5179_, v_lo_5176_, v_lo_5176_);
lean_dec(v_pivot_5180_);
v_fst_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_fst_5182_);
v_snd_5183_ = lean_ctor_get(v___x_5181_, 1);
lean_inc(v_snd_5183_);
lean_dec_ref(v___x_5181_);
v___x_5184_ = lean_nat_dec_le(v_hi_5177_, v_fst_5182_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(v___x_5173_, v_n_5174_, v_snd_5183_, v_lo_5176_, v_fst_5182_);
v___x_5186_ = lean_unsigned_to_nat(1u);
v___x_5187_ = lean_nat_add(v_fst_5182_, v___x_5186_);
lean_dec(v_fst_5182_);
v_as_5175_ = v___x_5185_;
v_lo_5176_ = v___x_5187_;
goto _start;
}
else
{
lean_dec(v_fst_5182_);
lean_dec(v_lo_5176_);
return v_snd_5183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg___boxed(lean_object* v___x_5209_, lean_object* v_n_5210_, lean_object* v_as_5211_, lean_object* v_lo_5212_, lean_object* v_hi_5213_){
_start:
{
uint8_t v___x_31153__boxed_5214_; lean_object* v_res_5215_; 
v___x_31153__boxed_5214_ = lean_unbox(v___x_5209_);
v_res_5215_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(v___x_31153__boxed_5214_, v_n_5210_, v_as_5211_, v_lo_5212_, v_hi_5213_);
lean_dec(v_hi_5213_);
lean_dec(v_n_5210_);
return v_res_5215_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1(void){
_start:
{
lean_object* v___x_5217_; double v___x_5218_; 
v___x_5217_ = lean_unsigned_to_nat(1000000000u);
v___x_5218_ = lean_float_of_nat(v___x_5217_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis(lean_object* v_sets_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_){
_start:
{
lean_object* v_toCold_5228_; lean_object* v_options_5229_; uint8_t v_hasTrace_5230_; 
v_toCold_5228_ = lean_ctor_get(v_a_5222_, 0);
v_options_5229_ = lean_ctor_get(v_toCold_5228_, 2);
v_hasTrace_5230_ = lean_ctor_get_uint8(v_options_5229_, sizeof(void*)*1);
if (v_hasTrace_5230_ == 0)
{
goto v___jp_5225_;
}
else
{
lean_object* v_inheritedTraceOptions_5231_; lean_object* v_cls_5232_; lean_object* v___x_5233_; uint8_t v___x_5234_; 
v_inheritedTraceOptions_5231_ = lean_ctor_get(v_toCold_5228_, 11);
v_cls_5232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_5233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7);
v___x_5234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5231_, v_options_5229_, v___x_5233_);
if (v___x_5234_ == 0)
{
goto v___jp_5225_;
}
else
{
lean_object* v_varRoots_5235_; lean_object* v_posRoot_5236_; lean_object* v___f_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5374_; 
v_varRoots_5235_ = lean_ctor_get(v_sets_5219_, 1);
v_posRoot_5236_ = lean_ctor_get(v_sets_5219_, 2);
v___f_5237_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__0));
v___x_5238_ = lean_unsigned_to_nat(0u);
v___x_5239_ = lean_array_get_size(v_varRoots_5235_);
v___x_5240_ = lean_box(0);
v___x_5241_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1));
v___x_5242_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg(v_a_5223_);
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5374_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5374_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5247_; uint8_t v___x_5248_; 
v___x_5247_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5248_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(v_options_5229_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; lean_object* v_a_5251_; lean_object* v_a_5264_; lean_object* v___x_5268_; 
v___x_5249_ = lean_io_mono_nanos_now();
v___x_5268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg(v___x_5239_, v_varRoots_5235_, v___x_5238_, v___x_5240_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v___y_5270_; lean_object* v___y_5286_; lean_object* v___y_5287_; lean_object* v___y_5288_; lean_object* v___y_5289_; lean_object* v___y_5292_; lean_object* v___y_5293_; lean_object* v___y_5294_; lean_object* v___y_5295_; lean_object* v___y_5298_; lean_object* v_size_5304_; lean_object* v_buckets_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; uint8_t v___x_5308_; 
lean_dec_ref_known(v___x_5268_, 1);
v_size_5304_ = lean_ctor_get(v_posRoot_5236_, 0);
v_buckets_5305_ = lean_ctor_get(v_posRoot_5236_, 1);
v___x_5306_ = lean_mk_empty_array_with_capacity(v_size_5304_);
v___x_5307_ = lean_array_get_size(v_buckets_5305_);
v___x_5308_ = lean_nat_dec_lt(v___x_5238_, v___x_5307_);
if (v___x_5308_ == 0)
{
v___y_5298_ = v___x_5306_;
goto v___jp_5297_;
}
else
{
size_t v___x_5309_; size_t v___x_5310_; lean_object* v___x_5311_; 
v___x_5309_ = ((size_t)0ULL);
v___x_5310_ = lean_usize_of_nat(v___x_5307_);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3(v_buckets_5305_, v___x_5309_, v___x_5310_, v___x_5306_);
v___y_5298_ = v___x_5311_;
goto v___jp_5297_;
}
v___jp_5269_:
{
size_t v_sz_5271_; size_t v___x_5272_; lean_object* v___x_5273_; 
v_sz_5271_ = lean_array_size(v___y_5270_);
v___x_5272_ = ((size_t)0ULL);
v___x_5273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0(v___y_5270_, v_sz_5271_, v___x_5272_, v___x_5240_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
lean_dec_ref(v___y_5270_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v___x_5274_; 
lean_dec_ref_known(v___x_5273_, 1);
v___x_5274_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses(v_sets_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5274_) == 0)
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_del_object(v___x_5245_);
v_a_5275_ = lean_ctor_get(v___x_5274_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5274_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5274_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
lean_ctor_set_tag(v___x_5277_, 1);
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
v_a_5251_ = v___x_5280_;
goto v___jp_5250_;
}
}
}
else
{
lean_object* v_a_5283_; 
v_a_5283_ = lean_ctor_get(v___x_5274_, 0);
lean_inc(v_a_5283_);
lean_dec_ref_known(v___x_5274_, 1);
v_a_5264_ = v_a_5283_;
goto v___jp_5263_;
}
}
else
{
lean_object* v_a_5284_; 
v_a_5284_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_a_5284_);
lean_dec_ref_known(v___x_5273_, 1);
v_a_5264_ = v_a_5284_;
goto v___jp_5263_;
}
}
v___jp_5285_:
{
lean_object* v___x_5290_; 
v___x_5290_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(v_hasTrace_5230_, v___y_5288_, v___y_5286_, v___y_5287_, v___y_5289_);
lean_dec(v___y_5289_);
lean_dec(v___y_5288_);
v___y_5270_ = v___x_5290_;
goto v___jp_5269_;
}
v___jp_5291_:
{
uint8_t v___x_5296_; 
v___x_5296_ = lean_nat_dec_le(v___y_5295_, v___y_5293_);
if (v___x_5296_ == 0)
{
lean_dec(v___y_5293_);
lean_inc(v___y_5295_);
v___y_5286_ = v___y_5292_;
v___y_5287_ = v___y_5295_;
v___y_5288_ = v___y_5294_;
v___y_5289_ = v___y_5295_;
goto v___jp_5285_;
}
else
{
v___y_5286_ = v___y_5292_;
v___y_5287_ = v___y_5295_;
v___y_5288_ = v___y_5294_;
v___y_5289_ = v___y_5293_;
goto v___jp_5285_;
}
}
v___jp_5297_:
{
lean_object* v___x_5299_; uint8_t v___x_5300_; 
v___x_5299_ = lean_array_get_size(v___y_5298_);
v___x_5300_ = lean_nat_dec_eq(v___x_5299_, v___x_5238_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; lean_object* v___x_5302_; uint8_t v___x_5303_; 
v___x_5301_ = lean_unsigned_to_nat(1u);
v___x_5302_ = lean_nat_sub(v___x_5299_, v___x_5301_);
v___x_5303_ = lean_nat_dec_le(v___x_5238_, v___x_5302_);
if (v___x_5303_ == 0)
{
lean_inc(v___x_5302_);
v___y_5292_ = v___y_5298_;
v___y_5293_ = v___x_5302_;
v___y_5294_ = v___x_5299_;
v___y_5295_ = v___x_5302_;
goto v___jp_5291_;
}
else
{
v___y_5292_ = v___y_5298_;
v___y_5293_ = v___x_5302_;
v___y_5294_ = v___x_5299_;
v___y_5295_ = v___x_5238_;
goto v___jp_5291_;
}
}
else
{
v___y_5270_ = v___y_5298_;
goto v___jp_5269_;
}
}
}
else
{
lean_object* v_a_5312_; 
v_a_5312_ = lean_ctor_get(v___x_5268_, 0);
lean_inc(v_a_5312_);
lean_dec_ref_known(v___x_5268_, 1);
v_a_5264_ = v_a_5312_;
goto v___jp_5263_;
}
v___jp_5250_:
{
lean_object* v___x_5252_; double v___x_5253_; double v___x_5254_; double v___x_5255_; double v___x_5256_; double v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5252_ = lean_io_mono_nanos_now();
v___x_5253_ = lean_float_of_nat(v___x_5249_);
v___x_5254_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1);
v___x_5255_ = lean_float_div(v___x_5253_, v___x_5254_);
v___x_5256_ = lean_float_of_nat(v___x_5252_);
v___x_5257_ = lean_float_div(v___x_5256_, v___x_5254_);
v___x_5258_ = lean_box_float(v___x_5255_);
v___x_5259_ = lean_box_float(v___x_5257_);
v___x_5260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5258_);
lean_ctor_set(v___x_5260_, 1, v___x_5259_);
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v_a_5251_);
lean_ctor_set(v___x_5261_, 1, v___x_5260_);
v___x_5262_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(v_cls_5232_, v_hasTrace_5230_, v___x_5241_, v_options_5229_, v___x_5234_, v_a_5243_, v___f_5237_, v___x_5261_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
return v___x_5262_;
}
v___jp_5263_:
{
lean_object* v___x_5266_; 
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v_a_5264_);
v___x_5266_ = v___x_5245_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5264_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
v_a_5251_ = v___x_5266_;
goto v___jp_5250_;
}
}
}
else
{
lean_object* v___x_5313_; lean_object* v_a_5315_; lean_object* v_a_5325_; lean_object* v___x_5329_; 
v___x_5313_ = lean_io_get_num_heartbeats();
v___x_5329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg(v___x_5239_, v_varRoots_5235_, v___x_5238_, v___x_5240_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v___y_5331_; lean_object* v___y_5347_; lean_object* v___y_5348_; lean_object* v___y_5349_; lean_object* v___y_5350_; lean_object* v___y_5353_; lean_object* v___y_5354_; lean_object* v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5359_; lean_object* v_size_5365_; lean_object* v_buckets_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; uint8_t v___x_5369_; 
lean_dec_ref_known(v___x_5329_, 1);
v_size_5365_ = lean_ctor_get(v_posRoot_5236_, 0);
v_buckets_5366_ = lean_ctor_get(v_posRoot_5236_, 1);
v___x_5367_ = lean_mk_empty_array_with_capacity(v_size_5365_);
v___x_5368_ = lean_array_get_size(v_buckets_5366_);
v___x_5369_ = lean_nat_dec_lt(v___x_5238_, v___x_5368_);
if (v___x_5369_ == 0)
{
v___y_5359_ = v___x_5367_;
goto v___jp_5358_;
}
else
{
size_t v___x_5370_; size_t v___x_5371_; lean_object* v___x_5372_; 
v___x_5370_ = ((size_t)0ULL);
v___x_5371_ = lean_usize_of_nat(v___x_5368_);
v___x_5372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__3(v_buckets_5366_, v___x_5370_, v___x_5371_, v___x_5367_);
v___y_5359_ = v___x_5372_;
goto v___jp_5358_;
}
v___jp_5330_:
{
size_t v_sz_5332_; size_t v___x_5333_; lean_object* v___x_5334_; 
v_sz_5332_ = lean_array_size(v___y_5331_);
v___x_5333_ = ((size_t)0ULL);
v___x_5334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__0(v___y_5331_, v_sz_5332_, v___x_5333_, v___x_5240_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
lean_dec_ref(v___y_5331_);
if (lean_obj_tag(v___x_5334_) == 0)
{
lean_object* v___x_5335_; 
lean_dec_ref_known(v___x_5334_, 1);
v___x_5335_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses(v_sets_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
lean_del_object(v___x_5245_);
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
lean_ctor_set_tag(v___x_5338_, 1);
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
v_a_5315_ = v___x_5341_;
goto v___jp_5314_;
}
}
}
else
{
lean_object* v_a_5344_; 
v_a_5344_ = lean_ctor_get(v___x_5335_, 0);
lean_inc(v_a_5344_);
lean_dec_ref_known(v___x_5335_, 1);
v_a_5325_ = v_a_5344_;
goto v___jp_5324_;
}
}
else
{
lean_object* v_a_5345_; 
v_a_5345_ = lean_ctor_get(v___x_5334_, 0);
lean_inc(v_a_5345_);
lean_dec_ref_known(v___x_5334_, 1);
v_a_5325_ = v_a_5345_;
goto v___jp_5324_;
}
}
v___jp_5346_:
{
lean_object* v___x_5351_; 
v___x_5351_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(v_hasTrace_5230_, v___y_5348_, v___y_5347_, v___y_5349_, v___y_5350_);
lean_dec(v___y_5350_);
lean_dec(v___y_5348_);
v___y_5331_ = v___x_5351_;
goto v___jp_5330_;
}
v___jp_5352_:
{
uint8_t v___x_5357_; 
v___x_5357_ = lean_nat_dec_le(v___y_5356_, v___y_5354_);
if (v___x_5357_ == 0)
{
lean_dec(v___y_5354_);
lean_inc(v___y_5356_);
v___y_5347_ = v___y_5353_;
v___y_5348_ = v___y_5355_;
v___y_5349_ = v___y_5356_;
v___y_5350_ = v___y_5356_;
goto v___jp_5346_;
}
else
{
v___y_5347_ = v___y_5353_;
v___y_5348_ = v___y_5355_;
v___y_5349_ = v___y_5356_;
v___y_5350_ = v___y_5354_;
goto v___jp_5346_;
}
}
v___jp_5358_:
{
lean_object* v___x_5360_; uint8_t v___x_5361_; 
v___x_5360_ = lean_array_get_size(v___y_5359_);
v___x_5361_ = lean_nat_dec_eq(v___x_5360_, v___x_5238_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; lean_object* v___x_5363_; uint8_t v___x_5364_; 
v___x_5362_ = lean_unsigned_to_nat(1u);
v___x_5363_ = lean_nat_sub(v___x_5360_, v___x_5362_);
v___x_5364_ = lean_nat_dec_le(v___x_5238_, v___x_5363_);
if (v___x_5364_ == 0)
{
lean_inc(v___x_5363_);
v___y_5353_ = v___y_5359_;
v___y_5354_ = v___x_5363_;
v___y_5355_ = v___x_5360_;
v___y_5356_ = v___x_5363_;
goto v___jp_5352_;
}
else
{
v___y_5353_ = v___y_5359_;
v___y_5354_ = v___x_5363_;
v___y_5355_ = v___x_5360_;
v___y_5356_ = v___x_5238_;
goto v___jp_5352_;
}
}
else
{
v___y_5331_ = v___y_5359_;
goto v___jp_5330_;
}
}
}
else
{
lean_object* v_a_5373_; 
v_a_5373_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v___x_5329_, 1);
v_a_5325_ = v_a_5373_;
goto v___jp_5324_;
}
v___jp_5314_:
{
lean_object* v___x_5316_; double v___x_5317_; double v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
v___x_5316_ = lean_io_get_num_heartbeats();
v___x_5317_ = lean_float_of_nat(v___x_5313_);
v___x_5318_ = lean_float_of_nat(v___x_5316_);
v___x_5319_ = lean_box_float(v___x_5317_);
v___x_5320_ = lean_box_float(v___x_5318_);
v___x_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5319_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5322_, 0, v_a_5315_);
lean_ctor_set(v___x_5322_, 1, v___x_5321_);
v___x_5323_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(v_cls_5232_, v_hasTrace_5230_, v___x_5241_, v_options_5229_, v___x_5234_, v_a_5243_, v___f_5237_, v___x_5322_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
return v___x_5323_;
}
v___jp_5324_:
{
lean_object* v___x_5327_; 
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v_a_5325_);
v___x_5327_ = v___x_5245_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5325_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
v_a_5315_ = v___x_5327_;
goto v___jp_5314_;
}
}
}
}
}
}
v___jp_5225_:
{
lean_object* v___x_5226_; lean_object* v___x_5227_; 
v___x_5226_ = lean_box(0);
v___x_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5226_);
return v___x_5227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___boxed(lean_object* v_sets_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis(v_sets_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
lean_dec_ref(v_sets_5375_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1(uint8_t v___x_5382_, lean_object* v_n_5383_, lean_object* v_as_5384_, lean_object* v_lo_5385_, lean_object* v_hi_5386_, lean_object* v_w_5387_, lean_object* v_hlo_5388_, lean_object* v_hhi_5389_){
_start:
{
lean_object* v___x_5390_; 
v___x_5390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___redArg(v___x_5382_, v_n_5383_, v_as_5384_, v_lo_5385_, v_hi_5386_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1___boxed(lean_object* v___x_5391_, lean_object* v_n_5392_, lean_object* v_as_5393_, lean_object* v_lo_5394_, lean_object* v_hi_5395_, lean_object* v_w_5396_, lean_object* v_hlo_5397_, lean_object* v_hhi_5398_){
_start:
{
uint8_t v___x_31525__boxed_5399_; lean_object* v_res_5400_; 
v___x_31525__boxed_5399_ = lean_unbox(v___x_5391_);
v_res_5400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1(v___x_31525__boxed_5399_, v_n_5392_, v_as_5393_, v_lo_5394_, v_hi_5395_, v_w_5396_, v_hlo_5397_, v_hhi_5398_);
lean_dec(v_hi_5395_);
lean_dec(v_n_5392_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4(lean_object* v_upperBound_5401_, lean_object* v_next_5402_, lean_object* v___x_5403_, lean_object* v_inst_5404_, lean_object* v_R_5405_, lean_object* v_a_5406_, lean_object* v_b_5407_, lean_object* v_c_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_){
_start:
{
lean_object* v___x_5414_; 
v___x_5414_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___redArg(v_upperBound_5401_, v_next_5402_, v___x_5403_, v_a_5406_, v_b_5407_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4___boxed(lean_object* v_upperBound_5415_, lean_object* v_next_5416_, lean_object* v___x_5417_, lean_object* v_inst_5418_, lean_object* v_R_5419_, lean_object* v_a_5420_, lean_object* v_b_5421_, lean_object* v_c_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__4(v_upperBound_5415_, v_next_5416_, v___x_5417_, v_inst_5418_, v_R_5419_, v_a_5420_, v_b_5421_, v_c_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec(v___y_5424_);
lean_dec_ref(v___y_5423_);
lean_dec_ref(v___x_5417_);
lean_dec(v_upperBound_5415_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5(lean_object* v_upperBound_5429_, lean_object* v___x_5430_, lean_object* v_inst_5431_, lean_object* v_R_5432_, lean_object* v_a_5433_, lean_object* v_b_5434_, lean_object* v_c_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___redArg(v_upperBound_5429_, v___x_5430_, v_a_5433_, v_b_5434_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5___boxed(lean_object* v_upperBound_5442_, lean_object* v___x_5443_, lean_object* v_inst_5444_, lean_object* v_R_5445_, lean_object* v_a_5446_, lean_object* v_b_5447_, lean_object* v_c_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__5(v_upperBound_5442_, v___x_5443_, v_inst_5444_, v_R_5445_, v_a_5446_, v_b_5447_, v_c_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec_ref(v___x_5443_);
lean_dec(v_upperBound_5442_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10(lean_object* v_00_u03b1_5455_, lean_object* v_x_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
lean_object* v___x_5462_; 
v___x_5462_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___redArg(v_x_5456_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10___boxed(lean_object* v_00_u03b1_5463_, lean_object* v_x_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8_spec__10(v_00_u03b1_5463_, v_x_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
return v_res_5470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1(uint8_t v___x_5471_, lean_object* v_n_5472_, lean_object* v_lo_5473_, lean_object* v_hi_5474_, lean_object* v_hhi_5475_, lean_object* v_pivot_5476_, lean_object* v_as_5477_, lean_object* v_i_5478_, lean_object* v_k_5479_, lean_object* v_ilo_5480_, lean_object* v_ik_5481_, lean_object* v_w_5482_){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___redArg(v___x_5471_, v_hi_5474_, v_pivot_5476_, v_as_5477_, v_i_5478_, v_k_5479_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1___boxed(lean_object* v___x_5484_, lean_object* v_n_5485_, lean_object* v_lo_5486_, lean_object* v_hi_5487_, lean_object* v_hhi_5488_, lean_object* v_pivot_5489_, lean_object* v_as_5490_, lean_object* v_i_5491_, lean_object* v_k_5492_, lean_object* v_ilo_5493_, lean_object* v_ik_5494_, lean_object* v_w_5495_){
_start:
{
uint8_t v___x_31602__boxed_5496_; lean_object* v_res_5497_; 
v___x_31602__boxed_5496_ = lean_unbox(v___x_5484_);
v_res_5497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__1_spec__1(v___x_31602__boxed_5496_, v_n_5485_, v_lo_5486_, v_hi_5487_, v_hhi_5488_, v_pivot_5489_, v_as_5490_, v_i_5491_, v_k_5492_, v_ilo_5493_, v_ik_5494_, v_w_5495_);
lean_dec_ref(v_pivot_5489_);
lean_dec(v_hi_5487_);
lean_dec(v_lo_5486_);
lean_dec(v_n_5485_);
return v_res_5497_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5499_; lean_object* v___x_5500_; 
v___x_5499_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__0));
v___x_5500_ = l_Lean_stringToMessageData(v___x_5499_);
return v___x_5500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0(lean_object* v_x_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_){
_start:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; 
v___x_5507_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___closed__1);
v___x_5508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5508_, 0, v___x_5507_);
return v___x_5508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0___boxed(lean_object* v_x_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
lean_object* v_res_5515_; 
v_res_5515_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___lam__0(v_x_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_);
lean_dec(v___y_5513_);
lean_dec_ref(v___y_5512_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
lean_dec_ref(v_x_5509_);
return v_res_5515_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; 
v___x_5517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__0));
v___x_5518_ = l_Lean_stringToMessageData(v___x_5517_);
return v___x_5518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0(lean_object* v_as_5519_, size_t v_sz_5520_, size_t v_i_5521_, lean_object* v_b_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v_a_5529_; uint8_t v___x_5533_; 
v___x_5533_ = lean_usize_dec_lt(v_i_5521_, v_sz_5520_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v_b_5522_);
return v___x_5534_;
}
else
{
lean_object* v_a_5535_; lean_object* v_snd_5536_; lean_object* v_fst_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5566_; 
v_a_5535_ = lean_array_uget(v_as_5519_, v_i_5521_);
v_snd_5536_ = lean_ctor_get(v_a_5535_, 1);
v_fst_5537_ = lean_ctor_get(v_a_5535_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v_a_5535_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5539_ = v_a_5535_;
v_isShared_5540_ = v_isSharedCheck_5566_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_snd_5536_);
lean_inc(v_fst_5537_);
lean_dec(v_a_5535_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5566_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
uint8_t v_full_5541_; lean_object* v_terms_5542_; lean_object* v___x_5543_; 
v_full_5541_ = lean_ctor_get_uint8(v_snd_5536_, sizeof(void*)*5);
v_terms_5542_ = lean_ctor_get(v_snd_5536_, 1);
lean_inc_ref(v_terms_5542_);
lean_dec(v_snd_5536_);
v___x_5543_ = lean_box(0);
if (v_full_5541_ == 0)
{
lean_object* v_toCold_5544_; lean_object* v_options_5545_; uint8_t v_hasTrace_5546_; 
v_toCold_5544_ = lean_ctor_get(v___y_5525_, 0);
v_options_5545_ = lean_ctor_get(v_toCold_5544_, 2);
v_hasTrace_5546_ = lean_ctor_get_uint8(v_options_5545_, sizeof(void*)*1);
if (v_hasTrace_5546_ == 0)
{
lean_dec_ref(v_terms_5542_);
lean_del_object(v___x_5539_);
lean_dec(v_fst_5537_);
v_a_5529_ = v___x_5543_;
goto v___jp_5528_;
}
else
{
lean_object* v_inheritedTraceOptions_5547_; lean_object* v_cls_5548_; lean_object* v___x_5549_; uint8_t v___x_5550_; 
v_inheritedTraceOptions_5547_ = lean_ctor_get(v_toCold_5544_, 11);
v_cls_5548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_5549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7);
v___x_5550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5547_, v_options_5545_, v___x_5549_);
if (v___x_5550_ == 0)
{
lean_dec_ref(v_terms_5542_);
lean_del_object(v___x_5539_);
lean_dec(v_fst_5537_);
v_a_5529_ = v___x_5543_;
goto v___jp_5528_;
}
else
{
lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5556_; 
v___x_5551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__9);
v___x_5552_ = l_Nat_reprFast(v_fst_5537_);
v___x_5553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5553_, 0, v___x_5552_);
v___x_5554_ = l_Lean_MessageData_ofFormat(v___x_5553_);
if (v_isShared_5540_ == 0)
{
lean_ctor_set_tag(v___x_5539_, 7);
lean_ctor_set(v___x_5539_, 1, v___x_5554_);
lean_ctor_set(v___x_5539_, 0, v___x_5551_);
v___x_5556_ = v___x_5539_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
v___x_5557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___closed__1);
v___x_5558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5556_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
v___x_5559_ = lean_array_to_list(v_terms_5542_);
v___x_5560_ = lean_box(0);
v___x_5561_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__0(v___x_5559_, v___x_5560_);
v___x_5562_ = l_Lean_MessageData_ofList(v___x_5561_);
v___x_5563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5558_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
v___x_5564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2(v_cls_5548_, v___x_5563_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_dec_ref_known(v___x_5564_, 1);
v_a_5529_ = v___x_5543_;
goto v___jp_5528_;
}
else
{
return v___x_5564_;
}
}
}
}
}
else
{
lean_dec_ref(v_terms_5542_);
lean_del_object(v___x_5539_);
lean_dec(v_fst_5537_);
v_a_5529_ = v___x_5543_;
goto v___jp_5528_;
}
}
}
v___jp_5528_:
{
size_t v___x_5530_; size_t v___x_5531_; 
v___x_5530_ = ((size_t)1ULL);
v___x_5531_ = lean_usize_add(v_i_5521_, v___x_5530_);
v_i_5521_ = v___x_5531_;
v_b_5522_ = v_a_5529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0___boxed(lean_object* v_as_5567_, lean_object* v_sz_5568_, lean_object* v_i_5569_, lean_object* v_b_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
size_t v_sz_boxed_5576_; size_t v_i_boxed_5577_; lean_object* v_res_5578_; 
v_sz_boxed_5576_ = lean_unbox_usize(v_sz_5568_);
lean_dec(v_sz_5568_);
v_i_boxed_5577_ = lean_unbox_usize(v_i_5569_);
lean_dec(v_i_5569_);
v_res_5578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0(v_as_5567_, v_sz_boxed_5576_, v_i_boxed_5577_, v_b_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec_ref(v_as_5567_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets(lean_object* v_sets_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_){
_start:
{
lean_object* v_toCold_5589_; lean_object* v_options_5590_; uint8_t v_hasTrace_5591_; 
v_toCold_5589_ = lean_ctor_get(v_a_5583_, 0);
v_options_5590_ = lean_ctor_get(v_toCold_5589_, 2);
v_hasTrace_5591_ = lean_ctor_get_uint8(v_options_5590_, sizeof(void*)*1);
if (v_hasTrace_5591_ == 0)
{
lean_dec_ref(v_sets_5580_);
goto v___jp_5586_;
}
else
{
lean_object* v_inheritedTraceOptions_5592_; lean_object* v_cls_5593_; lean_object* v___x_5594_; uint8_t v___x_5595_; 
v_inheritedTraceOptions_5592_ = lean_ctor_get(v_toCold_5589_, 11);
v_cls_5593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__4));
v___x_5594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass___closed__7);
v___x_5595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5592_, v_options_5590_, v___x_5594_);
if (v___x_5595_ == 0)
{
lean_dec_ref(v_sets_5580_);
goto v___jp_5586_;
}
else
{
lean_object* v_classes_5596_; lean_object* v_size_5597_; lean_object* v_buckets_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5727_; 
v_classes_5596_ = lean_ctor_get(v_sets_5580_, 0);
lean_inc_ref(v_classes_5596_);
lean_dec_ref(v_sets_5580_);
v_size_5597_ = lean_ctor_get(v_classes_5596_, 0);
v_buckets_5598_ = lean_ctor_get(v_classes_5596_, 1);
v_isSharedCheck_5727_ = !lean_is_exclusive(v_classes_5596_);
if (v_isSharedCheck_5727_ == 0)
{
v___x_5600_ = v_classes_5596_;
v_isShared_5601_ = v_isSharedCheck_5727_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_buckets_5598_);
lean_inc(v_size_5597_);
lean_dec(v_classes_5596_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5727_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___f_5602_; lean_object* v___y_5604_; uint8_t v___y_5605_; lean_object* v___y_5606_; lean_object* v___y_5607_; lean_object* v_a_5608_; lean_object* v___y_5623_; uint8_t v___y_5624_; lean_object* v___y_5625_; lean_object* v___y_5626_; lean_object* v_a_5627_; lean_object* v___y_5637_; size_t v___y_5638_; uint8_t v___y_5639_; size_t v___y_5640_; lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v___y_5684_; lean_object* v___y_5701_; lean_object* v___y_5702_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v___y_5707_; lean_object* v___y_5708_; lean_object* v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5713_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; uint8_t v___x_5723_; 
v___f_5602_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___closed__0));
v___x_5720_ = lean_mk_empty_array_with_capacity(v_size_5597_);
lean_dec(v_size_5597_);
v___x_5721_ = lean_unsigned_to_nat(0u);
v___x_5722_ = lean_array_get_size(v_buckets_5598_);
v___x_5723_ = lean_nat_dec_lt(v___x_5721_, v___x_5722_);
if (v___x_5723_ == 0)
{
lean_dec_ref(v_buckets_5598_);
v___y_5713_ = v___x_5720_;
goto v___jp_5712_;
}
else
{
size_t v___x_5724_; size_t v___x_5725_; lean_object* v___x_5726_; 
v___x_5724_ = ((size_t)0ULL);
v___x_5725_ = lean_usize_of_nat(v___x_5722_);
v___x_5726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__3(v_buckets_5598_, v___x_5724_, v___x_5725_, v___x_5720_);
lean_dec_ref(v_buckets_5598_);
v___y_5713_ = v___x_5726_;
goto v___jp_5712_;
}
v___jp_5603_:
{
lean_object* v___x_5609_; double v___x_5610_; double v___x_5611_; double v___x_5612_; double v___x_5613_; double v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5618_; 
v___x_5609_ = lean_io_mono_nanos_now();
v___x_5610_ = lean_float_of_nat(v___y_5604_);
v___x_5611_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1, &l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis___closed__1);
v___x_5612_ = lean_float_div(v___x_5610_, v___x_5611_);
v___x_5613_ = lean_float_of_nat(v___x_5609_);
v___x_5614_ = lean_float_div(v___x_5613_, v___x_5611_);
v___x_5615_ = lean_box_float(v___x_5612_);
v___x_5616_ = lean_box_float(v___x_5614_);
if (v_isShared_5601_ == 0)
{
lean_ctor_set(v___x_5600_, 1, v___x_5616_);
lean_ctor_set(v___x_5600_, 0, v___x_5615_);
v___x_5618_ = v___x_5600_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v___x_5615_);
lean_ctor_set(v_reuseFailAlloc_5621_, 1, v___x_5616_);
v___x_5618_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; 
v___x_5619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5619_, 0, v_a_5608_);
lean_ctor_set(v___x_5619_, 1, v___x_5618_);
lean_inc_ref(v___y_5606_);
v___x_5620_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(v_cls_5593_, v_hasTrace_5591_, v___y_5606_, v_options_5590_, v___y_5605_, v___y_5607_, v___f_5602_, v___x_5619_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
return v___x_5620_;
}
}
v___jp_5622_:
{
lean_object* v___x_5628_; double v___x_5629_; double v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5628_ = lean_io_get_num_heartbeats();
v___x_5629_ = lean_float_of_nat(v___y_5623_);
v___x_5630_ = lean_float_of_nat(v___x_5628_);
v___x_5631_ = lean_box_float(v___x_5629_);
v___x_5632_ = lean_box_float(v___x_5630_);
v___x_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5631_);
lean_ctor_set(v___x_5633_, 1, v___x_5632_);
v___x_5634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5634_, 0, v_a_5627_);
lean_ctor_set(v___x_5634_, 1, v___x_5633_);
lean_inc_ref(v___y_5625_);
v___x_5635_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__8(v_cls_5593_, v_hasTrace_5591_, v___y_5625_, v_options_5590_, v___y_5624_, v___y_5626_, v___f_5602_, v___x_5634_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
return v___x_5635_;
}
v___jp_5636_:
{
lean_object* v___x_5643_; lean_object* v_a_5644_; lean_object* v___x_5645_; uint8_t v___x_5646_; 
v___x_5643_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__6___redArg(v_a_5584_);
v_a_5644_ = lean_ctor_get(v___x_5643_, 0);
lean_inc(v_a_5644_);
lean_dec_ref(v___x_5643_);
v___x_5645_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5646_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(v_options_5590_, v___x_5645_);
if (v___x_5646_ == 0)
{
lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5647_ = lean_io_mono_nanos_now();
v___x_5648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0(v___y_5642_, v___y_5640_, v___y_5638_, v___y_5637_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
lean_dec_ref(v___y_5642_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5655_; 
v_isSharedCheck_5655_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5655_ == 0)
{
lean_object* v_unused_5656_; 
v_unused_5656_ = lean_ctor_get(v___x_5648_, 0);
lean_dec(v_unused_5656_);
v___x_5650_ = v___x_5648_;
v_isShared_5651_ = v_isSharedCheck_5655_;
goto v_resetjp_5649_;
}
else
{
lean_dec(v___x_5648_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5655_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v___x_5653_; 
if (v_isShared_5651_ == 0)
{
lean_ctor_set_tag(v___x_5650_, 1);
lean_ctor_set(v___x_5650_, 0, v___y_5637_);
v___x_5653_ = v___x_5650_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v___y_5637_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
v___y_5604_ = v___x_5647_;
v___y_5605_ = v___y_5639_;
v___y_5606_ = v___y_5641_;
v___y_5607_ = v_a_5644_;
v_a_5608_ = v___x_5653_;
goto v___jp_5603_;
}
}
}
else
{
lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5664_; 
v_a_5657_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5664_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5664_ == 0)
{
v___x_5659_ = v___x_5648_;
v_isShared_5660_ = v_isSharedCheck_5664_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5648_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5664_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set_tag(v___x_5659_, 0);
v___x_5662_ = v___x_5659_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_a_5657_);
v___x_5662_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
v___y_5604_ = v___x_5647_;
v___y_5605_ = v___y_5639_;
v___y_5606_ = v___y_5641_;
v___y_5607_ = v_a_5644_;
v_a_5608_ = v___x_5662_;
goto v___jp_5603_;
}
}
}
}
else
{
lean_object* v___x_5665_; lean_object* v___x_5666_; 
lean_del_object(v___x_5600_);
v___x_5665_ = lean_io_get_num_heartbeats();
v___x_5666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0(v___y_5642_, v___y_5640_, v___y_5638_, v___y_5637_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
lean_dec_ref(v___y_5642_);
if (lean_obj_tag(v___x_5666_) == 0)
{
lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5673_ == 0)
{
lean_object* v_unused_5674_; 
v_unused_5674_ = lean_ctor_get(v___x_5666_, 0);
lean_dec(v_unused_5674_);
v___x_5668_ = v___x_5666_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_dec(v___x_5666_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
lean_ctor_set_tag(v___x_5668_, 1);
lean_ctor_set(v___x_5668_, 0, v___y_5637_);
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___y_5637_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
v___y_5623_ = v___x_5665_;
v___y_5624_ = v___y_5639_;
v___y_5625_ = v___y_5641_;
v___y_5626_ = v_a_5644_;
v_a_5627_ = v___x_5671_;
goto v___jp_5622_;
}
}
}
else
{
lean_object* v_a_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5682_; 
v_a_5675_ = lean_ctor_get(v___x_5666_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5677_ = v___x_5666_;
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_a_5675_);
lean_dec(v___x_5666_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
lean_object* v___x_5680_; 
if (v_isShared_5678_ == 0)
{
lean_ctor_set_tag(v___x_5677_, 0);
v___x_5680_ = v___x_5677_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_a_5675_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
v___y_5623_ = v___x_5665_;
v___y_5624_ = v___y_5639_;
v___y_5625_ = v___y_5641_;
v___y_5626_ = v_a_5644_;
v_a_5627_ = v___x_5680_;
goto v___jp_5622_;
}
}
}
}
}
v___jp_5683_:
{
lean_object* v___x_5685_; size_t v_sz_5686_; size_t v___x_5687_; lean_object* v___x_5688_; 
v___x_5685_ = lean_box(0);
v_sz_5686_ = lean_array_size(v___y_5684_);
v___x_5687_ = ((size_t)0ULL);
v___x_5688_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceClass_spec__2___closed__1));
if (v___x_5595_ == 0)
{
lean_object* v___x_5689_; uint8_t v___x_5690_; 
v___x_5689_ = l_Lean_trace_profiler;
v___x_5690_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_spec__7(v_options_5590_, v___x_5689_);
if (v___x_5690_ == 0)
{
lean_object* v___x_5691_; 
lean_del_object(v___x_5600_);
v___x_5691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets_spec__0(v___y_5684_, v_sz_5686_, v___x_5687_, v___x_5685_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
lean_dec_ref(v___y_5684_);
if (lean_obj_tag(v___x_5691_) == 0)
{
lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5698_; 
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5691_);
if (v_isSharedCheck_5698_ == 0)
{
lean_object* v_unused_5699_; 
v_unused_5699_ = lean_ctor_get(v___x_5691_, 0);
lean_dec(v_unused_5699_);
v___x_5693_ = v___x_5691_;
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
else
{
lean_dec(v___x_5691_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 0, v___x_5685_);
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v___x_5685_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
return v___x_5696_;
}
}
}
else
{
return v___x_5691_;
}
}
else
{
v___y_5637_ = v___x_5685_;
v___y_5638_ = v___x_5687_;
v___y_5639_ = v___x_5595_;
v___y_5640_ = v_sz_5686_;
v___y_5641_ = v___x_5688_;
v___y_5642_ = v___y_5684_;
goto v___jp_5636_;
}
}
else
{
v___y_5637_ = v___x_5685_;
v___y_5638_ = v___x_5687_;
v___y_5639_ = v___x_5595_;
v___y_5640_ = v_sz_5686_;
v___y_5641_ = v___x_5688_;
v___y_5642_ = v___y_5684_;
goto v___jp_5636_;
}
}
v___jp_5700_:
{
lean_object* v___x_5705_; 
v___x_5705_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_InstSets_0__Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceAnalysis_traceClasses_spec__1___redArg(v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
lean_dec(v___y_5704_);
lean_dec(v___y_5701_);
v___y_5684_ = v___x_5705_;
goto v___jp_5683_;
}
v___jp_5706_:
{
uint8_t v___x_5711_; 
v___x_5711_ = lean_nat_dec_le(v___y_5710_, v___y_5709_);
if (v___x_5711_ == 0)
{
lean_dec(v___y_5709_);
lean_inc(v___y_5710_);
v___y_5701_ = v___y_5707_;
v___y_5702_ = v___y_5708_;
v___y_5703_ = v___y_5710_;
v___y_5704_ = v___y_5710_;
goto v___jp_5700_;
}
else
{
v___y_5701_ = v___y_5707_;
v___y_5702_ = v___y_5708_;
v___y_5703_ = v___y_5710_;
v___y_5704_ = v___y_5709_;
goto v___jp_5700_;
}
}
v___jp_5712_:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; uint8_t v___x_5716_; 
v___x_5714_ = lean_array_get_size(v___y_5713_);
v___x_5715_ = lean_unsigned_to_nat(0u);
v___x_5716_ = lean_nat_dec_eq(v___x_5714_, v___x_5715_);
if (v___x_5716_ == 0)
{
lean_object* v___x_5717_; lean_object* v___x_5718_; uint8_t v___x_5719_; 
v___x_5717_ = lean_unsigned_to_nat(1u);
v___x_5718_ = lean_nat_sub(v___x_5714_, v___x_5717_);
v___x_5719_ = lean_nat_dec_le(v___x_5715_, v___x_5718_);
if (v___x_5719_ == 0)
{
lean_inc(v___x_5718_);
v___y_5707_ = v___x_5714_;
v___y_5708_ = v___y_5713_;
v___y_5709_ = v___x_5718_;
v___y_5710_ = v___x_5718_;
goto v___jp_5706_;
}
else
{
v___y_5707_ = v___x_5714_;
v___y_5708_ = v___y_5713_;
v___y_5709_ = v___x_5718_;
v___y_5710_ = v___x_5715_;
goto v___jp_5706_;
}
}
else
{
v___y_5684_ = v___y_5713_;
goto v___jp_5683_;
}
}
}
}
}
v___jp_5586_:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; 
v___x_5587_ = lean_box(0);
v___x_5588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5587_);
return v___x_5588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets___boxed(lean_object* v_sets_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l_Lean_Meta_Tactic_BVDecide_EPR_InstSets_traceSets(v_sets_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_);
lean_dec(v_a_5732_);
lean_dec_ref(v_a_5731_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
return v_res_5734_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_UnionFind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_UnionFind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstClass);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets_default);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedInstSets);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_UnionFind(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_UnionFind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.Tactic.SolveByElim
// Imports: public import Init.Data.Sum public import Lean.LabelAttribute public import Lean.Meta.Tactic.Backtrack public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Repeat public import Lean.Meta.Tactic.Symm public import Lean.Elab.Term
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_head___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveByElim"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 179, 43, 63, 49, 24, 32, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SolveByElim"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 124, 130, 51, 187, 220, 69, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(217, 20, 184, 114, 46, 152, 175, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 70, 43, 38, 54, 221, 118, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 139, 182, 61, 70, 53, 35, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 96, 167, 3, 193, 174, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 99, 190, 156, 65, 10, 108, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 198, 193, 11, 27, 150, 253, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 168, 148, 157, 214, 227, 227, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 34, 196, 227, 75, 22, 166, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 42, 156, 241, 147, 248, 49, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 159, 244, 240, 243, 215, 3, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1979843508) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 117, 78, 143, 26, 177, 227, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 86, 236, 87, 154, 213, 60, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 78, 242, 178, 10, 32, 62, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(167, 116, 242, 130, 86, 112, 31, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "trying to apply: "};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object*);
static const lean_ctor_object l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object*);
static const lean_ctor_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value;
static const lean_array_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`repeat1'` made no progress"};
static const lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 32, .m_data = "⏮️ starting over using `exfalso`"};
static const lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_solveByElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_solveByElim___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_solveByElim___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "It doesn't make sense to remove local hypotheses when using `only` without `*`."};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value),LEAN_SCALAR_PTR_LITERAL(16, 215, 57, 166, 49, 41, 228, 20)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value;
static const lean_array_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "It doesn't make sense to use `*` without `only`."};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_74_ = 0;
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_76_ = l_Lean_registerTraceClass(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
return v_res_78_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(32u);
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(32u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0);
v___x_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
lean_ctor_set(v___x_87_, 3, v___x_83_);
lean_ctor_set_usize(v___x_87_, 4, v___x_82_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_traceState_91_; lean_object* v_traces_92_; lean_object* v___x_93_; lean_object* v_traceState_94_; lean_object* v_env_95_; lean_object* v_nextMacroScope_96_; lean_object* v_ngen_97_; lean_object* v_auxDeclNGen_98_; lean_object* v_cache_99_; lean_object* v_messages_100_; lean_object* v_infoState_101_; lean_object* v_snapshotTasks_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_121_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_traceState_91_ = lean_ctor_get(v___x_90_, 4);
lean_inc_ref(v_traceState_91_);
lean_dec(v___x_90_);
v_traces_92_ = lean_ctor_get(v_traceState_91_, 0);
lean_inc_ref(v_traces_92_);
lean_dec_ref(v_traceState_91_);
v___x_93_ = lean_st_ref_take(v___y_88_);
v_traceState_94_ = lean_ctor_get(v___x_93_, 4);
v_env_95_ = lean_ctor_get(v___x_93_, 0);
v_nextMacroScope_96_ = lean_ctor_get(v___x_93_, 1);
v_ngen_97_ = lean_ctor_get(v___x_93_, 2);
v_auxDeclNGen_98_ = lean_ctor_get(v___x_93_, 3);
v_cache_99_ = lean_ctor_get(v___x_93_, 5);
v_messages_100_ = lean_ctor_get(v___x_93_, 6);
v_infoState_101_ = lean_ctor_get(v___x_93_, 7);
v_snapshotTasks_102_ = lean_ctor_get(v___x_93_, 8);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_121_ == 0)
{
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snapshotTasks_102_);
lean_inc(v_infoState_101_);
lean_inc(v_messages_100_);
lean_inc(v_cache_99_);
lean_inc(v_traceState_94_);
lean_inc(v_auxDeclNGen_98_);
lean_inc(v_ngen_97_);
lean_inc(v_nextMacroScope_96_);
lean_inc(v_env_95_);
lean_dec(v___x_93_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint64_t v_tid_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_119_; 
v_tid_106_ = lean_ctor_get_uint64(v_traceState_94_, sizeof(void*)*1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_traceState_94_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v_traceState_94_, 0);
lean_dec(v_unused_120_);
v___x_108_ = v_traceState_94_;
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_traceState_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_110_);
lean_ctor_set_uint64(v_reuseFailAlloc_118_, sizeof(void*)*1, v_tid_106_);
v___x_112_ = v_reuseFailAlloc_118_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_114_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 4, v___x_112_);
v___x_114_ = v___x_104_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_env_95_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_nextMacroScope_96_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_ngen_97_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_auxDeclNGen_98_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_117_, 5, v_cache_99_);
lean_ctor_set(v_reuseFailAlloc_117_, 6, v_messages_100_);
lean_ctor_set(v_reuseFailAlloc_117_, 7, v_infoState_101_);
lean_ctor_set(v_reuseFailAlloc_117_, 8, v_snapshotTasks_102_);
v___x_114_ = v_reuseFailAlloc_117_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_st_ref_put(v___y_88_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_traces_92_);
return v___x_116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_122_);
lean_dec(v___y_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
lean_object* v_name_139_; lean_object* v_defValue_140_; lean_object* v_map_141_; lean_object* v___x_142_; 
v_name_139_ = lean_ctor_get(v_opt_138_, 0);
v_defValue_140_ = lean_ctor_get(v_opt_138_, 1);
v_map_141_ = lean_ctor_get(v_opts_137_, 0);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_141_, v_name_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = lean_unbox(v_defValue_140_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; 
v_val_144_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_142_, 1);
if (lean_obj_tag(v_val_144_) == 1)
{
uint8_t v_v_145_; 
v_v_145_ = lean_ctor_get_uint8(v_val_144_, 0);
lean_dec_ref_known(v_val_144_, 0);
return v_v_145_;
}
else
{
uint8_t v___x_146_; 
lean_dec(v_val_144_);
v___x_146_ = lean_unbox(v_defValue_140_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_147_, v_opt_148_);
lean_dec_ref(v_opt_148_);
lean_dec_ref(v_opts_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_saveState___redArg(v___y_153_, v___y_155_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
v___x_159_ = lean_apply_5(v_x_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, lean_box(0));
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_a_158_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_198_; 
v_a_169_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_198_ == 0)
{
v___x_171_ = v___x_159_;
v_isShared_172_ = v_isSharedCheck_198_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_198_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___y_174_; uint8_t v___x_196_; 
v___x_196_ = l_Lean_Exception_isInterrupt(v_a_169_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_inc(v_a_169_);
v___x_197_ = l_Lean_Exception_isRuntime(v_a_169_);
v___y_174_ = v___x_197_;
goto v___jp_173_;
}
else
{
v___y_174_ = v___x_196_;
goto v___jp_173_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; 
lean_del_object(v___x_171_);
lean_dec(v_a_169_);
v___x_175_ = l_Lean_Meta_SavedState_restore___redArg(v_a_158_, v___y_153_, v___y_155_);
lean_dec(v_a_158_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_175_, 0);
lean_dec(v_unused_184_);
v___x_177_ = v___x_175_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_dec(v___x_175_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_175_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_175_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_a_158_);
if (v_isShared_172_ == 0)
{
v___x_194_ = v___x_171_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_169_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v_x_151_);
v_a_199_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_157_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_157_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_222_, lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_222_, v_x_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_233_, lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_241_ = l_Lean_MessageData_ofExpr(v_e_233_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_244_, lean_object* v_x_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v_x_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_252_, uint8_t v___x_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_x_255_);
return v___x_261_;
}
else
{
lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_287_; 
v_head_262_ = lean_ctor_get(v_x_254_, 0);
v_tail_263_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_287_ == 0)
{
v___x_265_ = v_x_254_;
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_tail_263_);
lean_inc(v_head_262_);
lean_dec(v_x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v_a_268_; lean_object* v___x_274_; 
lean_inc(v_head_262_);
v___x_274_ = l_Lean_MVarId_inferInstance(v_head_262_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_dec_ref_known(v___x_274_, 1);
v_a_268_ = v___x_252_;
goto v___jp_267_;
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_286_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_286_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v___y_280_; uint8_t v___x_284_; 
v___x_284_ = l_Lean_Exception_isInterrupt(v_a_275_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc(v_a_275_);
v___x_285_ = l_Lean_Exception_isRuntime(v_a_275_);
v___y_280_ = v___x_285_;
goto v___jp_279_;
}
else
{
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
lean_del_object(v___x_277_);
lean_dec(v_a_275_);
v_a_268_ = v___x_253_;
goto v___jp_267_;
}
else
{
lean_object* v___x_282_; 
lean_del_object(v___x_265_);
lean_dec(v_tail_263_);
lean_dec(v_head_262_);
lean_dec(v_x_255_);
if (v_isShared_278_ == 0)
{
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_275_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
v___jp_267_:
{
if (v_a_268_ == 0)
{
lean_del_object(v___x_265_);
lean_dec(v_head_262_);
v_x_254_ = v_tail_263_;
goto _start;
}
else
{
lean_object* v___x_271_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_x_255_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_head_262_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_x_255_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v_x_254_ = v_tail_263_;
v_x_255_ = v___x_271_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_12932__boxed_297_; uint8_t v___x_12933__boxed_298_; lean_object* v_res_299_; 
v___x_12932__boxed_297_ = lean_unbox(v___x_288_);
v___x_12933__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_12932__boxed_297_, v___x_12933__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_mctx_309_; lean_object* v_lctx_310_; lean_object* v_options_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_302_);
v_mctx_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_309_);
lean_dec(v___x_308_);
v_lctx_310_ = lean_ctor_get(v___y_301_, 2);
v_options_311_ = lean_ctor_get(v___y_303_, 2);
lean_inc_ref(v_options_311_);
lean_inc_ref(v_lctx_310_);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_env_307_);
lean_ctor_set(v___x_312_, 1, v_mctx_309_);
lean_ctor_set(v___x_312_, 2, v_lctx_310_);
lean_ctor_set(v___x_312_, 3, v_options_311_);
v___x_313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_msgData_300_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_322_, size_t v_i_323_, lean_object* v_bs_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_325_ == 0)
{
return v_bs_324_;
}
else
{
lean_object* v_v_326_; lean_object* v_msg_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_v_326_ = lean_array_uget_borrowed(v_bs_324_, v_i_323_);
v_msg_327_ = lean_ctor_get(v_v_326_, 1);
lean_inc_ref(v_msg_327_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_324_, v_i_323_, v___x_328_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_323_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_329_, v_i_323_, v_msg_327_);
v_i_323_ = v___x_331_;
v_bs_324_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_bs_336_){
_start:
{
size_t v_sz_boxed_337_; size_t v_i_boxed_338_; lean_object* v_res_339_; 
v_sz_boxed_337_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_337_, v_i_boxed_338_, v_bs_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_340_, lean_object* v_data_341_, lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_fileName_349_; lean_object* v_fileMap_350_; lean_object* v_options_351_; lean_object* v_currRecDepth_352_; lean_object* v_maxRecDepth_353_; lean_object* v_ref_354_; lean_object* v_currNamespace_355_; lean_object* v_openDecls_356_; lean_object* v_initHeartbeats_357_; lean_object* v_maxHeartbeats_358_; lean_object* v_quotContext_359_; lean_object* v_currMacroScope_360_; uint8_t v_diag_361_; lean_object* v_cancelTk_x3f_362_; uint8_t v_suppressElabErrors_363_; lean_object* v_inheritedTraceOptions_364_; lean_object* v___x_365_; lean_object* v_traceState_366_; lean_object* v_traces_367_; lean_object* v_ref_368_; lean_object* v___x_369_; lean_object* v___x_370_; size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; lean_object* v_msg_374_; lean_object* v___x_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_413_; 
v_fileName_349_ = lean_ctor_get(v___y_346_, 0);
v_fileMap_350_ = lean_ctor_get(v___y_346_, 1);
v_options_351_ = lean_ctor_get(v___y_346_, 2);
v_currRecDepth_352_ = lean_ctor_get(v___y_346_, 3);
v_maxRecDepth_353_ = lean_ctor_get(v___y_346_, 4);
v_ref_354_ = lean_ctor_get(v___y_346_, 5);
v_currNamespace_355_ = lean_ctor_get(v___y_346_, 6);
v_openDecls_356_ = lean_ctor_get(v___y_346_, 7);
v_initHeartbeats_357_ = lean_ctor_get(v___y_346_, 8);
v_maxHeartbeats_358_ = lean_ctor_get(v___y_346_, 9);
v_quotContext_359_ = lean_ctor_get(v___y_346_, 10);
v_currMacroScope_360_ = lean_ctor_get(v___y_346_, 11);
v_diag_361_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*14);
v_cancelTk_x3f_362_ = lean_ctor_get(v___y_346_, 12);
v_suppressElabErrors_363_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_364_ = lean_ctor_get(v___y_346_, 13);
v___x_365_ = lean_st_ref_get(v___y_347_);
v_traceState_366_ = lean_ctor_get(v___x_365_, 4);
lean_inc_ref(v_traceState_366_);
lean_dec(v___x_365_);
v_traces_367_ = lean_ctor_get(v_traceState_366_, 0);
lean_inc_ref(v_traces_367_);
lean_dec_ref(v_traceState_366_);
v_ref_368_ = l_Lean_replaceRef(v_ref_342_, v_ref_354_);
lean_inc_ref(v_inheritedTraceOptions_364_);
lean_inc(v_cancelTk_x3f_362_);
lean_inc(v_currMacroScope_360_);
lean_inc(v_quotContext_359_);
lean_inc(v_maxHeartbeats_358_);
lean_inc(v_initHeartbeats_357_);
lean_inc(v_openDecls_356_);
lean_inc(v_currNamespace_355_);
lean_inc(v_maxRecDepth_353_);
lean_inc(v_currRecDepth_352_);
lean_inc_ref(v_options_351_);
lean_inc_ref(v_fileMap_350_);
lean_inc_ref(v_fileName_349_);
v___x_369_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_369_, 0, v_fileName_349_);
lean_ctor_set(v___x_369_, 1, v_fileMap_350_);
lean_ctor_set(v___x_369_, 2, v_options_351_);
lean_ctor_set(v___x_369_, 3, v_currRecDepth_352_);
lean_ctor_set(v___x_369_, 4, v_maxRecDepth_353_);
lean_ctor_set(v___x_369_, 5, v_ref_368_);
lean_ctor_set(v___x_369_, 6, v_currNamespace_355_);
lean_ctor_set(v___x_369_, 7, v_openDecls_356_);
lean_ctor_set(v___x_369_, 8, v_initHeartbeats_357_);
lean_ctor_set(v___x_369_, 9, v_maxHeartbeats_358_);
lean_ctor_set(v___x_369_, 10, v_quotContext_359_);
lean_ctor_set(v___x_369_, 11, v_currMacroScope_360_);
lean_ctor_set(v___x_369_, 12, v_cancelTk_x3f_362_);
lean_ctor_set(v___x_369_, 13, v_inheritedTraceOptions_364_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*14, v_diag_361_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*14 + 1, v_suppressElabErrors_363_);
v___x_370_ = l_Lean_PersistentArray_toArray___redArg(v_traces_367_);
lean_dec_ref(v_traces_367_);
v_sz_371_ = lean_array_size(v___x_370_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_371_, v___x_372_, v___x_370_);
v_msg_374_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_374_, 0, v_data_341_);
lean_ctor_set(v_msg_374_, 1, v_msg_343_);
lean_ctor_set(v_msg_374_, 2, v___x_373_);
v___x_375_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_374_, v___y_344_, v___y_345_, v___x_369_, v___y_347_);
lean_dec_ref_known(v___x_369_, 14);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_413_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_413_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_413_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v_traceState_381_; lean_object* v_env_382_; lean_object* v_nextMacroScope_383_; lean_object* v_ngen_384_; lean_object* v_auxDeclNGen_385_; lean_object* v_cache_386_; lean_object* v_messages_387_; lean_object* v_infoState_388_; lean_object* v_snapshotTasks_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_412_; 
v___x_380_ = lean_st_ref_take(v___y_347_);
v_traceState_381_ = lean_ctor_get(v___x_380_, 4);
v_env_382_ = lean_ctor_get(v___x_380_, 0);
v_nextMacroScope_383_ = lean_ctor_get(v___x_380_, 1);
v_ngen_384_ = lean_ctor_get(v___x_380_, 2);
v_auxDeclNGen_385_ = lean_ctor_get(v___x_380_, 3);
v_cache_386_ = lean_ctor_get(v___x_380_, 5);
v_messages_387_ = lean_ctor_get(v___x_380_, 6);
v_infoState_388_ = lean_ctor_get(v___x_380_, 7);
v_snapshotTasks_389_ = lean_ctor_get(v___x_380_, 8);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_412_ == 0)
{
v___x_391_ = v___x_380_;
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snapshotTasks_389_);
lean_inc(v_infoState_388_);
lean_inc(v_messages_387_);
lean_inc(v_cache_386_);
lean_inc(v_traceState_381_);
lean_inc(v_auxDeclNGen_385_);
lean_inc(v_ngen_384_);
lean_inc(v_nextMacroScope_383_);
lean_inc(v_env_382_);
lean_dec(v___x_380_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint64_t v_tid_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_410_; 
v_tid_393_ = lean_ctor_get_uint64(v_traceState_381_, sizeof(void*)*1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_traceState_381_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_traceState_381_, 0);
lean_dec(v_unused_411_);
v___x_395_ = v_traceState_381_;
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_traceState_381_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_ref_342_);
lean_ctor_set(v___x_397_, 1, v_a_376_);
v___x_398_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_340_, v___x_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_398_);
lean_ctor_set_uint64(v_reuseFailAlloc_409_, sizeof(void*)*1, v_tid_393_);
v___x_400_ = v_reuseFailAlloc_409_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_400_);
v___x_402_ = v___x_391_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_env_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_cache_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_messages_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_infoState_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_snapshotTasks_389_);
v___x_402_ = v_reuseFailAlloc_408_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_st_ref_put(v___y_347_, v___x_402_);
v___x_404_ = lean_box(0);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_404_);
v___x_406_ = v___x_378_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_414_, lean_object* v_data_415_, lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_414_, v_data_415_, v_ref_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_424_){
_start:
{
if (lean_obj_tag(v_e_424_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 2;
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_427_);
lean_dec_ref(v_e_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_430_, lean_object* v_opt_431_){
_start:
{
lean_object* v_name_432_; lean_object* v_defValue_433_; lean_object* v_map_434_; lean_object* v___x_435_; 
v_name_432_ = lean_ctor_get(v_opt_431_, 0);
v_defValue_433_ = lean_ctor_get(v_opt_431_, 1);
v_map_434_ = lean_ctor_get(v_opts_430_, 0);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_434_, v_name_432_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_inc(v_defValue_433_);
return v_defValue_433_;
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
if (lean_obj_tag(v_val_436_) == 3)
{
lean_object* v_v_437_; 
v_v_437_ = lean_ctor_get(v_val_436_, 0);
lean_inc(v_v_437_);
lean_dec_ref_known(v_val_436_, 1);
return v_v_437_;
}
else
{
lean_dec(v_val_436_);
lean_inc(v_defValue_433_);
return v_defValue_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_438_, lean_object* v_opt_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_438_, v_opt_439_);
lean_dec_ref(v_opt_439_);
lean_dec_ref(v_opts_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v_x_441_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v_x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v_x_441_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_x_441_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 0);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_459_);
return v_res_461_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_462_; double v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_float_of_nat(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_467_; double v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1000u);
v___x_468_ = lean_float_of_nat(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_469_, uint8_t v_collapsed_470_, lean_object* v_tag_471_, lean_object* v_opts_472_, uint8_t v_clsEnabled_473_, lean_object* v_oldTraces_474_, lean_object* v_msg_475_, lean_object* v_resStartStop_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v_data_487_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___y_503_; lean_object* v_a_504_; uint8_t v___y_519_; double v___y_550_; 
v_fst_482_ = lean_ctor_get(v_resStartStop_476_, 0);
lean_inc(v_fst_482_);
v_snd_483_ = lean_ctor_get(v_resStartStop_476_, 1);
lean_inc(v_snd_483_);
lean_dec_ref(v_resStartStop_476_);
v_fst_498_ = lean_ctor_get(v_snd_483_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v_snd_483_, 1);
lean_inc(v_snd_499_);
lean_dec(v_snd_483_);
v___x_500_ = l_Lean_trace_profiler;
v___x_501_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_472_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_519_ = v___x_501_;
goto v___jp_518_;
}
else
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = l_Lean_trace_profiler_useHeartbeats;
v___x_556_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_472_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; double v___x_559_; double v___x_560_; double v___x_561_; 
v___x_557_ = l_Lean_trace_profiler_threshold;
v___x_558_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_472_, v___x_557_);
v___x_559_ = lean_float_of_nat(v___x_558_);
v___x_560_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_561_ = lean_float_div(v___x_559_, v___x_560_);
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; double v___x_564_; 
v___x_562_ = l_Lean_trace_profiler_threshold;
v___x_563_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_472_, v___x_562_);
v___x_564_ = lean_float_of_nat(v___x_563_);
v___y_550_ = v___x_564_;
goto v___jp_549_;
}
}
v___jp_484_:
{
lean_object* v___x_488_; 
lean_inc(v___y_486_);
v___x_488_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_474_, v_data_487_, v___y_486_, v___y_485_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; 
lean_dec_ref_known(v___x_488_, 1);
v___x_489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_482_);
return v___x_489_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_fst_482_);
v_a_490_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_488_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
v___jp_502_:
{
uint8_t v_result_505_; lean_object* v___x_506_; lean_object* v___x_507_; double v___x_508_; lean_object* v_data_509_; 
v_result_505_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_482_);
v___x_506_ = lean_box(v_result_505_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
v___x_508_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_471_);
lean_inc_ref(v___x_507_);
lean_inc(v_cls_469_);
v_data_509_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_509_, 0, v_cls_469_);
lean_ctor_set(v_data_509_, 1, v___x_507_);
lean_ctor_set(v_data_509_, 2, v_tag_471_);
lean_ctor_set_float(v_data_509_, sizeof(void*)*3, v___x_508_);
lean_ctor_set_float(v_data_509_, sizeof(void*)*3 + 8, v___x_508_);
lean_ctor_set_uint8(v_data_509_, sizeof(void*)*3 + 16, v_collapsed_470_);
if (v___x_501_ == 0)
{
lean_dec_ref_known(v___x_507_, 1);
lean_dec(v_snd_499_);
lean_dec(v_fst_498_);
lean_dec_ref(v_tag_471_);
lean_dec(v_cls_469_);
v___y_485_ = v_a_504_;
v___y_486_ = v___y_503_;
v_data_487_ = v_data_509_;
goto v___jp_484_;
}
else
{
lean_object* v_data_510_; double v___x_511_; double v___x_512_; 
lean_dec_ref_known(v_data_509_, 3);
v_data_510_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_510_, 0, v_cls_469_);
lean_ctor_set(v_data_510_, 1, v___x_507_);
lean_ctor_set(v_data_510_, 2, v_tag_471_);
v___x_511_ = lean_unbox_float(v_fst_498_);
lean_dec(v_fst_498_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3, v___x_511_);
v___x_512_ = lean_unbox_float(v_snd_499_);
lean_dec(v_snd_499_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3 + 8, v___x_512_);
lean_ctor_set_uint8(v_data_510_, sizeof(void*)*3 + 16, v_collapsed_470_);
v___y_485_ = v_a_504_;
v___y_486_ = v___y_503_;
v_data_487_ = v_data_510_;
goto v___jp_484_;
}
}
v___jp_513_:
{
lean_object* v_ref_514_; lean_object* v___x_515_; 
v_ref_514_ = lean_ctor_get(v___y_479_, 5);
lean_inc(v___y_480_);
lean_inc_ref(v___y_479_);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
lean_inc(v_fst_482_);
v___x_515_ = lean_apply_6(v_msg_475_, v_fst_482_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, lean_box(0));
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___y_503_ = v_ref_514_;
v_a_504_ = v_a_516_;
goto v___jp_502_;
}
else
{
lean_object* v___x_517_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_503_ = v_ref_514_;
v_a_504_ = v___x_517_;
goto v___jp_502_;
}
}
v___jp_518_:
{
if (v_clsEnabled_473_ == 0)
{
if (v___y_519_ == 0)
{
lean_object* v___x_520_; lean_object* v_traceState_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_cache_526_; lean_object* v_messages_527_; lean_object* v_infoState_528_; lean_object* v_snapshotTasks_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_snd_499_);
lean_dec(v_fst_498_);
lean_dec_ref(v_msg_475_);
lean_dec_ref(v_tag_471_);
lean_dec(v_cls_469_);
v___x_520_ = lean_st_ref_take(v___y_480_);
v_traceState_521_ = lean_ctor_get(v___x_520_, 4);
v_env_522_ = lean_ctor_get(v___x_520_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_520_, 1);
v_ngen_524_ = lean_ctor_get(v___x_520_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_520_, 3);
v_cache_526_ = lean_ctor_get(v___x_520_, 5);
v_messages_527_ = lean_ctor_get(v___x_520_, 6);
v_infoState_528_ = lean_ctor_get(v___x_520_, 7);
v_snapshotTasks_529_ = lean_ctor_get(v___x_520_, 8);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_548_ == 0)
{
v___x_531_ = v___x_520_;
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snapshotTasks_529_);
lean_inc(v_infoState_528_);
lean_inc(v_messages_527_);
lean_inc(v_cache_526_);
lean_inc(v_traceState_521_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_520_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint64_t v_tid_533_; lean_object* v_traces_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_547_; 
v_tid_533_ = lean_ctor_get_uint64(v_traceState_521_, sizeof(void*)*1);
v_traces_534_ = lean_ctor_get(v_traceState_521_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_traceState_521_);
if (v_isSharedCheck_547_ == 0)
{
v___x_536_ = v_traceState_521_;
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_traces_534_);
lean_dec(v_traceState_521_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_474_, v_traces_534_);
lean_dec_ref(v_traces_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_538_);
lean_ctor_set_uint64(v_reuseFailAlloc_546_, sizeof(void*)*1, v_tid_533_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v___x_540_);
v___x_542_ = v___x_531_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_env_522_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_messages_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_infoState_528_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_snapshotTasks_529_);
v___x_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_st_ref_put(v___y_480_, v___x_542_);
v___x_544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_482_);
return v___x_544_;
}
}
}
}
}
else
{
goto v___jp_513_;
}
}
else
{
goto v___jp_513_;
}
}
v___jp_549_:
{
double v___x_551_; double v___x_552_; double v___x_553_; uint8_t v___x_554_; 
v___x_551_ = lean_unbox_float(v_snd_499_);
v___x_552_ = lean_unbox_float(v_fst_498_);
v___x_553_ = lean_float_sub(v___x_551_, v___x_552_);
v___x_554_ = lean_float_decLt(v___y_550_, v___x_553_);
v___y_519_ = v___x_554_;
goto v___jp_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_565_, lean_object* v_collapsed_566_, lean_object* v_tag_567_, lean_object* v_opts_568_, lean_object* v_clsEnabled_569_, lean_object* v_oldTraces_570_, lean_object* v_msg_571_, lean_object* v_resStartStop_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v_collapsed_boxed_578_; uint8_t v_clsEnabled_boxed_579_; lean_object* v_res_580_; 
v_collapsed_boxed_578_ = lean_unbox(v_collapsed_566_);
v_clsEnabled_boxed_579_ = lean_unbox(v_clsEnabled_569_);
v_res_580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_565_, v_collapsed_boxed_578_, v_tag_567_, v_opts_568_, v_clsEnabled_boxed_579_, v_oldTraces_570_, v_msg_571_, v_resStartStop_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_opts_568_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_x_583_);
return v___x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_head_590_ = lean_ctor_get(v_x_582_, 0);
v_tail_591_ = lean_ctor_get(v_x_582_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v_x_582_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_head_590_);
lean_dec(v_x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
lean_inc(v_head_590_);
v___x_595_ = l_Lean_MVarId_inferInstance(v_head_590_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_dec_ref_known(v___x_595_, 1);
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
v_x_582_ = v_tail_591_;
goto _start;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_613_; 
v_a_597_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_613_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_613_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_613_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___y_602_; uint8_t v___x_611_; 
v___x_611_ = l_Lean_Exception_isInterrupt(v_a_597_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
lean_inc(v_a_597_);
v___x_612_ = l_Lean_Exception_isRuntime(v_a_597_);
v___y_602_ = v___x_612_;
goto v___jp_601_;
}
else
{
v___y_602_ = v___x_611_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
if (v___x_581_ == 0)
{
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
v_x_582_ = v_tail_591_;
goto _start;
}
else
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_x_583_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_head_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_x_583_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_x_582_ = v_tail_591_;
v_x_583_ = v___x_605_;
goto _start;
}
}
}
else
{
lean_object* v___x_609_; 
lean_del_object(v___x_593_);
lean_dec(v_tail_591_);
lean_dec(v_head_590_);
lean_dec(v_x_583_);
if (v_isShared_600_ == 0)
{
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_597_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_13357__boxed_623_; lean_object* v_res_624_; 
v___x_13357__boxed_623_ = lean_unbox(v___x_615_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_13357__boxed_623_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_x_627_);
return v___x_633_;
}
else
{
lean_object* v_head_634_; lean_object* v_tail_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_658_; 
v_head_634_ = lean_ctor_get(v_x_626_, 0);
v_tail_635_ = lean_ctor_get(v_x_626_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_658_ == 0)
{
v___x_637_ = v_x_626_;
v_isShared_638_ = v_isSharedCheck_658_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_tail_635_);
lean_inc(v_head_634_);
lean_dec(v_x_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_658_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_644_; 
lean_inc(v_head_634_);
v___x_644_ = l_Lean_MVarId_inferInstance(v_head_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref_known(v___x_644_, 1);
if (v___x_625_ == 0)
{
lean_del_object(v___x_637_);
lean_dec(v_head_634_);
v_x_626_ = v_tail_635_;
goto _start;
}
else
{
goto v___jp_639_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_a_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___y_651_; uint8_t v___x_655_; 
v___x_655_ = l_Lean_Exception_isInterrupt(v_a_646_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
lean_inc(v_a_646_);
v___x_656_ = l_Lean_Exception_isRuntime(v_a_646_);
v___y_651_ = v___x_656_;
goto v___jp_650_;
}
else
{
v___y_651_ = v___x_655_;
goto v___jp_650_;
}
v___jp_650_:
{
if (v___y_651_ == 0)
{
lean_del_object(v___x_648_);
lean_dec(v_a_646_);
goto v___jp_639_;
}
else
{
lean_object* v___x_653_; 
lean_del_object(v___x_637_);
lean_dec(v_tail_635_);
lean_dec(v_head_634_);
lean_dec(v_x_627_);
if (v_isShared_649_ == 0)
{
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_646_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
v___jp_639_:
{
lean_object* v___x_641_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_627_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_head_634_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_x_627_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v_x_626_ = v_tail_635_;
v_x_627_ = v___x_641_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_13434__boxed_667_; lean_object* v_res_668_; 
v___x_13434__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_13434__boxed_667_, v_x_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_668_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_672_; double v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(1000000000u);
v___x_673_ = lean_float_of_nat(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_674_, lean_object* v_g_675_, lean_object* v_e_676_, lean_object* v_cfg_677_, lean_object* v___x_678_, lean_object* v___x_679_, uint8_t v___x_680_, lean_object* v___x_681_, lean_object* v___f_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_options_688_; uint8_t v_hasTrace_689_; 
v_options_688_ = lean_ctor_get(v___y_685_, 2);
v_hasTrace_689_ = lean_ctor_get_uint8(v_options_688_, sizeof(void*)*1);
if (v_hasTrace_689_ == 0)
{
lean_object* v_keyedConfig_690_; uint8_t v_trackZetaDelta_691_; lean_object* v_zetaDeltaSet_692_; lean_object* v_lctx_693_; lean_object* v_localInstances_694_; lean_object* v_defEqCtx_x3f_695_; lean_object* v_synthPendingDepth_696_; lean_object* v_customCanUnfoldPredicate_x3f_697_; uint8_t v_univApprox_698_; uint8_t v_inTypeClassResolution_699_; uint8_t v_cacheInferType_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v_keyedConfig_690_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_691_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_692_ = lean_ctor_get(v___y_683_, 1);
v_lctx_693_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_694_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_695_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_696_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_697_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_698_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_699_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_700_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_690_);
v___x_701_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_690_);
lean_inc(v_customCanUnfoldPredicate_x3f_697_);
lean_inc(v_synthPendingDepth_696_);
lean_inc(v_defEqCtx_x3f_695_);
lean_inc_ref(v_localInstances_694_);
lean_inc_ref(v_lctx_693_);
lean_inc(v_zetaDeltaSet_692_);
v___x_702_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v_zetaDeltaSet_692_);
lean_ctor_set(v___x_702_, 2, v_lctx_693_);
lean_ctor_set(v___x_702_, 3, v_localInstances_694_);
lean_ctor_set(v___x_702_, 4, v_defEqCtx_x3f_695_);
lean_ctor_set(v___x_702_, 5, v_synthPendingDepth_696_);
lean_ctor_set(v___x_702_, 6, v_customCanUnfoldPredicate_x3f_697_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7, v_trackZetaDelta_691_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7 + 1, v_univApprox_698_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7 + 2, v_inTypeClassResolution_699_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7 + 3, v_cacheInferType_700_);
v___x_703_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_702_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_702_, 7);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_box(0);
v___x_706_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_689_, v_a_704_, v___x_705_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_List_reverse___redArg(v_a_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
return v___x_706_;
}
}
else
{
lean_dec_ref(v___y_683_);
return v___x_703_;
}
}
else
{
lean_object* v_inheritedTraceOptions_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v_a_723_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v_a_738_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v_a_756_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v_a_768_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; 
v_inheritedTraceOptions_716_ = lean_ctor_get(v___y_685_, 13);
v___x_717_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_679_);
v___x_718_ = l_Lean_Name_append(v___x_717_, v___x_679_);
v___x_719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_716_, v_options_688_, v___x_718_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_Lean_trace_profiler;
v___x_829_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v_keyedConfig_830_; uint8_t v_trackZetaDelta_831_; lean_object* v_zetaDeltaSet_832_; lean_object* v_lctx_833_; lean_object* v_localInstances_834_; lean_object* v_defEqCtx_x3f_835_; lean_object* v_synthPendingDepth_836_; lean_object* v_customCanUnfoldPredicate_x3f_837_; uint8_t v_univApprox_838_; uint8_t v_inTypeClassResolution_839_; uint8_t v_cacheInferType_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v_keyedConfig_830_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_831_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_832_ = lean_ctor_get(v___y_683_, 1);
v_lctx_833_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_834_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_835_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_836_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_837_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_838_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_839_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_840_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_830_);
v___x_841_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_830_);
lean_inc(v_customCanUnfoldPredicate_x3f_837_);
lean_inc(v_synthPendingDepth_836_);
lean_inc(v_defEqCtx_x3f_835_);
lean_inc_ref(v_localInstances_834_);
lean_inc_ref(v_lctx_833_);
lean_inc(v_zetaDeltaSet_832_);
v___x_842_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_zetaDeltaSet_832_);
lean_ctor_set(v___x_842_, 2, v_lctx_833_);
lean_ctor_set(v___x_842_, 3, v_localInstances_834_);
lean_ctor_set(v___x_842_, 4, v_defEqCtx_x3f_835_);
lean_ctor_set(v___x_842_, 5, v_synthPendingDepth_836_);
lean_ctor_set(v___x_842_, 6, v_customCanUnfoldPredicate_x3f_837_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7, v_trackZetaDelta_831_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7 + 1, v_univApprox_838_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7 + 2, v_inTypeClassResolution_839_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7 + 3, v_cacheInferType_840_);
v___x_843_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_842_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_842_, 7);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = lean_box(0);
v___x_846_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_829_, v_hasTrace_689_, v_a_844_, v___x_845_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_855_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = l_List_reverse___redArg(v_a_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
return v___x_846_;
}
}
else
{
lean_dec_ref(v___y_683_);
return v___x_843_;
}
}
else
{
goto v___jp_783_;
}
}
else
{
goto v___jp_783_;
}
v___jp_720_:
{
lean_object* v___x_724_; double v___x_725_; double v___x_726_; double v___x_727_; double v___x_728_; double v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_724_ = lean_io_mono_nanos_now();
v___x_725_ = lean_float_of_nat(v___y_722_);
v___x_726_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_727_ = lean_float_div(v___x_725_, v___x_726_);
v___x_728_ = lean_float_of_nat(v___x_724_);
v___x_729_ = lean_float_div(v___x_728_, v___x_726_);
v___x_730_ = lean_box_float(v___x_727_);
v___x_731_ = lean_box_float(v___x_729_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_723_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_719_, v___y_721_, v___f_682_, v___x_733_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
return v___x_734_;
}
v___jp_735_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_a_738_);
v___y_721_ = v___y_736_;
v___y_722_ = v___y_737_;
v_a_723_ = v___x_739_;
goto v___jp_720_;
}
v___jp_740_:
{
if (lean_obj_tag(v___y_743_) == 0)
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v___y_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___y_743_, 1);
v___y_736_ = v___y_741_;
v___y_737_ = v___y_742_;
v_a_738_ = v_a_744_;
goto v___jp_735_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___y_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___y_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___y_743_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___y_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v___y_721_ = v___y_741_;
v___y_722_ = v___y_742_;
v_a_723_ = v___x_750_;
goto v___jp_720_;
}
}
}
}
v___jp_753_:
{
lean_object* v___x_757_; double v___x_758_; double v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_757_ = lean_io_get_num_heartbeats();
v___x_758_ = lean_float_of_nat(v___y_755_);
v___x_759_ = lean_float_of_nat(v___x_757_);
v___x_760_ = lean_box_float(v___x_758_);
v___x_761_ = lean_box_float(v___x_759_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_a_756_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_719_, v___y_754_, v___f_682_, v___x_763_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
return v___x_764_;
}
v___jp_765_:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_a_768_);
v___y_754_ = v___y_766_;
v___y_755_ = v___y_767_;
v_a_756_ = v___x_769_;
goto v___jp_753_;
}
v___jp_770_:
{
if (lean_obj_tag(v___y_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___y_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___y_773_, 1);
v___y_766_ = v___y_771_;
v___y_767_ = v___y_772_;
v_a_768_ = v_a_774_;
goto v___jp_765_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___y_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___y_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___y_773_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___y_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 0);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
v___y_754_ = v___y_771_;
v___y_755_ = v___y_772_;
v_a_756_ = v___x_780_;
goto v___jp_753_;
}
}
}
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_686_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v___x_786_ = l_Lean_trace_profiler_useHeartbeats;
v___x_787_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v_keyedConfig_789_; uint8_t v_trackZetaDelta_790_; lean_object* v_zetaDeltaSet_791_; lean_object* v_lctx_792_; lean_object* v_localInstances_793_; lean_object* v_defEqCtx_x3f_794_; lean_object* v_synthPendingDepth_795_; lean_object* v_customCanUnfoldPredicate_x3f_796_; uint8_t v_univApprox_797_; uint8_t v_inTypeClassResolution_798_; uint8_t v_cacheInferType_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_788_ = lean_io_mono_nanos_now();
v_keyedConfig_789_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_790_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_791_ = lean_ctor_get(v___y_683_, 1);
v_lctx_792_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_793_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_794_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_795_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_796_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_797_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_798_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_799_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_789_);
v___x_800_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_789_);
lean_inc(v_customCanUnfoldPredicate_x3f_796_);
lean_inc(v_synthPendingDepth_795_);
lean_inc(v_defEqCtx_x3f_794_);
lean_inc_ref(v_localInstances_793_);
lean_inc_ref(v_lctx_792_);
lean_inc(v_zetaDeltaSet_791_);
v___x_801_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_zetaDeltaSet_791_);
lean_ctor_set(v___x_801_, 2, v_lctx_792_);
lean_ctor_set(v___x_801_, 3, v_localInstances_793_);
lean_ctor_set(v___x_801_, 4, v_defEqCtx_x3f_794_);
lean_ctor_set(v___x_801_, 5, v_synthPendingDepth_795_);
lean_ctor_set(v___x_801_, 6, v_customCanUnfoldPredicate_x3f_796_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7, v_trackZetaDelta_790_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7 + 1, v_univApprox_797_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7 + 2, v_inTypeClassResolution_798_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7 + 3, v_cacheInferType_799_);
v___x_802_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_801_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_801_, 7);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_box(0);
v___x_805_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_787_, v_hasTrace_689_, v_a_803_, v___x_804_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = l_List_reverse___redArg(v_a_806_);
v___y_736_ = v_a_785_;
v___y_737_ = v___x_788_;
v_a_738_ = v___x_807_;
goto v___jp_735_;
}
else
{
v___y_741_ = v_a_785_;
v___y_742_ = v___x_788_;
v___y_743_ = v___x_805_;
goto v___jp_740_;
}
}
else
{
v___y_741_ = v_a_785_;
v___y_742_ = v___x_788_;
v___y_743_ = v___x_802_;
goto v___jp_740_;
}
}
else
{
lean_object* v___x_808_; lean_object* v_keyedConfig_809_; uint8_t v_trackZetaDelta_810_; lean_object* v_zetaDeltaSet_811_; lean_object* v_lctx_812_; lean_object* v_localInstances_813_; lean_object* v_defEqCtx_x3f_814_; lean_object* v_synthPendingDepth_815_; lean_object* v_customCanUnfoldPredicate_x3f_816_; uint8_t v_univApprox_817_; uint8_t v_inTypeClassResolution_818_; uint8_t v_cacheInferType_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_808_ = lean_io_get_num_heartbeats();
v_keyedConfig_809_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_810_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_811_ = lean_ctor_get(v___y_683_, 1);
v_lctx_812_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_813_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_814_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_815_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_816_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_817_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_818_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_819_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_809_);
v___x_820_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_809_);
lean_inc(v_customCanUnfoldPredicate_x3f_816_);
lean_inc(v_synthPendingDepth_815_);
lean_inc(v_defEqCtx_x3f_814_);
lean_inc_ref(v_localInstances_813_);
lean_inc_ref(v_lctx_812_);
lean_inc(v_zetaDeltaSet_811_);
v___x_821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_zetaDeltaSet_811_);
lean_ctor_set(v___x_821_, 2, v_lctx_812_);
lean_ctor_set(v___x_821_, 3, v_localInstances_813_);
lean_ctor_set(v___x_821_, 4, v_defEqCtx_x3f_814_);
lean_ctor_set(v___x_821_, 5, v_synthPendingDepth_815_);
lean_ctor_set(v___x_821_, 6, v_customCanUnfoldPredicate_x3f_816_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7, v_trackZetaDelta_810_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7 + 1, v_univApprox_817_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7 + 2, v_inTypeClassResolution_818_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7 + 3, v_cacheInferType_819_);
v___x_822_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_821_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_821_, 7);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_box(0);
v___x_825_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_787_, v_a_823_, v___x_824_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_List_reverse___redArg(v_a_826_);
v___y_766_ = v_a_785_;
v___y_767_ = v___x_808_;
v_a_768_ = v___x_827_;
goto v___jp_765_;
}
else
{
v___y_771_ = v_a_785_;
v___y_772_ = v___x_808_;
v___y_773_ = v___x_825_;
goto v___jp_770_;
}
}
else
{
v___y_771_ = v_a_785_;
v___y_772_ = v___x_808_;
v___y_773_ = v___x_822_;
goto v___jp_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_856_, lean_object* v_g_857_, lean_object* v_e_858_, lean_object* v_cfg_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v___f_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_transparency_boxed_870_; uint8_t v___x_13522__boxed_871_; lean_object* v_res_872_; 
v_transparency_boxed_870_ = lean_unbox(v_transparency_856_);
v___x_13522__boxed_871_ = lean_unbox(v___x_862_);
v_res_872_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_870_, v_g_857_, v_e_858_, v_cfg_859_, v___x_860_, v___x_861_, v___x_13522__boxed_871_, v___x_863_, v___f_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_874_, lean_object* v_g_875_, lean_object* v_cfg_876_, lean_object* v_e_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
lean_inc_ref(v_e_877_);
v___f_883_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_883_, 0, v_e_877_);
v___x_884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_885_ = lean_box(0);
v___x_886_ = 1;
v___x_887_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_888_ = lean_box(v_transparency_874_);
v___x_889_ = lean_box(v___x_886_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_890_, 0, v___x_888_);
lean_closure_set(v___f_890_, 1, v_g_875_);
lean_closure_set(v___f_890_, 2, v_e_877_);
lean_closure_set(v___f_890_, 3, v_cfg_876_);
lean_closure_set(v___f_890_, 4, v___x_885_);
lean_closure_set(v___f_890_, 5, v___x_884_);
lean_closure_set(v___f_890_, 6, v___x_889_);
lean_closure_set(v___f_890_, 7, v___x_887_);
lean_closure_set(v___f_890_, 8, v___f_883_);
v___x_891_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_890_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_892_, lean_object* v_g_893_, lean_object* v_cfg_894_, lean_object* v_e_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v_transparency_boxed_901_; lean_object* v_res_902_; 
v_transparency_boxed_901_ = lean_unbox(v_transparency_892_);
v_res_902_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_901_, v_g_893_, v_cfg_894_, v_e_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_903_, uint8_t v_transparency_904_, lean_object* v_lemmas_905_, lean_object* v_g_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_905_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_921_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_921_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_915_ = lean_box(v_transparency_904_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_916_, 0, v___x_915_);
lean_closure_set(v___f_916_, 1, v_g_906_);
lean_closure_set(v___f_916_, 2, v_cfg_903_);
v___x_917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_917_, 0, lean_box(0));
lean_closure_set(v___x_917_, 1, lean_box(0));
lean_closure_set(v___x_917_, 2, v___f_916_);
lean_closure_set(v___x_917_, 3, v_a_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_917_);
v___x_919_ = v___x_913_;
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
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_g_906_);
lean_dec_ref(v_cfg_903_);
v_a_922_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_910_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_910_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_930_, lean_object* v_transparency_931_, lean_object* v_lemmas_932_, lean_object* v_g_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_transparency_boxed_937_; lean_object* v_res_938_; 
v_transparency_boxed_937_ = lean_unbox(v_transparency_931_);
v_res_938_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_930_, v_transparency_boxed_937_, v_lemmas_932_, v_g_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec(v_a_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_939_, uint8_t v_transparency_940_, lean_object* v_lemmas_941_, lean_object* v_g_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_939_, v_transparency_940_, v_lemmas_941_, v_g_942_, v_a_944_, v_a_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_949_, lean_object* v_transparency_950_, lean_object* v_lemmas_951_, lean_object* v_g_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
uint8_t v_transparency_boxed_958_; lean_object* v_res_959_; 
v_transparency_boxed_958_ = lean_unbox(v_transparency_950_);
v_res_959_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_949_, v_transparency_boxed_958_, v_lemmas_951_, v_g_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_961_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_976_, uint8_t v_transparency_977_, lean_object* v_lemmas_978_, lean_object* v_g_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_976_, v_transparency_977_, v_lemmas_978_, v_g_979_, v_a_981_, v_a_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_Meta_Iterator_head___redArg(v_a_986_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_987_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_985_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_985_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_996_, lean_object* v_transparency_997_, lean_object* v_lemmas_998_, lean_object* v_g_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
uint8_t v_transparency_boxed_1005_; lean_object* v_res_1006_; 
v_transparency_boxed_1005_ = lean_unbox(v_transparency_997_);
v_res_1006_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_996_, v_transparency_boxed_1005_, v_lemmas_998_, v_g_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1007_){
_start:
{
lean_object* v_toApplyRulesConfig_1008_; lean_object* v_toBacktrackConfig_1009_; 
v_toApplyRulesConfig_1008_ = lean_ctor_get(v_x_1007_, 0);
v_toBacktrackConfig_1009_ = lean_ctor_get(v_toApplyRulesConfig_1008_, 0);
lean_inc_ref(v_toBacktrackConfig_1009_);
return v_toBacktrackConfig_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1010_);
lean_dec_ref(v_x_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1014_, lean_object* v_discharge_1015_, lean_object* v_g_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v_g_1016_);
v___x_1022_ = lean_apply_6(v_test_1014_, v_g_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1033_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1033_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1033_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_unbox(v_a_1023_);
lean_dec(v_a_1023_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_del_object(v___x_1025_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
v___x_1028_ = lean_apply_6(v_discharge_1015_, v_g_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec(v_g_1016_);
lean_dec_ref(v_discharge_1015_);
v___x_1029_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_g_1016_);
lean_dec_ref(v_discharge_1015_);
v_a_1034_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1022_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1022_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1042_, lean_object* v_discharge_1043_, lean_object* v_g_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1042_, v_discharge_1043_, v_g_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1051_, lean_object* v_test_1052_){
_start:
{
lean_object* v_toApplyRulesConfig_1053_; lean_object* v_toBacktrackConfig_1054_; uint8_t v_backtracking_1055_; uint8_t v_intro_1056_; uint8_t v_constructor_1057_; uint8_t v_suggestions_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1090_; 
v_toApplyRulesConfig_1053_ = lean_ctor_get(v_cfg_1051_, 0);
lean_inc_ref(v_toApplyRulesConfig_1053_);
v_toBacktrackConfig_1054_ = lean_ctor_get(v_toApplyRulesConfig_1053_, 0);
lean_inc_ref(v_toBacktrackConfig_1054_);
v_backtracking_1055_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1);
v_intro_1056_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1 + 1);
v_constructor_1057_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1 + 2);
v_suggestions_1058_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1 + 3);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_cfg_1051_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_cfg_1051_, 0);
lean_dec(v_unused_1091_);
v___x_1060_ = v_cfg_1051_;
v_isShared_1061_ = v_isSharedCheck_1090_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v_cfg_1051_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1090_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_toApplyConfig_1062_; uint8_t v_transparency_1063_; uint8_t v_symm_1064_; uint8_t v_exfalso_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1088_; 
v_toApplyConfig_1062_ = lean_ctor_get(v_toApplyRulesConfig_1053_, 1);
v_transparency_1063_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1053_, sizeof(void*)*2);
v_symm_1064_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1053_, sizeof(void*)*2 + 1);
v_exfalso_1065_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1053_, sizeof(void*)*2 + 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_toApplyRulesConfig_1053_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_toApplyRulesConfig_1053_, 0);
lean_dec(v_unused_1089_);
v___x_1067_ = v_toApplyRulesConfig_1053_;
v_isShared_1068_ = v_isSharedCheck_1088_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_toApplyConfig_1062_);
lean_dec(v_toApplyRulesConfig_1053_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1088_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_maxDepth_1069_; lean_object* v_proc_1070_; lean_object* v_suspend_1071_; lean_object* v_discharge_1072_; uint8_t v_commitIndependentGoals_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1087_; 
v_maxDepth_1069_ = lean_ctor_get(v_toBacktrackConfig_1054_, 0);
v_proc_1070_ = lean_ctor_get(v_toBacktrackConfig_1054_, 1);
v_suspend_1071_ = lean_ctor_get(v_toBacktrackConfig_1054_, 2);
v_discharge_1072_ = lean_ctor_get(v_toBacktrackConfig_1054_, 3);
v_commitIndependentGoals_1073_ = lean_ctor_get_uint8(v_toBacktrackConfig_1054_, sizeof(void*)*4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_toBacktrackConfig_1054_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1075_ = v_toBacktrackConfig_1054_;
v_isShared_1076_ = v_isSharedCheck_1087_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_discharge_1072_);
lean_inc(v_suspend_1071_);
lean_inc(v_proc_1070_);
lean_inc(v_maxDepth_1069_);
lean_dec(v_toBacktrackConfig_1054_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1087_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___f_1077_; lean_object* v___x_1079_; 
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1077_, 0, v_test_1052_);
lean_closure_set(v___f_1077_, 1, v_discharge_1072_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 3, v___f_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_maxDepth_1069_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_proc_1070_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_suspend_1071_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___f_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1086_, sizeof(void*)*4, v_commitIndependentGoals_1073_);
v___x_1079_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1079_);
v___x_1081_ = v___x_1067_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_toApplyConfig_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2, v_transparency_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2 + 1, v_symm_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2 + 2, v_exfalso_1065_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1081_);
v___x_1083_ = v___x_1060_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1, v_backtracking_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1 + 1, v_intro_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1 + 2, v_constructor_1057_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1 + 3, v_suggestions_1058_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1092_, lean_object* v_proc_1093_, lean_object* v_orig_1094_, lean_object* v_goals_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
if (lean_obj_tag(v_goals_1095_) == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref(v_proc_1093_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
v___x_1101_ = lean_apply_7(v_proc_1092_, v_orig_1094_, v_goals_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
return v___x_1101_;
}
else
{
lean_object* v_head_1102_; lean_object* v_tail_1103_; lean_object* v___x_1104_; 
v_head_1102_ = lean_ctor_get(v_goals_1095_, 0);
v_tail_1103_ = lean_ctor_get(v_goals_1095_, 1);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v_head_1102_);
v___x_1104_ = lean_apply_6(v_proc_1093_, v_head_1102_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
lean_inc(v_tail_1103_);
lean_dec_ref_known(v_goals_1095_, 2);
lean_dec(v_orig_1094_);
lean_dec_ref(v_proc_1092_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = l_List_appendTR___redArg(v_a_1105_, v_tail_1103_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1110_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1127_; 
v_a_1115_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1117_ = v___x_1104_;
v_isShared_1118_ = v_isSharedCheck_1127_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1104_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1127_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___y_1120_; uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_Exception_isInterrupt(v_a_1115_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; 
lean_inc(v_a_1115_);
v___x_1126_ = l_Lean_Exception_isRuntime(v_a_1115_);
v___y_1120_ = v___x_1126_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v___x_1125_;
goto v___jp_1119_;
}
v___jp_1119_:
{
if (v___y_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_del_object(v___x_1117_);
lean_dec(v_a_1115_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
v___x_1121_ = lean_apply_7(v_proc_1092_, v_orig_1094_, v_goals_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
return v___x_1121_;
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref_known(v_goals_1095_, 2);
lean_dec(v_orig_1094_);
lean_dec_ref(v_proc_1092_);
if (v_isShared_1118_ == 0)
{
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1115_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1128_, lean_object* v_proc_1129_, lean_object* v_orig_1130_, lean_object* v_goals_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1128_, v_proc_1129_, v_orig_1130_, v_goals_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1138_, lean_object* v_proc_1139_){
_start:
{
lean_object* v_toApplyRulesConfig_1140_; lean_object* v_toBacktrackConfig_1141_; uint8_t v_backtracking_1142_; uint8_t v_intro_1143_; uint8_t v_constructor_1144_; uint8_t v_suggestions_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1177_; 
v_toApplyRulesConfig_1140_ = lean_ctor_get(v_cfg_1138_, 0);
lean_inc_ref(v_toApplyRulesConfig_1140_);
v_toBacktrackConfig_1141_ = lean_ctor_get(v_toApplyRulesConfig_1140_, 0);
lean_inc_ref(v_toBacktrackConfig_1141_);
v_backtracking_1142_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1);
v_intro_1143_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1 + 1);
v_constructor_1144_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1 + 2);
v_suggestions_1145_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1 + 3);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_cfg_1138_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v_cfg_1138_, 0);
lean_dec(v_unused_1178_);
v___x_1147_ = v_cfg_1138_;
v_isShared_1148_ = v_isSharedCheck_1177_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v_cfg_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1177_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_toApplyConfig_1149_; uint8_t v_transparency_1150_; uint8_t v_symm_1151_; uint8_t v_exfalso_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1175_; 
v_toApplyConfig_1149_ = lean_ctor_get(v_toApplyRulesConfig_1140_, 1);
v_transparency_1150_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1140_, sizeof(void*)*2);
v_symm_1151_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1140_, sizeof(void*)*2 + 1);
v_exfalso_1152_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1140_, sizeof(void*)*2 + 2);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_toApplyRulesConfig_1140_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_toApplyRulesConfig_1140_, 0);
lean_dec(v_unused_1176_);
v___x_1154_ = v_toApplyRulesConfig_1140_;
v_isShared_1155_ = v_isSharedCheck_1175_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_toApplyConfig_1149_);
lean_dec(v_toApplyRulesConfig_1140_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1175_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_maxDepth_1156_; lean_object* v_proc_1157_; lean_object* v_suspend_1158_; lean_object* v_discharge_1159_; uint8_t v_commitIndependentGoals_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1174_; 
v_maxDepth_1156_ = lean_ctor_get(v_toBacktrackConfig_1141_, 0);
v_proc_1157_ = lean_ctor_get(v_toBacktrackConfig_1141_, 1);
v_suspend_1158_ = lean_ctor_get(v_toBacktrackConfig_1141_, 2);
v_discharge_1159_ = lean_ctor_get(v_toBacktrackConfig_1141_, 3);
v_commitIndependentGoals_1160_ = lean_ctor_get_uint8(v_toBacktrackConfig_1141_, sizeof(void*)*4);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_toBacktrackConfig_1141_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1162_ = v_toBacktrackConfig_1141_;
v_isShared_1163_ = v_isSharedCheck_1174_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_discharge_1159_);
lean_inc(v_suspend_1158_);
lean_inc(v_proc_1157_);
lean_inc(v_maxDepth_1156_);
lean_dec(v_toBacktrackConfig_1141_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1174_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___f_1164_; lean_object* v___x_1166_; 
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1164_, 0, v_proc_1157_);
lean_closure_set(v___f_1164_, 1, v_proc_1139_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___f_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_maxDepth_1156_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___f_1164_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_suspend_1158_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_discharge_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*4, v_commitIndependentGoals_1160_);
v___x_1166_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1166_);
v___x_1168_ = v___x_1154_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_toApplyConfig_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2, v_transparency_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2 + 1, v_symm_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2 + 2, v_exfalso_1152_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1168_);
v___x_1170_ = v___x_1147_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1, v_backtracking_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1 + 1, v_intro_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1 + 2, v_constructor_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1 + 3, v_suggestions_1145_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = 1;
v___x_1186_ = l_Lean_Meta_intro1Core(v_g_1179_, v___x_1185_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1204_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1204_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1204_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1202_; 
v_snd_1191_ = lean_ctor_get(v_a_1187_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_a_1187_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_a_1187_, 0);
lean_dec(v_unused_1203_);
v___x_1193_ = v_a_1187_;
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_dec(v_a_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 1);
lean_ctor_set(v___x_1193_, 1, v___x_1195_);
lean_ctor_set(v___x_1193_, 0, v_snd_1191_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_snd_1191_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1197_);
v___x_1199_ = v___x_1189_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1186_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1186_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1221_){
_start:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; 
v___f_1222_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1223_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1221_, v___f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_ks_1228_; lean_object* v_vs_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1253_; 
v_ks_1228_ = lean_ctor_get(v_x_1224_, 0);
v_vs_1229_ = lean_ctor_get(v_x_1224_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1231_ = v_x_1224_;
v_isShared_1232_ = v_isSharedCheck_1253_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_vs_1229_);
lean_inc(v_ks_1228_);
lean_dec(v_x_1224_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1253_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_ks_1228_);
v___x_1234_ = lean_nat_dec_lt(v_x_1225_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v_x_1225_);
v___x_1235_ = lean_array_push(v_ks_1228_, v_x_1226_);
v___x_1236_ = lean_array_push(v_vs_1229_, v_x_1227_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1236_);
lean_ctor_set(v___x_1231_, 0, v___x_1235_);
v___x_1238_ = v___x_1231_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v_k_x27_1240_; uint8_t v___x_1241_; 
v_k_x27_1240_ = lean_array_fget_borrowed(v_ks_1228_, v_x_1225_);
v___x_1241_ = l_Lean_instBEqMVarId_beq(v_x_1226_, v_k_x27_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1243_; 
if (v_isShared_1232_ == 0)
{
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ks_1228_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_vs_1229_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_x_1225_, v___x_1244_);
lean_dec(v_x_1225_);
v_x_1224_ = v___x_1243_;
v_x_1225_ = v___x_1245_;
goto _start;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1248_ = lean_array_fset(v_ks_1228_, v_x_1225_, v_x_1226_);
v___x_1249_ = lean_array_fset(v_vs_1229_, v_x_1225_, v_x_1227_);
lean_dec(v_x_1225_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1249_);
lean_ctor_set(v___x_1231_, 0, v___x_1248_);
v___x_1251_ = v___x_1231_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1254_, lean_object* v_k_1255_, lean_object* v_v_1256_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1254_, v___x_1257_, v_k_1255_, v_v_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1260_, size_t v_x_1261_, size_t v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
lean_object* v_es_1265_; size_t v___x_1266_; size_t v___x_1267_; lean_object* v_j_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_es_1265_ = lean_ctor_get(v_x_1260_, 0);
v___x_1266_ = ((size_t)31ULL);
v___x_1267_ = lean_usize_land(v_x_1261_, v___x_1266_);
v_j_1268_ = lean_usize_to_nat(v___x_1267_);
v___x_1269_ = lean_array_get_size(v_es_1265_);
v___x_1270_ = lean_nat_dec_lt(v_j_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v_j_1268_);
lean_dec(v_x_1264_);
lean_dec(v_x_1263_);
return v_x_1260_;
}
else
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1309_; 
lean_inc_ref(v_es_1265_);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_x_1260_, 0);
lean_dec(v_unused_1310_);
v___x_1272_ = v_x_1260_;
v_isShared_1273_ = v_isSharedCheck_1309_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_x_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1309_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_v_1274_; lean_object* v___x_1275_; lean_object* v_xs_x27_1276_; lean_object* v___y_1278_; 
v_v_1274_ = lean_array_fget(v_es_1265_, v_j_1268_);
v___x_1275_ = lean_box(0);
v_xs_x27_1276_ = lean_array_fset(v_es_1265_, v_j_1268_, v___x_1275_);
switch(lean_obj_tag(v_v_1274_))
{
case 0:
{
lean_object* v_key_1283_; lean_object* v_val_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1294_; 
v_key_1283_ = lean_ctor_get(v_v_1274_, 0);
v_val_1284_ = lean_ctor_get(v_v_1274_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_v_1274_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1286_ = v_v_1274_;
v_isShared_1287_ = v_isSharedCheck_1294_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_val_1284_);
lean_inc(v_key_1283_);
lean_dec(v_v_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1294_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_instBEqMVarId_beq(v_x_1263_, v_key_1283_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_del_object(v___x_1286_);
v___x_1289_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1283_, v_val_1284_, v_x_1263_, v_x_1264_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
v___y_1278_ = v___x_1290_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1292_; 
lean_dec(v_val_1284_);
lean_dec(v_key_1283_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v_x_1264_);
lean_ctor_set(v___x_1286_, 0, v_x_1263_);
v___x_1292_ = v___x_1286_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_x_1263_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_x_1264_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
v___y_1278_ = v___x_1292_;
goto v___jp_1277_;
}
}
}
}
case 1:
{
lean_object* v_node_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1307_; 
v_node_1295_ = lean_ctor_get(v_v_1274_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_v_1274_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1297_ = v_v_1274_;
v_isShared_1298_ = v_isSharedCheck_1307_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_node_1295_);
lean_dec(v_v_1274_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1307_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1299_ = ((size_t)5ULL);
v___x_1300_ = lean_usize_shift_right(v_x_1261_, v___x_1299_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_x_1262_, v___x_1301_);
v___x_1303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1295_, v___x_1300_, v___x_1302_, v_x_1263_, v_x_1264_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1303_);
v___x_1305_ = v___x_1297_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v___y_1278_ = v___x_1305_;
goto v___jp_1277_;
}
}
}
default: 
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_x_1263_);
lean_ctor_set(v___x_1308_, 1, v_x_1264_);
v___y_1278_ = v___x_1308_;
goto v___jp_1277_;
}
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_array_fset(v_xs_x27_1276_, v_j_1268_, v___y_1278_);
lean_dec(v_j_1268_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1279_);
v___x_1281_ = v___x_1272_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_ks_1311_; lean_object* v_vs_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1330_; 
v_ks_1311_ = lean_ctor_get(v_x_1260_, 0);
v_vs_1312_ = lean_ctor_get(v_x_1260_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1314_ = v_x_1260_;
v_isShared_1315_ = v_isSharedCheck_1330_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_vs_1312_);
lean_inc(v_ks_1311_);
lean_dec(v_x_1260_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1330_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_ks_1311_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_vs_1312_);
v___x_1317_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v_newNode_1318_; size_t v___x_1319_; uint8_t v___x_1320_; 
v_newNode_1318_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1317_, v_x_1263_, v_x_1264_);
v___x_1319_ = ((size_t)7ULL);
v___x_1320_ = lean_usize_dec_le(v___x_1319_, v_x_1262_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1321_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1318_);
v___x_1322_ = lean_unsigned_to_nat(4u);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
lean_dec(v___x_1321_);
if (v___x_1323_ == 0)
{
lean_object* v_ks_1324_; lean_object* v_vs_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_ks_1324_ = lean_ctor_get(v_newNode_1318_, 0);
lean_inc_ref(v_ks_1324_);
v_vs_1325_ = lean_ctor_get(v_newNode_1318_, 1);
lean_inc_ref(v_vs_1325_);
lean_dec_ref(v_newNode_1318_);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1262_, v_ks_1324_, v_vs_1325_, v___x_1326_, v___x_1327_);
lean_dec_ref(v_vs_1325_);
lean_dec_ref(v_ks_1324_);
return v___x_1328_;
}
else
{
return v_newNode_1318_;
}
}
else
{
return v_newNode_1318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1331_, lean_object* v_keys_1332_, lean_object* v_vals_1333_, lean_object* v_i_1334_, lean_object* v_entries_1335_){
_start:
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_array_get_size(v_keys_1332_);
v___x_1337_ = lean_nat_dec_lt(v_i_1334_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec(v_i_1334_);
return v_entries_1335_;
}
else
{
lean_object* v_k_1338_; lean_object* v_v_1339_; uint64_t v___x_1340_; size_t v_h_1341_; size_t v___x_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; size_t v_h_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_k_1338_ = lean_array_fget_borrowed(v_keys_1332_, v_i_1334_);
v_v_1339_ = lean_array_fget_borrowed(v_vals_1333_, v_i_1334_);
v___x_1340_ = l_Lean_instHashableMVarId_hash(v_k_1338_);
v_h_1341_ = lean_uint64_to_usize(v___x_1340_);
v___x_1342_ = ((size_t)5ULL);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_sub(v_depth_1331_, v___x_1344_);
v___x_1346_ = lean_usize_mul(v___x_1342_, v___x_1345_);
v_h_1347_ = lean_usize_shift_right(v_h_1341_, v___x_1346_);
v___x_1348_ = lean_nat_add(v_i_1334_, v___x_1343_);
lean_dec(v_i_1334_);
lean_inc(v_v_1339_);
lean_inc(v_k_1338_);
v___x_1349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1335_, v_h_1347_, v_depth_1331_, v_k_1338_, v_v_1339_);
v_i_1334_ = v___x_1348_;
v_entries_1335_ = v___x_1349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1351_, lean_object* v_keys_1352_, lean_object* v_vals_1353_, lean_object* v_i_1354_, lean_object* v_entries_1355_){
_start:
{
size_t v_depth_boxed_1356_; lean_object* v_res_1357_; 
v_depth_boxed_1356_ = lean_unbox_usize(v_depth_1351_);
lean_dec(v_depth_1351_);
v_res_1357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1356_, v_keys_1352_, v_vals_1353_, v_i_1354_, v_entries_1355_);
lean_dec_ref(v_vals_1353_);
lean_dec_ref(v_keys_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
size_t v_x_832__boxed_1363_; size_t v_x_833__boxed_1364_; lean_object* v_res_1365_; 
v_x_832__boxed_1363_ = lean_unbox_usize(v_x_1359_);
lean_dec(v_x_1359_);
v_x_833__boxed_1364_ = lean_unbox_usize(v_x_1360_);
lean_dec(v_x_1360_);
v_res_1365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1358_, v_x_832__boxed_1363_, v_x_833__boxed_1364_, v_x_1361_, v_x_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
uint64_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v___x_1369_ = l_Lean_instHashableMVarId_hash(v_x_1367_);
v___x_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1366_, v___x_1370_, v___x_1371_, v_x_1367_, v_x_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1373_, lean_object* v_val_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_mctx_1378_; lean_object* v_cache_1379_; lean_object* v_zetaDeltaFVarIds_1380_; lean_object* v_postponed_1381_; lean_object* v_diag_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1411_; 
v___x_1377_ = lean_st_ref_take(v___y_1375_);
v_mctx_1378_ = lean_ctor_get(v___x_1377_, 0);
v_cache_1379_ = lean_ctor_get(v___x_1377_, 1);
v_zetaDeltaFVarIds_1380_ = lean_ctor_get(v___x_1377_, 2);
v_postponed_1381_ = lean_ctor_get(v___x_1377_, 3);
v_diag_1382_ = lean_ctor_get(v___x_1377_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1384_ = v___x_1377_;
v_isShared_1385_ = v_isSharedCheck_1411_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_diag_1382_);
lean_inc(v_postponed_1381_);
lean_inc(v_zetaDeltaFVarIds_1380_);
lean_inc(v_cache_1379_);
lean_inc(v_mctx_1378_);
lean_dec(v___x_1377_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1411_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_depth_1386_; lean_object* v_levelAssignDepth_1387_; lean_object* v_lmvarCounter_1388_; lean_object* v_mvarCounter_1389_; lean_object* v_lDecls_1390_; lean_object* v_decls_1391_; lean_object* v_userNames_1392_; lean_object* v_lAssignment_1393_; lean_object* v_eAssignment_1394_; lean_object* v_dAssignment_1395_; lean_object* v_instanceTypedMVars_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1410_; 
v_depth_1386_ = lean_ctor_get(v_mctx_1378_, 0);
v_levelAssignDepth_1387_ = lean_ctor_get(v_mctx_1378_, 1);
v_lmvarCounter_1388_ = lean_ctor_get(v_mctx_1378_, 2);
v_mvarCounter_1389_ = lean_ctor_get(v_mctx_1378_, 3);
v_lDecls_1390_ = lean_ctor_get(v_mctx_1378_, 4);
v_decls_1391_ = lean_ctor_get(v_mctx_1378_, 5);
v_userNames_1392_ = lean_ctor_get(v_mctx_1378_, 6);
v_lAssignment_1393_ = lean_ctor_get(v_mctx_1378_, 7);
v_eAssignment_1394_ = lean_ctor_get(v_mctx_1378_, 8);
v_dAssignment_1395_ = lean_ctor_get(v_mctx_1378_, 9);
v_instanceTypedMVars_1396_ = lean_ctor_get(v_mctx_1378_, 10);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_mctx_1378_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1398_ = v_mctx_1378_;
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_instanceTypedMVars_1396_);
lean_inc(v_dAssignment_1395_);
lean_inc(v_eAssignment_1394_);
lean_inc(v_lAssignment_1393_);
lean_inc(v_userNames_1392_);
lean_inc(v_decls_1391_);
lean_inc(v_lDecls_1390_);
lean_inc(v_mvarCounter_1389_);
lean_inc(v_lmvarCounter_1388_);
lean_inc(v_levelAssignDepth_1387_);
lean_inc(v_depth_1386_);
lean_dec(v_mctx_1378_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1394_, v_mvarId_1373_, v_val_1374_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 8, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_depth_1386_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_levelAssignDepth_1387_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_lmvarCounter_1388_);
lean_ctor_set(v_reuseFailAlloc_1409_, 3, v_mvarCounter_1389_);
lean_ctor_set(v_reuseFailAlloc_1409_, 4, v_lDecls_1390_);
lean_ctor_set(v_reuseFailAlloc_1409_, 5, v_decls_1391_);
lean_ctor_set(v_reuseFailAlloc_1409_, 6, v_userNames_1392_);
lean_ctor_set(v_reuseFailAlloc_1409_, 7, v_lAssignment_1393_);
lean_ctor_set(v_reuseFailAlloc_1409_, 8, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1409_, 9, v_dAssignment_1395_);
lean_ctor_set(v_reuseFailAlloc_1409_, 10, v_instanceTypedMVars_1396_);
v___x_1402_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1402_);
v___x_1404_ = v___x_1384_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_cache_1379_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_zetaDeltaFVarIds_1380_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_postponed_1381_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_diag_1382_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_st_ref_put(v___y_1375_, v___x_1404_);
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1412_, lean_object* v_val_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1412_, v_val_1413_, v___y_1414_);
lean_dec(v___y_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
lean_inc(v_g_1417_);
v___x_1423_ = l_Lean_MVarId_getType(v_g_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_box(0);
v___x_1426_ = l_Lean_Meta_synthInstance(v_a_1424_, v___x_1425_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1417_, v_a_1427_, v___y_1419_);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v___x_1428_, 0);
lean_dec(v_unused_1437_);
v___x_1430_ = v___x_1428_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v___x_1428_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_box(0);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_g_1417_);
v_a_1438_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1426_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1426_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
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
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_g_1417_);
v_a_1446_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1423_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1423_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1462_){
_start:
{
lean_object* v___f_1463_; lean_object* v___x_1464_; 
v___f_1463_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1464_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1462_, v___f_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1465_, lean_object* v_val_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1465_, v_val_1466_, v___y_1468_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1473_, lean_object* v_val_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1473_, v_val_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1482_, v_x_1483_, v_x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1486_, lean_object* v_x_1487_, size_t v_x_1488_, size_t v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1487_, v_x_1488_, v_x_1489_, v_x_1490_, v_x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
size_t v_x_1153__boxed_1499_; size_t v_x_1154__boxed_1500_; lean_object* v_res_1501_; 
v_x_1153__boxed_1499_ = lean_unbox_usize(v_x_1495_);
lean_dec(v_x_1495_);
v_x_1154__boxed_1500_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_res_1501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1493_, v_x_1494_, v_x_1153__boxed_1499_, v_x_1154__boxed_1500_, v_x_1497_, v_x_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1502_, lean_object* v_n_1503_, lean_object* v_k_1504_, lean_object* v_v_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1503_, v_k_1504_, v_v_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1507_, size_t v_depth_1508_, lean_object* v_keys_1509_, lean_object* v_vals_1510_, lean_object* v_heq_1511_, lean_object* v_i_1512_, lean_object* v_entries_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1508_, v_keys_1509_, v_vals_1510_, v_i_1512_, v_entries_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1515_, lean_object* v_depth_1516_, lean_object* v_keys_1517_, lean_object* v_vals_1518_, lean_object* v_heq_1519_, lean_object* v_i_1520_, lean_object* v_entries_1521_){
_start:
{
size_t v_depth_boxed_1522_; lean_object* v_res_1523_; 
v_depth_boxed_1522_ = lean_unbox_usize(v_depth_1516_);
lean_dec(v_depth_1516_);
v_res_1523_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1515_, v_depth_boxed_1522_, v_keys_1517_, v_vals_1518_, v_heq_1519_, v_i_1520_, v_entries_1521_);
lean_dec_ref(v_vals_1518_);
lean_dec_ref(v_keys_1517_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1525_, v_x_1526_, v_x_1527_, v_x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1530_, lean_object* v_discharge_1531_, lean_object* v_g_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
lean_inc(v___y_1534_);
lean_inc_ref(v___y_1533_);
lean_inc(v_g_1532_);
v___x_1538_ = lean_apply_6(v_discharge_1530_, v_g_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, lean_box(0));
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_dec(v_g_1532_);
lean_dec_ref(v_discharge_1531_);
return v___x_1538_;
}
else
{
lean_object* v_a_1539_; uint8_t v___y_1541_; uint8_t v___x_1543_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
v___x_1543_ = l_Lean_Exception_isInterrupt(v_a_1539_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lean_Exception_isRuntime(v_a_1539_);
v___y_1541_ = v___x_1544_;
goto v___jp_1540_;
}
else
{
lean_dec(v_a_1539_);
v___y_1541_ = v___x_1543_;
goto v___jp_1540_;
}
v___jp_1540_:
{
if (v___y_1541_ == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref_known(v___x_1538_, 1);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
lean_inc(v___y_1534_);
lean_inc_ref(v___y_1533_);
v___x_1542_ = lean_apply_6(v_discharge_1531_, v_g_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, lean_box(0));
return v___x_1542_;
}
else
{
lean_dec(v_g_1532_);
lean_dec_ref(v_discharge_1531_);
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1545_, lean_object* v_discharge_1546_, lean_object* v_g_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1545_, v_discharge_1546_, v_g_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1554_, lean_object* v_discharge_1555_){
_start:
{
lean_object* v_toApplyRulesConfig_1556_; lean_object* v_toBacktrackConfig_1557_; uint8_t v_backtracking_1558_; uint8_t v_intro_1559_; uint8_t v_constructor_1560_; uint8_t v_suggestions_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1593_; 
v_toApplyRulesConfig_1556_ = lean_ctor_get(v_cfg_1554_, 0);
lean_inc_ref(v_toApplyRulesConfig_1556_);
v_toBacktrackConfig_1557_ = lean_ctor_get(v_toApplyRulesConfig_1556_, 0);
lean_inc_ref(v_toBacktrackConfig_1557_);
v_backtracking_1558_ = lean_ctor_get_uint8(v_cfg_1554_, sizeof(void*)*1);
v_intro_1559_ = lean_ctor_get_uint8(v_cfg_1554_, sizeof(void*)*1 + 1);
v_constructor_1560_ = lean_ctor_get_uint8(v_cfg_1554_, sizeof(void*)*1 + 2);
v_suggestions_1561_ = lean_ctor_get_uint8(v_cfg_1554_, sizeof(void*)*1 + 3);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_cfg_1554_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_cfg_1554_, 0);
lean_dec(v_unused_1594_);
v___x_1563_ = v_cfg_1554_;
v_isShared_1564_ = v_isSharedCheck_1593_;
goto v_resetjp_1562_;
}
else
{
lean_dec(v_cfg_1554_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1593_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_toApplyConfig_1565_; uint8_t v_transparency_1566_; uint8_t v_symm_1567_; uint8_t v_exfalso_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1591_; 
v_toApplyConfig_1565_ = lean_ctor_get(v_toApplyRulesConfig_1556_, 1);
v_transparency_1566_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1556_, sizeof(void*)*2);
v_symm_1567_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1556_, sizeof(void*)*2 + 1);
v_exfalso_1568_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1556_, sizeof(void*)*2 + 2);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_toApplyRulesConfig_1556_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_toApplyRulesConfig_1556_, 0);
lean_dec(v_unused_1592_);
v___x_1570_ = v_toApplyRulesConfig_1556_;
v_isShared_1571_ = v_isSharedCheck_1591_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_toApplyConfig_1565_);
lean_dec(v_toApplyRulesConfig_1556_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1591_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_maxDepth_1572_; lean_object* v_proc_1573_; lean_object* v_suspend_1574_; lean_object* v_discharge_1575_; uint8_t v_commitIndependentGoals_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1590_; 
v_maxDepth_1572_ = lean_ctor_get(v_toBacktrackConfig_1557_, 0);
v_proc_1573_ = lean_ctor_get(v_toBacktrackConfig_1557_, 1);
v_suspend_1574_ = lean_ctor_get(v_toBacktrackConfig_1557_, 2);
v_discharge_1575_ = lean_ctor_get(v_toBacktrackConfig_1557_, 3);
v_commitIndependentGoals_1576_ = lean_ctor_get_uint8(v_toBacktrackConfig_1557_, sizeof(void*)*4);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_toBacktrackConfig_1557_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1578_ = v_toBacktrackConfig_1557_;
v_isShared_1579_ = v_isSharedCheck_1590_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_discharge_1575_);
lean_inc(v_suspend_1574_);
lean_inc(v_proc_1573_);
lean_inc(v_maxDepth_1572_);
lean_dec(v_toBacktrackConfig_1557_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1590_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___f_1580_; lean_object* v___x_1582_; 
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1580_, 0, v_discharge_1555_);
lean_closure_set(v___f_1580_, 1, v_discharge_1575_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 3, v___f_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_maxDepth_1572_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_proc_1573_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_suspend_1574_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___f_1580_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*4, v_commitIndependentGoals_1576_);
v___x_1582_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1582_);
v___x_1584_ = v___x_1570_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_toApplyConfig_1565_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*2, v_transparency_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*2 + 1, v_symm_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*2 + 2, v_exfalso_1568_);
v___x_1584_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1584_);
v___x_1586_ = v___x_1563_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1587_, sizeof(void*)*1, v_backtracking_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1587_, sizeof(void*)*1 + 1, v_intro_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1587_, sizeof(void*)*1 + 2, v_constructor_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1587_, sizeof(void*)*1 + 3, v_suggestions_1561_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = 1;
v___x_1602_ = l_Lean_Meta_intro1Core(v_g_1595_, v___x_1601_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1621_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1621_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1621_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1619_; 
v_snd_1607_ = lean_ctor_get(v_a_1603_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; 
v_unused_1620_ = lean_ctor_get(v_a_1603_, 0);
lean_dec(v_unused_1620_);
v___x_1609_ = v_a_1603_;
v_isShared_1610_ = v_isSharedCheck_1619_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_dec(v_a_1603_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1619_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 1);
lean_ctor_set(v___x_1609_, 1, v___x_1611_);
lean_ctor_set(v___x_1609_, 0, v_snd_1607_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_snd_1607_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1614_);
v___x_1616_ = v___x_1605_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1602_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1602_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1638_){
_start:
{
lean_object* v___f_1639_; lean_object* v___x_1640_; 
v___f_1639_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1640_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1638_, v___f_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1652_ = l_Lean_MVarId_constructor(v_g_1645_, v___x_1651_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_a_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1652_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1652_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1678_){
_start:
{
lean_object* v___f_1679_; lean_object* v___x_1680_; 
v___f_1679_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1680_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1678_, v___f_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
lean_inc(v_g_1683_);
v___x_1689_ = l_Lean_MVarId_getType(v_g_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1691_ = lean_box(0);
v___x_1692_ = l_Lean_Meta_synthInstance(v_a_1690_, v___x_1691_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1683_, v_a_1693_, v___y_1685_);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v___x_1694_, 0);
lean_dec(v_unused_1703_);
v___x_1696_ = v___x_1694_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v___x_1694_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_g_1683_);
v_a_1704_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1692_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1692_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_g_1683_);
v_a_1712_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1689_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1689_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1728_){
_start:
{
lean_object* v___f_1729_; lean_object* v___x_1730_; 
v___f_1729_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1730_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1728_, v___f_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = l_Lean_Expr_hasMVar(v_e_1731_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_e_1731_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; lean_object* v_mctx_1737_; lean_object* v___x_1738_; lean_object* v_fst_1739_; lean_object* v_snd_1740_; lean_object* v___x_1741_; lean_object* v_cache_1742_; lean_object* v_zetaDeltaFVarIds_1743_; lean_object* v_postponed_1744_; lean_object* v_diag_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1754_; 
v___x_1736_ = lean_st_ref_get(v___y_1732_);
v_mctx_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_ref(v_mctx_1737_);
lean_dec(v___x_1736_);
v___x_1738_ = l_Lean_instantiateMVarsCore(v_mctx_1737_, v_e_1731_);
v_fst_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_fst_1739_);
v_snd_1740_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_snd_1740_);
lean_dec_ref(v___x_1738_);
v___x_1741_ = lean_st_ref_take(v___y_1732_);
v_cache_1742_ = lean_ctor_get(v___x_1741_, 1);
v_zetaDeltaFVarIds_1743_ = lean_ctor_get(v___x_1741_, 2);
v_postponed_1744_ = lean_ctor_get(v___x_1741_, 3);
v_diag_1745_ = lean_ctor_get(v___x_1741_, 4);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1755_);
v___x_1747_ = v___x_1741_;
v_isShared_1748_ = v_isSharedCheck_1754_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_diag_1745_);
lean_inc(v_postponed_1744_);
lean_inc(v_zetaDeltaFVarIds_1743_);
lean_inc(v_cache_1742_);
lean_dec(v___x_1741_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1754_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v_snd_1740_);
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_snd_1740_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_cache_1742_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_zetaDeltaFVarIds_1743_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_postponed_1744_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_diag_1745_);
v___x_1750_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_st_ref_put(v___y_1732_, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_fst_1739_);
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1756_, v___y_1757_);
lean_dec(v___y_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1760_, v___y_1762_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1774_, v_x_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1781_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1781_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1798_, lean_object* v_x_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1798_, v_x_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1806_, lean_object* v_mvarId_1807_, lean_object* v_x_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1807_, v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_mvarId_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1815_, v_mvarId_1816_, v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_ref_1830_; lean_object* v___x_1831_; lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
v_ref_1830_ = lean_ctor_get(v___y_1827_, 5);
v___x_1831_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_inc(v_ref_1830_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_ref_1830_);
lean_ctor_set(v___x_1836_, 1, v_a_1832_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 1);
lean_ctor_set(v___x_1834_, 0, v___x_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
if (lean_obj_tag(v_x_1848_) == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = l_List_reverse___redArg(v_x_1849_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
else
{
lean_object* v_head_1857_; lean_object* v_tail_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1878_; 
v_head_1857_ = lean_ctor_get(v_x_1848_, 0);
v_tail_1858_ = lean_ctor_get(v_x_1848_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_x_1848_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1860_ = v_x_1848_;
v_isShared_1861_ = v_isSharedCheck_1878_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_tail_1858_);
lean_inc(v_head_1857_);
lean_dec(v_x_1848_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1878_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_inc(v_head_1857_);
v___x_1862_ = l_Lean_Expr_mvar___override(v_head_1857_);
v___x_1863_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1863_, 0, v___x_1862_);
v___x_1864_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1857_, v___x_1863_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v_x_1849_);
lean_ctor_set(v___x_1860_, 0, v_a_1865_);
v___x_1867_ = v___x_1860_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1865_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_x_1849_);
v___x_1867_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
v_x_1848_ = v_tail_1858_;
v_x_1849_ = v___x_1867_;
goto _start;
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_del_object(v___x_1860_);
lean_dec(v_tail_1858_);
lean_dec(v_x_1849_);
v_a_1870_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1864_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1864_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1879_, v_x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1890_, lean_object* v_proc_1891_, lean_object* v_orig_1892_, lean_object* v_goals_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
lean_inc(v_orig_1892_);
v___x_1900_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1892_, v___x_1899_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
v___x_1902_ = lean_apply_6(v_test_1890_, v_a_1901_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, lean_box(0));
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; uint8_t v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = lean_unbox(v_a_1903_);
lean_dec(v_a_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_goals_1893_);
lean_dec(v_orig_1892_);
lean_dec_ref(v_proc_1891_);
v___x_1905_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1906_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1905_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v___x_1915_; 
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
v___x_1915_ = lean_apply_7(v_proc_1891_, v_orig_1892_, v_goals_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, lean_box(0));
return v___x_1915_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_goals_1893_);
lean_dec(v_orig_1892_);
lean_dec_ref(v_proc_1891_);
v_a_1916_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1902_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1902_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_goals_1893_);
lean_dec(v_orig_1892_);
lean_dec_ref(v_proc_1891_);
lean_dec_ref(v_test_1890_);
v_a_1924_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1900_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1900_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1932_, lean_object* v_proc_1933_, lean_object* v_orig_1934_, lean_object* v_goals_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1932_, v_proc_1933_, v_orig_1934_, v_goals_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1942_, lean_object* v_test_1943_){
_start:
{
lean_object* v_toApplyRulesConfig_1944_; lean_object* v_toBacktrackConfig_1945_; uint8_t v_backtracking_1946_; uint8_t v_intro_1947_; uint8_t v_constructor_1948_; uint8_t v_suggestions_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1981_; 
v_toApplyRulesConfig_1944_ = lean_ctor_get(v_cfg_1942_, 0);
lean_inc_ref(v_toApplyRulesConfig_1944_);
v_toBacktrackConfig_1945_ = lean_ctor_get(v_toApplyRulesConfig_1944_, 0);
lean_inc_ref(v_toBacktrackConfig_1945_);
v_backtracking_1946_ = lean_ctor_get_uint8(v_cfg_1942_, sizeof(void*)*1);
v_intro_1947_ = lean_ctor_get_uint8(v_cfg_1942_, sizeof(void*)*1 + 1);
v_constructor_1948_ = lean_ctor_get_uint8(v_cfg_1942_, sizeof(void*)*1 + 2);
v_suggestions_1949_ = lean_ctor_get_uint8(v_cfg_1942_, sizeof(void*)*1 + 3);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_cfg_1942_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_cfg_1942_, 0);
lean_dec(v_unused_1982_);
v___x_1951_ = v_cfg_1942_;
v_isShared_1952_ = v_isSharedCheck_1981_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v_cfg_1942_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1981_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_toApplyConfig_1953_; uint8_t v_transparency_1954_; uint8_t v_symm_1955_; uint8_t v_exfalso_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1979_; 
v_toApplyConfig_1953_ = lean_ctor_get(v_toApplyRulesConfig_1944_, 1);
v_transparency_1954_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1944_, sizeof(void*)*2);
v_symm_1955_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1944_, sizeof(void*)*2 + 1);
v_exfalso_1956_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1944_, sizeof(void*)*2 + 2);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_toApplyRulesConfig_1944_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v_toApplyRulesConfig_1944_, 0);
lean_dec(v_unused_1980_);
v___x_1958_ = v_toApplyRulesConfig_1944_;
v_isShared_1959_ = v_isSharedCheck_1979_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_toApplyConfig_1953_);
lean_dec(v_toApplyRulesConfig_1944_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1979_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_maxDepth_1960_; lean_object* v_proc_1961_; lean_object* v_suspend_1962_; lean_object* v_discharge_1963_; uint8_t v_commitIndependentGoals_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1978_; 
v_maxDepth_1960_ = lean_ctor_get(v_toBacktrackConfig_1945_, 0);
v_proc_1961_ = lean_ctor_get(v_toBacktrackConfig_1945_, 1);
v_suspend_1962_ = lean_ctor_get(v_toBacktrackConfig_1945_, 2);
v_discharge_1963_ = lean_ctor_get(v_toBacktrackConfig_1945_, 3);
v_commitIndependentGoals_1964_ = lean_ctor_get_uint8(v_toBacktrackConfig_1945_, sizeof(void*)*4);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_toBacktrackConfig_1945_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1966_ = v_toBacktrackConfig_1945_;
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_discharge_1963_);
lean_inc(v_suspend_1962_);
lean_inc(v_proc_1961_);
lean_inc(v_maxDepth_1960_);
lean_dec(v_toBacktrackConfig_1945_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___f_1968_; lean_object* v___x_1970_; 
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1968_, 0, v_test_1943_);
lean_closure_set(v___f_1968_, 1, v_proc_1961_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v___f_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_maxDepth_1960_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___f_1968_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_suspend_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_discharge_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*4, v_commitIndependentGoals_1964_);
v___x_1970_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1970_);
v___x_1972_ = v___x_1958_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_toApplyConfig_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*2, v_transparency_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*2 + 1, v_symm_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*2 + 2, v_exfalso_1956_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1972_);
v___x_1974_ = v___x_1951_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*1, v_backtracking_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*1 + 1, v_intro_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*1 + 2, v_constructor_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*1 + 3, v_suggestions_1949_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_1983_, lean_object* v_msg_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_1991_, v_msg_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_1999_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = 0;
return v___x_2000_;
}
else
{
lean_object* v_head_2001_; lean_object* v_tail_2002_; uint8_t v___x_2003_; 
v_head_2001_ = lean_ctor_get(v_x_1999_, 0);
v_tail_2002_ = lean_ctor_get(v_x_1999_, 1);
v___x_2003_ = l_Lean_Expr_hasMVar(v_head_2001_);
if (v___x_2003_ == 0)
{
v_x_1999_ = v_tail_2002_;
goto _start;
}
else
{
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2005_){
_start:
{
uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_res_2006_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2005_);
lean_dec(v_x_2005_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2008_, lean_object* v_sols_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2009_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
v___x_2016_ = lean_apply_6(v_test_2008_, v_sols_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, lean_box(0));
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v_sols_2009_);
lean_dec_ref(v_test_2008_);
v___x_2017_ = lean_box(v___x_2015_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2019_, lean_object* v_sols_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2019_, v_sols_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2027_, lean_object* v_test_2028_){
_start:
{
lean_object* v___f_2029_; lean_object* v___x_2030_; 
v___f_2029_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2029_, 0, v_test_2028_);
v___x_2030_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2027_, v___f_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2031_, lean_object* v_x_2032_){
_start:
{
if (lean_obj_tag(v_x_2032_) == 0)
{
uint8_t v___x_2033_; 
lean_dec_ref(v_e_2031_);
v___x_2033_ = 0;
return v___x_2033_;
}
else
{
lean_object* v_head_2034_; lean_object* v_tail_2035_; uint8_t v___x_2036_; 
v_head_2034_ = lean_ctor_get(v_x_2032_, 0);
v_tail_2035_ = lean_ctor_get(v_x_2032_, 1);
lean_inc_ref(v_e_2031_);
v___x_2036_ = l_Lean_Expr_occurs(v_e_2031_, v_head_2034_);
if (v___x_2036_ == 0)
{
v_x_2032_ = v_tail_2035_;
goto _start;
}
else
{
lean_dec_ref(v_e_2031_);
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2038_, lean_object* v_x_2039_){
_start:
{
uint8_t v_res_2040_; lean_object* v_r_2041_; 
v_res_2040_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2038_, v_x_2039_);
lean_dec(v_x_2039_);
v_r_2041_ = lean_box(v_res_2040_);
return v_r_2041_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2042_, lean_object* v_x_2043_){
_start:
{
if (lean_obj_tag(v_x_2043_) == 0)
{
uint8_t v___x_2044_; 
v___x_2044_ = 1;
return v___x_2044_;
}
else
{
lean_object* v_head_2045_; lean_object* v_tail_2046_; uint8_t v___x_2047_; 
v_head_2045_ = lean_ctor_get(v_x_2043_, 0);
lean_inc(v_head_2045_);
v_tail_2046_ = lean_ctor_get(v_x_2043_, 1);
lean_inc(v_tail_2046_);
lean_dec_ref_known(v_x_2043_, 2);
v___x_2047_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2045_, v_sols_2042_);
if (v___x_2047_ == 0)
{
lean_dec(v_tail_2046_);
return v___x_2047_;
}
else
{
v_x_2043_ = v_tail_2046_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2049_, lean_object* v_x_2050_){
_start:
{
uint8_t v_res_2051_; lean_object* v_r_2052_; 
v_res_2051_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2049_, v_x_2050_);
lean_dec(v_sols_2049_);
v_r_2052_ = lean_box(v_res_2051_);
return v_r_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2053_, lean_object* v_sols_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2054_, v_use_2053_);
v___x_2061_ = lean_box(v___x_2060_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2063_, lean_object* v_sols_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2063_, v_sols_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v_sols_2064_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2071_, lean_object* v_use_2072_){
_start:
{
lean_object* v___f_2073_; lean_object* v___x_2074_; 
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2073_, 0, v_use_2072_);
v___x_2074_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2071_, v___f_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2075_){
_start:
{
lean_object* v___y_2077_; lean_object* v_toApplyRulesConfig_2078_; uint8_t v_backtracking_2079_; uint8_t v_intro_2080_; uint8_t v_constructor_2081_; uint8_t v_suggestions_2082_; uint8_t v_intro_2086_; 
v_intro_2086_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1 + 1);
if (v_intro_2086_ == 0)
{
lean_object* v_toApplyRulesConfig_2087_; uint8_t v_backtracking_2088_; uint8_t v_constructor_2089_; uint8_t v_suggestions_2090_; 
v_toApplyRulesConfig_2087_ = lean_ctor_get(v_cfg_2075_, 0);
lean_inc_ref(v_toApplyRulesConfig_2087_);
v_backtracking_2088_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1);
v_constructor_2089_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1 + 2);
v_suggestions_2090_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1 + 3);
v___y_2077_ = v_cfg_2075_;
v_toApplyRulesConfig_2078_ = v_toApplyRulesConfig_2087_;
v_backtracking_2079_ = v_backtracking_2088_;
v_intro_2080_ = v_intro_2086_;
v_constructor_2081_ = v_constructor_2089_;
v_suggestions_2082_ = v_suggestions_2090_;
goto v___jp_2076_;
}
else
{
lean_object* v_toApplyRulesConfig_2091_; uint8_t v_backtracking_2092_; uint8_t v_constructor_2093_; uint8_t v_suggestions_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2108_; 
v_toApplyRulesConfig_2091_ = lean_ctor_get(v_cfg_2075_, 0);
v_backtracking_2092_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1);
v_constructor_2093_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1 + 2);
v_suggestions_2094_ = lean_ctor_get_uint8(v_cfg_2075_, sizeof(void*)*1 + 3);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_cfg_2075_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2096_ = v_cfg_2075_;
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_toApplyRulesConfig_2091_);
lean_dec(v_cfg_2075_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
uint8_t v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = 0;
if (v_isShared_2097_ == 0)
{
v___x_2100_ = v___x_2096_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_toApplyRulesConfig_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1, v_backtracking_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1 + 2, v_constructor_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1 + 3, v_suggestions_2094_);
v___x_2100_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v_toApplyRulesConfig_2102_; uint8_t v_backtracking_2103_; uint8_t v_intro_2104_; uint8_t v_constructor_2105_; uint8_t v_suggestions_2106_; 
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*1 + 1, v___x_2098_);
v___x_2101_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2100_);
v_toApplyRulesConfig_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_ref(v_toApplyRulesConfig_2102_);
v_backtracking_2103_ = lean_ctor_get_uint8(v___x_2101_, sizeof(void*)*1);
v_intro_2104_ = lean_ctor_get_uint8(v___x_2101_, sizeof(void*)*1 + 1);
v_constructor_2105_ = lean_ctor_get_uint8(v___x_2101_, sizeof(void*)*1 + 2);
v_suggestions_2106_ = lean_ctor_get_uint8(v___x_2101_, sizeof(void*)*1 + 3);
v___y_2077_ = v___x_2101_;
v_toApplyRulesConfig_2078_ = v_toApplyRulesConfig_2102_;
v_backtracking_2079_ = v_backtracking_2103_;
v_intro_2080_ = v_intro_2104_;
v_constructor_2081_ = v_constructor_2105_;
v_suggestions_2082_ = v_suggestions_2106_;
goto v___jp_2076_;
}
}
}
v___jp_2076_:
{
if (v_constructor_2081_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2078_);
return v___y_2077_;
}
else
{
uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref(v___y_2077_);
v___x_2083_ = 0;
v___x_2084_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2084_, 0, v_toApplyRulesConfig_2078_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*1, v_backtracking_2079_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*1 + 1, v_intro_2080_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*1 + 2, v___x_2083_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*1 + 3, v_suggestions_2082_);
v___x_2085_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2084_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2109_, lean_object* v_x_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = l_List_reverse___redArg(v_x_2110_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
else
{
lean_object* v_head_2120_; lean_object* v_tail_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2139_; 
v_head_2120_ = lean_ctor_get(v_x_2109_, 0);
v_tail_2121_ = lean_ctor_get(v_x_2109_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2123_ = v_x_2109_;
v_isShared_2124_ = v_isSharedCheck_2139_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_tail_2121_);
lean_inc(v_head_2120_);
lean_dec(v_x_2109_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2139_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; 
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
v___x_2125_ = lean_apply_7(v_head_2120_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, lean_box(0));
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 1, v_x_2110_);
lean_ctor_set(v___x_2123_, 0, v_a_2126_);
v___x_2128_ = v___x_2123_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2126_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_x_2110_);
v___x_2128_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
v_x_2109_ = v_tail_2121_;
v_x_2110_ = v___x_2128_;
goto _start;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_del_object(v___x_2123_);
lean_dec(v_tail_2121_);
lean_dec(v_x_2110_);
v_a_2131_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2125_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2125_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2140_, v_x_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2150_, lean_object* v_cfg_2151_, lean_object* v_lemmas_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
lean_inc(v___y_2156_);
lean_inc_ref(v___y_2155_);
lean_inc(v___y_2154_);
lean_inc_ref(v___y_2153_);
v___x_2160_ = lean_apply_8(v_ctx_2150_, v_cfg_2151_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, lean_box(0));
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_box(0);
v___x_2163_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2152_, v___x_2162_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2172_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = l_List_appendTR___redArg(v_a_2161_, v_a_2164_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
else
{
lean_dec(v_a_2161_);
return v___x_2163_;
}
}
else
{
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v_lemmas_2152_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2173_, lean_object* v_cfg_2174_, lean_object* v_lemmas_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2173_, v_cfg_2174_, v_lemmas_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2184_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = 0;
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2186_){
_start:
{
uint8_t v_res_2187_; lean_object* v_r_2188_; 
v_res_2187_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2186_);
lean_dec(v_x_2186_);
v_r_2188_ = lean_box(v_res_2187_);
return v_r_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2189_, lean_object* v___x_2190_, lean_object* v___x_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2189_, v___x_2190_, v___x_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2206_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2206_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2206_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_fst_2202_; lean_object* v___x_2204_; 
v_fst_2202_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_fst_2202_);
lean_dec(v_a_2198_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_fst_2202_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_fst_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
v_a_2207_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2197_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2197_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2215_, lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2215_, v___x_2216_, v___x_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2238_, lean_object* v_g_2239_, lean_object* v_lemmas_2240_, lean_object* v_ctx_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; 
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2247_, 0, v_ctx_2241_);
lean_closure_set(v___f_2247_, 1, v_cfg_2238_);
lean_closure_set(v___f_2247_, 2, v_lemmas_2240_);
v___x_2248_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2249_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2250_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2250_, 0, v___f_2247_);
lean_closure_set(v___f_2250_, 1, v___x_2248_);
lean_closure_set(v___f_2250_, 2, v___x_2249_);
v___x_2251_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2239_, v___f_2250_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2252_, lean_object* v_g_2253_, lean_object* v_lemmas_2254_, lean_object* v_ctx_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2252_, v_g_2253_, v_lemmas_2254_, v_ctx_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2262_, lean_object* v_lemmas_2263_, lean_object* v_ctx_2264_, lean_object* v_g_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; 
lean_inc(v_g_2265_);
lean_inc_ref(v_cfg_2262_);
v___x_2271_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2262_, v_g_2265_, v_lemmas_2263_, v_ctx_2264_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_toApplyRulesConfig_2272_; lean_object* v_a_2273_; lean_object* v_toApplyConfig_2274_; uint8_t v_transparency_2275_; lean_object* v___x_2276_; 
v_toApplyRulesConfig_2272_ = lean_ctor_get(v_cfg_2262_, 0);
lean_inc_ref(v_toApplyRulesConfig_2272_);
lean_dec_ref(v_cfg_2262_);
v_a_2273_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2271_, 1);
v_toApplyConfig_2274_ = lean_ctor_get(v_toApplyRulesConfig_2272_, 1);
lean_inc_ref(v_toApplyConfig_2274_);
v_transparency_2275_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2272_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2272_);
v___x_2276_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2274_, v_transparency_2275_, v_a_2273_, v_g_2265_, v_a_2267_, v_a_2269_);
return v___x_2276_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_g_2265_);
lean_dec_ref(v_cfg_2262_);
v_a_2277_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2271_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2271_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2285_, lean_object* v_lemmas_2286_, lean_object* v_ctx_2287_, lean_object* v_g_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2285_, v_lemmas_2286_, v_ctx_2287_, v_g_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2295_, lean_object* v_lemmas_2296_, lean_object* v_ctx_2297_, lean_object* v_g_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; 
lean_inc(v_g_2298_);
lean_inc_ref(v_cfg_2295_);
v___x_2304_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2295_, v_g_2298_, v_lemmas_2296_, v_ctx_2297_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_toApplyRulesConfig_2305_; lean_object* v_a_2306_; lean_object* v_toApplyConfig_2307_; uint8_t v_transparency_2308_; lean_object* v___x_2309_; 
v_toApplyRulesConfig_2305_ = lean_ctor_get(v_cfg_2295_, 0);
lean_inc_ref(v_toApplyRulesConfig_2305_);
lean_dec_ref(v_cfg_2295_);
v_a_2306_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2304_, 1);
v_toApplyConfig_2307_ = lean_ctor_get(v_toApplyRulesConfig_2305_, 1);
lean_inc_ref(v_toApplyConfig_2307_);
v_transparency_2308_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2305_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2305_);
v___x_2309_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2307_, v_transparency_2308_, v_a_2306_, v_g_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2309_;
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_g_2298_);
lean_dec_ref(v_cfg_2295_);
v_a_2310_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2304_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2304_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2318_, lean_object* v_lemmas_2319_, lean_object* v_ctx_2320_, lean_object* v_g_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2318_, v_lemmas_2319_, v_ctx_2320_, v_g_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2328_, lean_object* v_i_2329_, lean_object* v_k_2330_){
_start:
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = lean_array_get_size(v_keys_2328_);
v___x_2332_ = lean_nat_dec_lt(v_i_2329_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec(v_i_2329_);
return v___x_2332_;
}
else
{
lean_object* v_k_x27_2333_; uint8_t v___x_2334_; 
v_k_x27_2333_ = lean_array_fget_borrowed(v_keys_2328_, v_i_2329_);
v___x_2334_ = l_Lean_instBEqMVarId_beq(v_k_2330_, v_k_x27_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_unsigned_to_nat(1u);
v___x_2336_ = lean_nat_add(v_i_2329_, v___x_2335_);
lean_dec(v_i_2329_);
v_i_2329_ = v___x_2336_;
goto _start;
}
else
{
lean_dec(v_i_2329_);
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2338_, lean_object* v_i_2339_, lean_object* v_k_2340_){
_start:
{
uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_res_2341_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2338_, v_i_2339_, v_k_2340_);
lean_dec(v_k_2340_);
lean_dec_ref(v_keys_2338_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2343_, size_t v_x_2344_, lean_object* v_x_2345_){
_start:
{
if (lean_obj_tag(v_x_2343_) == 0)
{
lean_object* v_es_2346_; lean_object* v___x_2347_; size_t v___x_2348_; size_t v___x_2349_; lean_object* v_j_2350_; lean_object* v___x_2351_; 
v_es_2346_ = lean_ctor_get(v_x_2343_, 0);
v___x_2347_ = lean_box(2);
v___x_2348_ = ((size_t)31ULL);
v___x_2349_ = lean_usize_land(v_x_2344_, v___x_2348_);
v_j_2350_ = lean_usize_to_nat(v___x_2349_);
v___x_2351_ = lean_array_get_borrowed(v___x_2347_, v_es_2346_, v_j_2350_);
lean_dec(v_j_2350_);
switch(lean_obj_tag(v___x_2351_))
{
case 0:
{
lean_object* v_key_2352_; uint8_t v___x_2353_; 
v_key_2352_ = lean_ctor_get(v___x_2351_, 0);
v___x_2353_ = l_Lean_instBEqMVarId_beq(v_x_2345_, v_key_2352_);
return v___x_2353_;
}
case 1:
{
lean_object* v_node_2354_; size_t v___x_2355_; size_t v___x_2356_; 
v_node_2354_ = lean_ctor_get(v___x_2351_, 0);
v___x_2355_ = ((size_t)5ULL);
v___x_2356_ = lean_usize_shift_right(v_x_2344_, v___x_2355_);
v_x_2343_ = v_node_2354_;
v_x_2344_ = v___x_2356_;
goto _start;
}
default: 
{
uint8_t v___x_2358_; 
v___x_2358_ = 0;
return v___x_2358_;
}
}
}
else
{
lean_object* v_ks_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_ks_2359_ = lean_ctor_get(v_x_2343_, 0);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2359_, v___x_2360_, v_x_2345_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_){
_start:
{
size_t v_x_1986__boxed_2365_; uint8_t v_res_2366_; lean_object* v_r_2367_; 
v_x_1986__boxed_2365_ = lean_unbox_usize(v_x_2363_);
lean_dec(v_x_2363_);
v_res_2366_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2362_, v_x_1986__boxed_2365_, v_x_2364_);
lean_dec(v_x_2364_);
lean_dec_ref(v_x_2362_);
v_r_2367_ = lean_box(v_res_2366_);
return v_r_2367_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2368_, lean_object* v_x_2369_){
_start:
{
uint64_t v___x_2370_; size_t v___x_2371_; uint8_t v___x_2372_; 
v___x_2370_ = l_Lean_instHashableMVarId_hash(v_x_2369_);
v___x_2371_ = lean_uint64_to_usize(v___x_2370_);
v___x_2372_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2368_, v___x_2371_, v_x_2369_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2373_, v_x_2374_);
lean_dec(v_x_2374_);
lean_dec_ref(v_x_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v_mctx_2381_; lean_object* v_eAssignment_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2380_ = lean_st_ref_get(v___y_2378_);
v_mctx_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc_ref(v_mctx_2381_);
lean_dec(v___x_2380_);
v_eAssignment_2382_ = lean_ctor_get(v_mctx_2381_, 8);
lean_inc_ref(v_eAssignment_2382_);
lean_dec_ref(v_mctx_2381_);
v___x_2383_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2382_, v_mvarId_2377_);
lean_dec_ref(v_eAssignment_2382_);
v___x_2384_ = lean_box(v___x_2383_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec(v_mvarId_2386_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
if (lean_obj_tag(v_x_2391_) == 0)
{
return v_x_2390_;
}
else
{
lean_object* v_head_2392_; lean_object* v_tail_2393_; lean_object* v___x_2394_; 
v_head_2392_ = lean_ctor_get(v_x_2391_, 0);
lean_inc(v_head_2392_);
v_tail_2393_ = lean_ctor_get(v_x_2391_, 1);
lean_inc(v_tail_2393_);
lean_dec_ref_known(v_x_2391_, 2);
v___x_2394_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2390_, v_head_2392_);
v_x_2390_ = v___x_2394_;
v_x_2391_ = v_tail_2393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2396_, lean_object* v_a_2397_, uint8_t v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
if (lean_obj_tag(v_a_2399_) == 0)
{
if (lean_obj_tag(v_a_2400_) == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec(v_a_2397_);
lean_dec_ref(v_f_2396_);
v___x_2407_ = lean_box(v_a_2398_);
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v_a_2401_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
else
{
lean_object* v_head_2410_; lean_object* v_tail_2411_; 
v_head_2410_ = lean_ctor_get(v_a_2400_, 0);
lean_inc(v_head_2410_);
v_tail_2411_ = lean_ctor_get(v_a_2400_, 1);
lean_inc(v_tail_2411_);
lean_dec_ref_known(v_a_2400_, 2);
v_a_2399_ = v_head_2410_;
v_a_2400_ = v_tail_2411_;
goto _start;
}
}
else
{
lean_object* v_head_2413_; lean_object* v_tail_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2457_; 
v_head_2413_ = lean_ctor_get(v_a_2399_, 0);
v_tail_2414_ = lean_ctor_get(v_a_2399_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2416_ = v_a_2399_;
v_isShared_2417_ = v_isSharedCheck_2457_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_tail_2414_);
lean_inc(v_head_2413_);
lean_dec(v_a_2399_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2457_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2456_; 
v___x_2418_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2413_, v___y_2403_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2456_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2456_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_unbox(v_a_2419_);
lean_dec(v_a_2419_);
if (v___x_2423_ == 0)
{
lean_object* v_zero_2424_; uint8_t v_isZero_2425_; 
v_zero_2424_ = lean_unsigned_to_nat(0u);
v_isZero_2425_ = lean_nat_dec_eq(v_a_2397_, v_zero_2424_);
if (v_isZero_2425_ == 1)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
lean_del_object(v___x_2416_);
lean_dec(v_a_2397_);
lean_dec_ref(v_f_2396_);
v___x_2426_ = lean_array_push(v_a_2401_, v_head_2413_);
v___x_2427_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2426_, v_tail_2414_);
v___x_2428_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2427_, v_a_2400_);
v___x_2429_ = lean_box(v_a_2398_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___x_2428_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2430_);
v___x_2432_ = v___x_2421_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_del_object(v___x_2421_);
lean_inc_ref(v_f_2396_);
lean_inc(v_head_2413_);
v___x_2434_ = lean_apply_1(v_f_2396_, v_head_2413_);
v___x_2435_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2434_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v_one_2437_; lean_object* v_n_2438_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_one_2437_ = lean_unsigned_to_nat(1u);
v_n_2438_ = lean_nat_sub(v_a_2397_, v_one_2437_);
lean_dec(v_a_2397_);
if (lean_obj_tag(v_a_2436_) == 0)
{
lean_object* v___x_2439_; 
lean_del_object(v___x_2416_);
v___x_2439_ = lean_array_push(v_a_2401_, v_head_2413_);
v_a_2397_ = v_n_2438_;
v_a_2399_ = v_tail_2414_;
v_a_2401_ = v___x_2439_;
goto _start;
}
else
{
lean_object* v_val_2441_; uint8_t v___x_2442_; lean_object* v___x_2444_; 
lean_dec(v_head_2413_);
v_val_2441_ = lean_ctor_get(v_a_2436_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v_a_2436_, 1);
v___x_2442_ = 1;
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_a_2400_);
lean_ctor_set(v___x_2416_, 0, v_tail_2414_);
v___x_2444_ = v___x_2416_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_tail_2414_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_a_2400_);
v___x_2444_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
v_a_2397_ = v_n_2438_;
v_a_2398_ = v___x_2442_;
v_a_2399_ = v_val_2441_;
v_a_2400_ = v___x_2444_;
goto _start;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_del_object(v___x_2416_);
lean_dec(v_tail_2414_);
lean_dec(v_head_2413_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec(v_a_2397_);
lean_dec_ref(v_f_2396_);
v_a_2447_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2435_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2435_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
else
{
lean_del_object(v___x_2421_);
lean_del_object(v___x_2416_);
lean_dec(v_head_2413_);
v_a_2399_ = v_tail_2414_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v_a_2065__boxed_2469_; lean_object* v_res_2470_; 
v_a_2065__boxed_2469_ = lean_unbox(v_a_2460_);
v_res_2470_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2458_, v_a_2459_, v_a_2065__boxed_2469_, v_a_2461_, v_a_2462_, v_a_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2471_, size_t v_i_2472_, size_t v_stop_2473_, lean_object* v_b_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_a_2481_; uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2472_, v_stop_2473_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2489_; 
v___x_2486_ = lean_array_uget_borrowed(v_as_2471_, v_i_2472_);
v___x_2489_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2486_, v___y_2476_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; uint8_t v___x_2491_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = lean_unbox(v_a_2490_);
lean_dec(v_a_2490_);
if (v___x_2491_ == 0)
{
goto v___jp_2487_;
}
else
{
v_a_2481_ = v_b_2474_;
goto v___jp_2480_;
}
}
else
{
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2492_; uint8_t v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2493_ = lean_unbox(v_a_2492_);
lean_dec(v_a_2492_);
if (v___x_2493_ == 0)
{
v_a_2481_ = v_b_2474_;
goto v___jp_2480_;
}
else
{
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec_ref(v_b_2474_);
v_a_2494_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2489_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2489_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
v___jp_2487_:
{
lean_object* v___x_2488_; 
lean_inc(v___x_2486_);
v___x_2488_ = lean_array_push(v_b_2474_, v___x_2486_);
v_a_2481_ = v___x_2488_;
goto v___jp_2480_;
}
}
else
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_b_2474_);
return v___x_2502_;
}
v___jp_2480_:
{
size_t v___x_2482_; size_t v___x_2483_; 
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_add(v_i_2472_, v___x_2482_);
v_i_2472_ = v___x_2483_;
v_b_2474_ = v_a_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2503_, lean_object* v_i_2504_, lean_object* v_stop_2505_, lean_object* v_b_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
size_t v_i_boxed_2512_; size_t v_stop_boxed_2513_; lean_object* v_res_2514_; 
v_i_boxed_2512_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_stop_boxed_2513_ = lean_unbox_usize(v_stop_2505_);
lean_dec(v_stop_2505_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2503_, v_i_boxed_2512_, v_stop_boxed_2513_, v_b_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v_as_2503_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2518_ = lean_array_to_list(v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2519_, lean_object* v_goals_2520_, lean_object* v_maxIters_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2527_ = 0;
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2531_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2519_, v_maxIters_2521_, v___x_2527_, v_goals_2520_, v___x_2528_, v___x_2530_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2574_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2574_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2574_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_fst_2536_; lean_object* v_snd_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2573_; 
v_fst_2536_ = lean_ctor_get(v_a_2532_, 0);
v_snd_2537_ = lean_ctor_get(v_a_2532_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_a_2532_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2539_ = v_a_2532_;
v_isShared_2540_ = v_isSharedCheck_2573_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snd_2537_);
lean_inc(v_fst_2536_);
lean_dec(v_a_2532_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2573_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = lean_array_get_size(v_snd_2537_);
v___x_2542_ = lean_nat_dec_lt(v___x_2529_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_dec(v_snd_2537_);
v___x_2543_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2543_);
v___x_2545_ = v___x_2539_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_fst_2536_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2545_);
v___x_2547_ = v___x_2534_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
else
{
size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
lean_del_object(v___x_2534_);
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = lean_usize_of_nat(v___x_2541_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2537_, v___x_2550_, v___x_2551_, v___x_2530_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v_snd_2537_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2564_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_array_to_list(v_a_2553_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2557_);
v___x_2559_ = v___x_2539_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_fst_2536_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2561_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2559_);
v___x_2561_ = v___x_2555_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_del_object(v___x_2539_);
lean_dec(v_fst_2536_);
v_a_2565_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2552_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2552_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
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
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2531_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2531_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2583_, lean_object* v_goals_2584_, lean_object* v_maxIters_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2583_, v_goals_2584_, v_maxIters_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2591_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2595_, lean_object* v_goals_2596_, lean_object* v_maxIters_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2595_, v_goals_2596_, v_maxIters_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2616_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2616_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2616_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_fst_2608_; uint8_t v___x_2609_; 
v_fst_2608_ = lean_ctor_get(v_a_2604_, 0);
v___x_2609_ = lean_unbox(v_fst_2608_);
if (v___x_2609_ == 1)
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; 
v_snd_2610_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2610_);
lean_dec(v_a_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_snd_2610_);
v___x_2612_ = v___x_2606_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_snd_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_del_object(v___x_2606_);
lean_dec(v_a_2604_);
v___x_2614_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2615_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2614_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2615_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_a_2617_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2603_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2603_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2625_, lean_object* v_goals_2626_, lean_object* v_maxIters_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2625_, v_goals_2626_, v_maxIters_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2634_, lean_object* v_ctx_2635_, lean_object* v_cfg_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
uint8_t v_backtracking_2643_; 
v_backtracking_2643_ = lean_ctor_get_uint8(v_cfg_2636_, sizeof(void*)*1);
if (v_backtracking_2643_ == 0)
{
lean_object* v_toApplyRulesConfig_2644_; lean_object* v_toBacktrackConfig_2645_; lean_object* v_maxDepth_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_toApplyRulesConfig_2644_ = lean_ctor_get(v_cfg_2636_, 0);
v_toBacktrackConfig_2645_ = lean_ctor_get(v_toApplyRulesConfig_2644_, 0);
v_maxDepth_2646_ = lean_ctor_get(v_toBacktrackConfig_2645_, 0);
lean_inc(v_maxDepth_2646_);
v___x_2647_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2647_, 0, v_cfg_2636_);
lean_closure_set(v___x_2647_, 1, v_lemmas_2634_);
lean_closure_set(v___x_2647_, 2, v_ctx_2635_);
v___x_2648_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2647_, v_a_2637_, v_maxDepth_2646_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2648_;
}
else
{
lean_object* v_toApplyRulesConfig_2649_; lean_object* v_toBacktrackConfig_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_toApplyRulesConfig_2649_ = lean_ctor_get(v_cfg_2636_, 0);
v_toBacktrackConfig_2650_ = lean_ctor_get(v_toApplyRulesConfig_2649_, 0);
lean_inc_ref(v_toBacktrackConfig_2650_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2652_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2652_, 0, v_cfg_2636_);
lean_closure_set(v___x_2652_, 1, v_lemmas_2634_);
lean_closure_set(v___x_2652_, 2, v_ctx_2635_);
v___x_2653_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2650_, v___x_2651_, v___x_2652_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2654_, lean_object* v_ctx_2655_, lean_object* v_cfg_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2654_, v_ctx_2655_, v_cfg_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2664_, v___y_2666_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v_mvarId_2671_);
return v_res_2677_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2679_, v_x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
uint8_t v_res_2685_; lean_object* v_r_2686_; 
v_res_2685_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2682_, v_x_2683_, v_x_2684_);
lean_dec(v_x_2684_);
lean_dec_ref(v_x_2683_);
v_r_2686_ = lean_box(v_res_2685_);
return v_r_2686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2687_, lean_object* v_x_2688_, size_t v_x_2689_, lean_object* v_x_2690_){
_start:
{
uint8_t v___x_2691_; 
v___x_2691_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2688_, v_x_2689_, v_x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_){
_start:
{
size_t v_x_2511__boxed_2696_; uint8_t v_res_2697_; lean_object* v_r_2698_; 
v_x_2511__boxed_2696_ = lean_unbox_usize(v_x_2694_);
lean_dec(v_x_2694_);
v_res_2697_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2692_, v_x_2693_, v_x_2511__boxed_2696_, v_x_2695_);
lean_dec(v_x_2695_);
lean_dec_ref(v_x_2693_);
v_r_2698_ = lean_box(v_res_2697_);
return v_r_2698_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2699_, lean_object* v_keys_2700_, lean_object* v_vals_2701_, lean_object* v_heq_2702_, lean_object* v_i_2703_, lean_object* v_k_2704_){
_start:
{
uint8_t v___x_2705_; 
v___x_2705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2700_, v_i_2703_, v_k_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2706_, lean_object* v_keys_2707_, lean_object* v_vals_2708_, lean_object* v_heq_2709_, lean_object* v_i_2710_, lean_object* v_k_2711_){
_start:
{
uint8_t v_res_2712_; lean_object* v_r_2713_; 
v_res_2712_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2706_, v_keys_2707_, v_vals_2708_, v_heq_2709_, v_i_2710_, v_k_2711_);
lean_dec(v_k_2711_);
lean_dec_ref(v_vals_2708_);
lean_dec_ref(v_keys_2707_);
v_r_2713_ = lean_box(v_res_2712_);
return v_r_2713_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v_x_2725_);
return v_res_2731_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2734_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2735_ = l_Lean_Name_append(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2736_, lean_object* v_lemmas_2737_, lean_object* v_ctx_2738_, lean_object* v_goals_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_cfg_2745_; lean_object* v___x_2746_; 
v_cfg_2745_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2736_);
lean_inc(v_goals_2739_);
lean_inc_ref(v_cfg_2745_);
lean_inc_ref(v_ctx_2738_);
lean_inc(v_lemmas_2737_);
v___x_2746_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2737_, v_ctx_2738_, v_cfg_2745_, v_goals_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_dec_ref(v_cfg_2745_);
lean_dec(v_goals_2739_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
return v___x_2746_;
}
else
{
lean_object* v_a_2747_; lean_object* v___f_2748_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; uint8_t v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v_a_2757_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; uint8_t v___y_2773_; uint8_t v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v_a_2777_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v_a_2787_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; uint8_t v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; lean_object* v_a_2804_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; uint8_t v___y_2849_; uint8_t v___x_2902_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
v___f_2748_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_2902_ = l_Lean_Exception_isInterrupt(v_a_2747_);
if (v___x_2902_ == 0)
{
uint8_t v___x_2903_; 
v___x_2903_ = l_Lean_Exception_isRuntime(v_a_2747_);
v___y_2849_ = v___x_2903_;
goto v___jp_2848_;
}
else
{
lean_dec(v_a_2747_);
v___y_2849_ = v___x_2902_;
goto v___jp_2848_;
}
v___jp_2749_:
{
lean_object* v___x_2758_; double v___x_2759_; double v___x_2760_; double v___x_2761_; double v___x_2762_; double v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2758_ = lean_io_mono_nanos_now();
v___x_2759_ = lean_float_of_nat(v___y_2755_);
v___x_2760_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2761_ = lean_float_div(v___x_2759_, v___x_2760_);
v___x_2762_ = lean_float_of_nat(v___x_2758_);
v___x_2763_ = lean_float_div(v___x_2762_, v___x_2760_);
v___x_2764_ = lean_box_float(v___x_2761_);
v___x_2765_ = lean_box_float(v___x_2763_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_a_2757_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2756_);
v___x_2768_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2756_, v___y_2754_, v___y_2752_, v___y_2750_, v___y_2753_, v___y_2751_, v___f_2748_, v___x_2767_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2768_;
}
v___jp_2769_:
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v_a_2777_);
v___y_2750_ = v___y_2770_;
v___y_2751_ = v___y_2771_;
v___y_2752_ = v___y_2772_;
v___y_2753_ = v___y_2774_;
v___y_2754_ = v___y_2773_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2776_;
v_a_2757_ = v___x_2778_;
goto v___jp_2749_;
}
v___jp_2779_:
{
lean_object* v___x_2788_; double v___x_2789_; double v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2788_ = lean_io_get_num_heartbeats();
v___x_2789_ = lean_float_of_nat(v___y_2785_);
v___x_2790_ = lean_float_of_nat(v___x_2788_);
v___x_2791_ = lean_box_float(v___x_2789_);
v___x_2792_ = lean_box_float(v___x_2790_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2787_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2786_);
v___x_2795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2786_, v___y_2784_, v___y_2782_, v___y_2780_, v___y_2783_, v___y_2781_, v___f_2748_, v___x_2794_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2795_;
}
v___jp_2796_:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2804_);
v___y_2780_ = v___y_2797_;
v___y_2781_ = v___y_2798_;
v___y_2782_ = v___y_2799_;
v___y_2783_ = v___y_2802_;
v___y_2784_ = v___y_2801_;
v___y_2785_ = v___y_2800_;
v___y_2786_ = v___y_2803_;
v_a_2787_ = v___x_2805_;
goto v___jp_2779_;
}
v___jp_2806_:
{
lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2814_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2743_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2817_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2807_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_io_mono_nanos_now();
v___x_2819_ = l_Lean_MVarId_exfalso(v___y_2811_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2820_);
lean_ctor_set(v___x_2821_, 1, v___y_2812_);
v___x_2822_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2737_, v_ctx_2738_, v_cfg_2745_, v___x_2821_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 1);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
v___y_2750_ = v___y_2807_;
v___y_2751_ = v_a_2815_;
v___y_2752_ = v___y_2808_;
v___y_2753_ = v___y_2810_;
v___y_2754_ = v___y_2809_;
v___y_2755_ = v___x_2818_;
v___y_2756_ = v___y_2813_;
v_a_2757_ = v___x_2828_;
goto v___jp_2749_;
}
}
}
else
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2822_, 1);
v___y_2770_ = v___y_2807_;
v___y_2771_ = v_a_2815_;
v___y_2772_ = v___y_2808_;
v___y_2773_ = v___y_2809_;
v___y_2774_ = v___y_2810_;
v___y_2775_ = v___x_2818_;
v___y_2776_ = v___y_2813_;
v_a_2777_ = v_a_2831_;
goto v___jp_2769_;
}
}
else
{
lean_object* v_a_2832_; 
lean_dec(v___y_2812_);
lean_dec_ref(v_cfg_2745_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
v_a_2832_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2819_, 1);
v___y_2770_ = v___y_2807_;
v___y_2771_ = v_a_2815_;
v___y_2772_ = v___y_2808_;
v___y_2773_ = v___y_2809_;
v___y_2774_ = v___y_2810_;
v___y_2775_ = v___x_2818_;
v___y_2776_ = v___y_2813_;
v_a_2777_ = v_a_2832_;
goto v___jp_2769_;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_io_get_num_heartbeats();
v___x_2834_ = l_Lean_MVarId_exfalso(v___y_2811_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2835_);
lean_ctor_set(v___x_2836_, 1, v___y_2812_);
v___x_2837_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2737_, v_ctx_2738_, v_cfg_2745_, v___x_2836_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 1);
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
v___y_2780_ = v___y_2807_;
v___y_2781_ = v_a_2815_;
v___y_2782_ = v___y_2808_;
v___y_2783_ = v___y_2810_;
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___x_2833_;
v___y_2786_ = v___y_2813_;
v_a_2787_ = v___x_2843_;
goto v___jp_2779_;
}
}
}
else
{
lean_object* v_a_2846_; 
v_a_2846_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2837_, 1);
v___y_2797_ = v___y_2807_;
v___y_2798_ = v_a_2815_;
v___y_2799_ = v___y_2808_;
v___y_2800_ = v___x_2833_;
v___y_2801_ = v___y_2809_;
v___y_2802_ = v___y_2810_;
v___y_2803_ = v___y_2813_;
v_a_2804_ = v_a_2846_;
goto v___jp_2796_;
}
}
else
{
lean_object* v_a_2847_; 
lean_dec(v___y_2812_);
lean_dec_ref(v_cfg_2745_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
v_a_2847_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2834_, 1);
v___y_2797_ = v___y_2807_;
v___y_2798_ = v_a_2815_;
v___y_2799_ = v___y_2808_;
v___y_2800_ = v___x_2833_;
v___y_2801_ = v___y_2809_;
v___y_2802_ = v___y_2810_;
v___y_2803_ = v___y_2813_;
v_a_2804_ = v_a_2847_;
goto v___jp_2796_;
}
}
}
v___jp_2848_:
{
if (v___y_2849_ == 0)
{
if (lean_obj_tag(v_goals_2739_) == 1)
{
lean_object* v_tail_2850_; 
v_tail_2850_ = lean_ctor_get(v_goals_2739_, 1);
lean_inc(v_tail_2850_);
if (lean_obj_tag(v_tail_2850_) == 0)
{
lean_object* v_toApplyRulesConfig_2851_; uint8_t v_exfalso_2852_; 
v_toApplyRulesConfig_2851_ = lean_ctor_get(v_cfg_2745_, 0);
lean_inc_ref(v_toApplyRulesConfig_2851_);
v_exfalso_2852_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2851_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2851_);
if (v_exfalso_2852_ == 1)
{
lean_object* v_options_2853_; uint8_t v_hasTrace_2854_; 
lean_dec_ref_known(v___x_2746_, 1);
v_options_2853_ = lean_ctor_get(v_a_2742_, 2);
v_hasTrace_2854_ = lean_ctor_get_uint8(v_options_2853_, sizeof(void*)*1);
if (v_hasTrace_2854_ == 0)
{
lean_object* v_head_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2873_; 
v_head_2855_ = lean_ctor_get(v_goals_2739_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_goals_2739_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v_goals_2739_, 1);
lean_dec(v_unused_2874_);
v___x_2857_ = v_goals_2739_;
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_head_2855_);
lean_dec(v_goals_2739_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_MVarId_exfalso(v_head_2855_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v_a_2860_);
v___x_2862_ = v___x_2857_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2860_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_tail_2850_);
v___x_2862_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2737_, v_ctx_2738_, v_cfg_2745_, v___x_2862_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2863_;
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_del_object(v___x_2857_);
lean_dec_ref(v_cfg_2745_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
v_a_2865_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2859_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2859_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
else
{
lean_object* v_head_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2900_; 
v_head_2875_ = lean_ctor_get(v_goals_2739_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_goals_2739_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v_goals_2739_, 1);
lean_dec(v_unused_2901_);
v___x_2877_ = v_goals_2739_;
v_isShared_2878_ = v_isSharedCheck_2900_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_head_2875_);
lean_dec(v_goals_2739_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2900_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_inheritedTraceOptions_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_inheritedTraceOptions_2879_ = lean_ctor_get(v_a_2742_, 13);
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2881_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2882_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2879_, v_options_2853_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = l_Lean_trace_profiler;
v___x_2885_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2853_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_MVarId_exfalso(v_head_2875_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2889_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v_a_2887_);
v___x_2889_ = v___x_2877_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2887_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_tail_2850_);
v___x_2889_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2737_, v_ctx_2738_, v_cfg_2745_, v___x_2889_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2890_;
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_del_object(v___x_2877_);
lean_dec_ref(v_cfg_2745_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
v_a_2892_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2886_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2886_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_del_object(v___x_2877_);
v___y_2807_ = v_options_2853_;
v___y_2808_ = v___x_2881_;
v___y_2809_ = v_exfalso_2852_;
v___y_2810_ = v___x_2883_;
v___y_2811_ = v_head_2875_;
v___y_2812_ = v_tail_2850_;
v___y_2813_ = v___x_2880_;
goto v___jp_2806_;
}
}
else
{
lean_del_object(v___x_2877_);
v___y_2807_ = v_options_2853_;
v___y_2808_ = v___x_2881_;
v___y_2809_ = v_exfalso_2852_;
v___y_2810_ = v___x_2883_;
v___y_2811_ = v_head_2875_;
v___y_2812_ = v_tail_2850_;
v___y_2813_ = v___x_2880_;
goto v___jp_2806_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2739_, 2);
lean_dec_ref(v_cfg_2745_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
return v___x_2746_;
}
}
else
{
lean_dec(v_tail_2850_);
lean_dec_ref_known(v_goals_2739_, 2);
lean_dec_ref(v_cfg_2745_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
return v___x_2746_;
}
}
else
{
lean_dec_ref(v_cfg_2745_);
lean_dec(v_goals_2739_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
return v___x_2746_;
}
}
else
{
lean_dec_ref(v_cfg_2745_);
lean_dec(v_goals_2739_);
lean_dec_ref(v_ctx_2738_);
lean_dec(v_lemmas_2737_);
return v___x_2746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2904_, lean_object* v_lemmas_2905_, lean_object* v_ctx_2906_, lean_object* v_goals_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2904_, v_lemmas_2905_, v_ctx_2906_, v_goals_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
if (lean_obj_tag(v_x_2914_) == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = l_List_reverse___redArg(v_x_2915_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
else
{
lean_object* v_head_2923_; lean_object* v_tail_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2947_; 
v_head_2923_ = lean_ctor_get(v_x_2914_, 0);
v_tail_2924_ = lean_ctor_get(v_x_2914_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_x_2914_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2926_ = v_x_2914_;
v_isShared_2927_ = v_isSharedCheck_2947_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_tail_2924_);
lean_inc(v_head_2923_);
lean_dec(v_x_2914_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2947_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Expr_applySymm(v_head_2923_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2931_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v_x_2915_);
lean_ctor_set(v___x_2926_, 0, v_a_2929_);
v___x_2931_ = v___x_2926_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2929_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_x_2915_);
v___x_2931_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
v_x_2914_ = v_tail_2924_;
v_x_2915_ = v___x_2931_;
goto _start;
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2946_; 
lean_del_object(v___x_2926_);
v_a_2934_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2936_ = v___x_2928_;
v_isShared_2937_ = v_isSharedCheck_2946_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2928_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2946_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
uint8_t v___y_2939_; uint8_t v___x_2944_; 
v___x_2944_ = l_Lean_Exception_isInterrupt(v_a_2934_);
if (v___x_2944_ == 0)
{
uint8_t v___x_2945_; 
lean_inc(v_a_2934_);
v___x_2945_ = l_Lean_Exception_isRuntime(v_a_2934_);
v___y_2939_ = v___x_2945_;
goto v___jp_2938_;
}
else
{
v___y_2939_ = v___x_2944_;
goto v___jp_2938_;
}
v___jp_2938_:
{
if (v___y_2939_ == 0)
{
lean_del_object(v___x_2936_);
lean_dec(v_a_2934_);
v_x_2914_ = v_tail_2924_;
goto _start;
}
else
{
lean_object* v___x_2942_; 
lean_dec(v_tail_2924_);
lean_dec(v_x_2915_);
if (v_isShared_2937_ == 0)
{
v___x_2942_ = v___x_2936_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2934_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2948_, v_x_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2956_, lean_object* v_hyps_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
if (v_symm_2956_ == 0)
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_hyps_2957_);
return v___x_2963_;
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_box(0);
lean_inc(v_hyps_2957_);
v___x_2965_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2957_, v___x_2964_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2974_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2970_ = l_List_appendTR___redArg(v_hyps_2957_, v_a_2966_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2970_);
v___x_2972_ = v___x_2968_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_dec(v_hyps_2957_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_2975_, lean_object* v_hyps_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
uint8_t v_symm_boxed_2982_; lean_object* v_res_2983_; 
v_symm_boxed_2982_ = lean_unbox(v_symm_2975_);
v_res_2983_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_2982_, v_hyps_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_2984_, size_t v_sz_2985_, size_t v_i_2986_, lean_object* v_b_2987_){
_start:
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_usize_dec_lt(v_i_2986_, v_sz_2985_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_b_2987_);
return v___x_2990_;
}
else
{
lean_object* v_snd_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3009_; 
v_snd_2991_ = lean_ctor_get(v_b_2987_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_b_2987_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v_b_2987_, 0);
lean_dec(v_unused_3010_);
v___x_2993_ = v_b_2987_;
v_isShared_2994_ = v_isSharedCheck_3009_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snd_2991_);
lean_dec(v_b_2987_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3009_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v_a_2997_; lean_object* v_a_3004_; 
v___x_2995_ = lean_box(0);
v_a_3004_ = lean_array_uget_borrowed(v_as_2984_, v_i_2986_);
if (lean_obj_tag(v_a_3004_) == 0)
{
v_a_2997_ = v_snd_2991_;
goto v___jp_2996_;
}
else
{
lean_object* v_val_3005_; uint8_t v___x_3006_; 
v_val_3005_ = lean_ctor_get(v_a_3004_, 0);
v___x_3006_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_inc(v_val_3005_);
v___x_3007_ = l_Lean_LocalDecl_toExpr(v_val_3005_);
v___x_3008_ = lean_array_push(v_snd_2991_, v___x_3007_);
v_a_2997_ = v___x_3008_;
goto v___jp_2996_;
}
else
{
v_a_2997_ = v_snd_2991_;
goto v___jp_2996_;
}
}
v___jp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_a_2997_);
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2999_ = v___x_2993_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_a_2997_);
v___x_2999_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
size_t v___x_3000_; size_t v___x_3001_; 
v___x_3000_ = ((size_t)1ULL);
v___x_3001_ = lean_usize_add(v_i_2986_, v___x_3000_);
v_i_2986_ = v___x_3001_;
v_b_2987_ = v___x_2999_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3011_, lean_object* v_sz_3012_, lean_object* v_i_3013_, lean_object* v_b_3014_, lean_object* v___y_3015_){
_start:
{
size_t v_sz_boxed_3016_; size_t v_i_boxed_3017_; lean_object* v_res_3018_; 
v_sz_boxed_3016_ = lean_unbox_usize(v_sz_3012_);
lean_dec(v_sz_3012_);
v_i_boxed_3017_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_res_3018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3011_, v_sz_boxed_3016_, v_i_boxed_3017_, v_b_3014_);
lean_dec_ref(v_as_3011_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3019_, size_t v_sz_3020_, size_t v_i_3021_, lean_object* v_b_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_usize_dec_lt(v_i_3021_, v_sz_3020_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_b_3022_);
return v___x_3031_;
}
else
{
lean_object* v_snd_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3050_; 
v_snd_3032_ = lean_ctor_get(v_b_3022_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_b_3022_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; 
v_unused_3051_ = lean_ctor_get(v_b_3022_, 0);
lean_dec(v_unused_3051_);
v___x_3034_ = v_b_3022_;
v_isShared_3035_ = v_isSharedCheck_3050_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_snd_3032_);
lean_dec(v_b_3022_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3050_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v_a_3038_; lean_object* v_a_3045_; 
v___x_3036_ = lean_box(0);
v_a_3045_ = lean_array_uget_borrowed(v_as_3019_, v_i_3021_);
if (lean_obj_tag(v_a_3045_) == 0)
{
v_a_3038_ = v_snd_3032_;
goto v___jp_3037_;
}
else
{
lean_object* v_val_3046_; uint8_t v___x_3047_; 
v_val_3046_ = lean_ctor_get(v_a_3045_, 0);
v___x_3047_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_inc(v_val_3046_);
v___x_3048_ = l_Lean_LocalDecl_toExpr(v_val_3046_);
v___x_3049_ = lean_array_push(v_snd_3032_, v___x_3048_);
v_a_3038_ = v___x_3049_;
goto v___jp_3037_;
}
else
{
v_a_3038_ = v_snd_3032_;
goto v___jp_3037_;
}
}
v___jp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 1, v_a_3038_);
lean_ctor_set(v___x_3034_, 0, v___x_3036_);
v___x_3040_ = v___x_3034_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_a_3038_);
v___x_3040_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
size_t v___x_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = ((size_t)1ULL);
v___x_3042_ = lean_usize_add(v_i_3021_, v___x_3041_);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3019_, v_sz_3020_, v___x_3042_, v___x_3040_);
return v___x_3043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3052_, lean_object* v_sz_3053_, lean_object* v_i_3054_, lean_object* v_b_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
size_t v_sz_boxed_3063_; size_t v_i_boxed_3064_; lean_object* v_res_3065_; 
v_sz_boxed_3063_ = lean_unbox_usize(v_sz_3053_);
lean_dec(v_sz_3053_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3054_);
lean_dec(v_i_3054_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3052_, v_sz_boxed_3063_, v_i_boxed_3064_, v_b_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v_as_3052_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3066_, size_t v_sz_3067_, size_t v_i_3068_, lean_object* v_b_3069_){
_start:
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_usize_dec_lt(v_i_3068_, v_sz_3067_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_b_3069_);
return v___x_3072_;
}
else
{
lean_object* v_snd_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3091_; 
v_snd_3073_ = lean_ctor_get(v_b_3069_, 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_b_3069_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_b_3069_, 0);
lean_dec(v_unused_3092_);
v___x_3075_ = v_b_3069_;
v_isShared_3076_ = v_isSharedCheck_3091_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_snd_3073_);
lean_dec(v_b_3069_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3091_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v_a_3079_; lean_object* v_a_3086_; 
v___x_3077_ = lean_box(0);
v_a_3086_ = lean_array_uget_borrowed(v_as_3066_, v_i_3068_);
if (lean_obj_tag(v_a_3086_) == 0)
{
v_a_3079_ = v_snd_3073_;
goto v___jp_3078_;
}
else
{
lean_object* v_val_3087_; uint8_t v___x_3088_; 
v_val_3087_ = lean_ctor_get(v_a_3086_, 0);
v___x_3088_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_inc(v_val_3087_);
v___x_3089_ = l_Lean_LocalDecl_toExpr(v_val_3087_);
v___x_3090_ = lean_array_push(v_snd_3073_, v___x_3089_);
v_a_3079_ = v___x_3090_;
goto v___jp_3078_;
}
else
{
v_a_3079_ = v_snd_3073_;
goto v___jp_3078_;
}
}
v___jp_3078_:
{
lean_object* v___x_3081_; 
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 1, v_a_3079_);
lean_ctor_set(v___x_3075_, 0, v___x_3077_);
v___x_3081_ = v___x_3075_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_a_3079_);
v___x_3081_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
size_t v___x_3082_; size_t v___x_3083_; 
v___x_3082_ = ((size_t)1ULL);
v___x_3083_ = lean_usize_add(v_i_3068_, v___x_3082_);
v_i_3068_ = v___x_3083_;
v_b_3069_ = v___x_3081_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3093_, lean_object* v_sz_3094_, lean_object* v_i_3095_, lean_object* v_b_3096_, lean_object* v___y_3097_){
_start:
{
size_t v_sz_boxed_3098_; size_t v_i_boxed_3099_; lean_object* v_res_3100_; 
v_sz_boxed_3098_ = lean_unbox_usize(v_sz_3094_);
lean_dec(v_sz_3094_);
v_i_boxed_3099_ = lean_unbox_usize(v_i_3095_);
lean_dec(v_i_3095_);
v_res_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3093_, v_sz_boxed_3098_, v_i_boxed_3099_, v_b_3096_);
lean_dec_ref(v_as_3093_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3101_, size_t v_sz_3102_, size_t v_i_3103_, lean_object* v_b_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_usize_dec_lt(v_i_3103_, v_sz_3102_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_b_3104_);
return v___x_3113_;
}
else
{
lean_object* v_snd_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3132_; 
v_snd_3114_ = lean_ctor_get(v_b_3104_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_b_3104_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v_b_3104_, 0);
lean_dec(v_unused_3133_);
v___x_3116_ = v_b_3104_;
v_isShared_3117_ = v_isSharedCheck_3132_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_snd_3114_);
lean_dec(v_b_3104_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3132_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v_a_3120_; lean_object* v_a_3127_; 
v___x_3118_ = lean_box(0);
v_a_3127_ = lean_array_uget_borrowed(v_as_3101_, v_i_3103_);
if (lean_obj_tag(v_a_3127_) == 0)
{
v_a_3120_ = v_snd_3114_;
goto v___jp_3119_;
}
else
{
lean_object* v_val_3128_; uint8_t v___x_3129_; 
v_val_3128_ = lean_ctor_get(v_a_3127_, 0);
v___x_3129_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3128_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_inc(v_val_3128_);
v___x_3130_ = l_Lean_LocalDecl_toExpr(v_val_3128_);
v___x_3131_ = lean_array_push(v_snd_3114_, v___x_3130_);
v_a_3120_ = v___x_3131_;
goto v___jp_3119_;
}
else
{
v_a_3120_ = v_snd_3114_;
goto v___jp_3119_;
}
}
v___jp_3119_:
{
lean_object* v___x_3122_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v_a_3120_);
lean_ctor_set(v___x_3116_, 0, v___x_3118_);
v___x_3122_ = v___x_3116_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_a_3120_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((size_t)1ULL);
v___x_3124_ = lean_usize_add(v_i_3103_, v___x_3123_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3101_, v_sz_3102_, v___x_3124_, v___x_3122_);
return v___x_3125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3134_, lean_object* v_sz_3135_, lean_object* v_i_3136_, lean_object* v_b_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
size_t v_sz_boxed_3145_; size_t v_i_boxed_3146_; lean_object* v_res_3147_; 
v_sz_boxed_3145_ = lean_unbox_usize(v_sz_3135_);
lean_dec(v_sz_3135_);
v_i_boxed_3146_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3134_, v_sz_boxed_3145_, v_i_boxed_3146_, v_b_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec_ref(v_as_3134_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3148_, lean_object* v_n_3149_, lean_object* v_b_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
if (lean_obj_tag(v_n_3149_) == 0)
{
lean_object* v_cs_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; size_t v_sz_3161_; size_t v___x_3162_; lean_object* v___x_3163_; 
v_cs_3158_ = lean_ctor_get(v_n_3149_, 0);
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v_b_3150_);
v_sz_3161_ = lean_array_size(v_cs_3158_);
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3148_, v_cs_3158_, v_sz_3161_, v___x_3162_, v___x_3160_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3178_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3178_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3178_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v_fst_3168_; 
v_fst_3168_ = lean_ctor_get(v_a_3164_, 0);
if (lean_obj_tag(v_fst_3168_) == 0)
{
lean_object* v_snd_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v_snd_3169_ = lean_ctor_get(v_a_3164_, 1);
lean_inc(v_snd_3169_);
lean_dec(v_a_3164_);
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v_snd_3169_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3170_);
v___x_3172_ = v___x_3166_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
else
{
lean_object* v_val_3174_; lean_object* v___x_3176_; 
lean_inc_ref(v_fst_3168_);
lean_dec(v_a_3164_);
v_val_3174_ = lean_ctor_get(v_fst_3168_, 0);
lean_inc(v_val_3174_);
lean_dec_ref_known(v_fst_3168_, 1);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v_val_3174_);
v___x_3176_ = v___x_3166_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_val_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_a_3179_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3163_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3163_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_vs_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; size_t v_sz_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v_vs_3187_ = lean_ctor_get(v_n_3149_, 0);
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v_b_3150_);
v_sz_3190_ = lean_array_size(v_vs_3187_);
v___x_3191_ = ((size_t)0ULL);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3187_, v_sz_3190_, v___x_3191_, v___x_3189_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3207_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_fst_3197_; 
v_fst_3197_ = lean_ctor_get(v_a_3193_, 0);
if (lean_obj_tag(v_fst_3197_) == 0)
{
lean_object* v_snd_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v_snd_3198_ = lean_ctor_get(v_a_3193_, 1);
lean_inc(v_snd_3198_);
lean_dec(v_a_3193_);
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v_snd_3198_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3199_);
v___x_3201_ = v___x_3195_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
else
{
lean_object* v_val_3203_; lean_object* v___x_3205_; 
lean_inc_ref(v_fst_3197_);
lean_dec(v_a_3193_);
v_val_3203_ = lean_ctor_get(v_fst_3197_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v_fst_3197_, 1);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_val_3203_);
v___x_3205_ = v___x_3195_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_val_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v_a_3208_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3192_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3192_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3216_, lean_object* v_as_3217_, size_t v_sz_3218_, size_t v_i_3219_, lean_object* v_b_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
uint8_t v___x_3228_; 
v___x_3228_ = lean_usize_dec_lt(v_i_3219_, v_sz_3218_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_b_3220_);
return v___x_3229_;
}
else
{
lean_object* v_snd_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3264_; 
v_snd_3230_ = lean_ctor_get(v_b_3220_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_b_3220_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_b_3220_, 0);
lean_dec(v_unused_3265_);
v___x_3232_ = v_b_3220_;
v_isShared_3233_ = v_isSharedCheck_3264_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_snd_3230_);
lean_dec(v_b_3220_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3264_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v_a_3234_; lean_object* v___x_3235_; 
v_a_3234_ = lean_array_uget_borrowed(v_as_3217_, v_i_3219_);
lean_inc(v_snd_3230_);
v___x_3235_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3216_, v_a_3234_, v_snd_3230_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3255_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3255_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3255_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
if (lean_obj_tag(v_a_3236_) == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_a_3236_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3240_);
v___x_3242_ = v___x_3232_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_snd_3230_);
v___x_3242_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3242_);
v___x_3244_ = v___x_3238_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
lean_del_object(v___x_3238_);
lean_dec(v_snd_3230_);
v_a_3247_ = lean_ctor_get(v_a_3236_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v_a_3236_, 1);
v___x_3248_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 1, v_a_3247_);
lean_ctor_set(v___x_3232_, 0, v___x_3248_);
v___x_3250_ = v___x_3232_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_a_3247_);
v___x_3250_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
size_t v___x_3251_; size_t v___x_3252_; 
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3219_, v___x_3251_);
v_i_3219_ = v___x_3252_;
v_b_3220_ = v___x_3250_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_del_object(v___x_3232_);
lean_dec(v_snd_3230_);
v_a_3256_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3235_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3235_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3266_, lean_object* v_as_3267_, lean_object* v_sz_3268_, lean_object* v_i_3269_, lean_object* v_b_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3268_);
lean_dec(v_sz_3268_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3269_);
lean_dec(v_i_3269_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3266_, v_as_3267_, v_sz_boxed_3278_, v_i_boxed_3279_, v_b_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v_as_3267_);
lean_dec_ref(v_init_3266_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3281_, lean_object* v_n_3282_, lean_object* v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3281_, v_n_3282_, v_b_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec_ref(v_n_3282_);
lean_dec_ref(v_init_3281_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3292_, lean_object* v_init_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_root_3301_; lean_object* v_tail_3302_; lean_object* v___x_3303_; 
v_root_3301_ = lean_ctor_get(v_t_3292_, 0);
v_tail_3302_ = lean_ctor_get(v_t_3292_, 1);
lean_inc_ref(v_init_3293_);
v___x_3303_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3293_, v_root_3301_, v_init_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec_ref(v_init_3293_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3340_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3340_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3340_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
if (lean_obj_tag(v_a_3304_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; 
v_a_3308_ = lean_ctor_get(v_a_3304_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v_a_3304_, 1);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v_a_3308_);
v___x_3310_ = v___x_3306_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; size_t v_sz_3315_; size_t v___x_3316_; lean_object* v___x_3317_; 
lean_del_object(v___x_3306_);
v_a_3312_ = lean_ctor_get(v_a_3304_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v_a_3304_, 1);
v___x_3313_ = lean_box(0);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v_a_3312_);
v_sz_3315_ = lean_array_size(v_tail_3302_);
v___x_3316_ = ((size_t)0ULL);
v___x_3317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3302_, v_sz_3315_, v___x_3316_, v___x_3314_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3331_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3331_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3331_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v_fst_3322_; 
v_fst_3322_ = lean_ctor_get(v_a_3318_, 0);
if (lean_obj_tag(v_fst_3322_) == 0)
{
lean_object* v_snd_3323_; lean_object* v___x_3325_; 
v_snd_3323_ = lean_ctor_get(v_a_3318_, 1);
lean_inc(v_snd_3323_);
lean_dec(v_a_3318_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_snd_3323_);
v___x_3325_ = v___x_3320_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_snd_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
else
{
lean_object* v_val_3327_; lean_object* v___x_3329_; 
lean_inc_ref(v_fst_3322_);
lean_dec(v_a_3318_);
v_val_3327_ = lean_ctor_get(v_fst_3322_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v_fst_3322_, 1);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_val_3327_);
v___x_3329_ = v___x_3320_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_val_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_a_3332_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3317_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3317_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
v_a_3341_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3303_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3303_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3349_, lean_object* v_init_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3349_, v_init_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec_ref(v_t_3349_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_lctx_3368_; lean_object* v_decls_3369_; lean_object* v_hs_3370_; lean_object* v___x_3371_; 
v_lctx_3368_ = lean_ctor_get(v___y_3363_, 2);
v_decls_3369_ = lean_ctor_get(v_lctx_3368_, 1);
v_hs_3370_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3371_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3369_, v_hs_3370_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3380_, lean_object* v_cfg_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
if (v_only_3380_ == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_toApplyRulesConfig_3390_; lean_object* v_a_3391_; uint8_t v_symm_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v_toApplyRulesConfig_3390_ = lean_ctor_get(v_cfg_3381_, 0);
v_a_3391_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3389_, 1);
v_symm_3392_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3390_, sizeof(void*)*2 + 1);
v___x_3393_ = lean_array_to_list(v_a_3391_);
v___x_3394_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3392_, v___x_3393_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
return v___x_3394_;
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_a_3395_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3389_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3389_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_box(0);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3405_, lean_object* v_cfg_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_only_boxed_3414_; lean_object* v_res_3415_; 
v_only_boxed_3414_ = lean_unbox(v_only_3405_);
v_res_3415_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3414_, v_cfg_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec_ref(v_cfg_3406_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3416_, lean_object* v_lemmas_3417_, uint8_t v_only_3418_, lean_object* v_g_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_toApplyRulesConfig_3425_; uint8_t v_intro_3426_; uint8_t v_constructor_3427_; uint8_t v_suggestions_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3441_; 
v_toApplyRulesConfig_3425_ = lean_ctor_get(v_cfg_3416_, 0);
v_intro_3426_ = lean_ctor_get_uint8(v_cfg_3416_, sizeof(void*)*1 + 1);
v_constructor_3427_ = lean_ctor_get_uint8(v_cfg_3416_, sizeof(void*)*1 + 2);
v_suggestions_3428_ = lean_ctor_get_uint8(v_cfg_3416_, sizeof(void*)*1 + 3);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_cfg_3416_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3430_ = v_cfg_3416_;
v_isShared_3431_ = v_isSharedCheck_3441_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_toApplyRulesConfig_3425_);
lean_dec(v_cfg_3416_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3441_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v_ctx_3433_; uint8_t v___x_3434_; lean_object* v___x_3436_; 
v___x_3432_ = lean_box(v_only_3418_);
v_ctx_3433_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3433_, 0, v___x_3432_);
v___x_3434_ = 0;
if (v_isShared_3431_ == 0)
{
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_toApplyRulesConfig_3425_);
lean_ctor_set_uint8(v_reuseFailAlloc_3440_, sizeof(void*)*1 + 1, v_intro_3426_);
lean_ctor_set_uint8(v_reuseFailAlloc_3440_, sizeof(void*)*1 + 2, v_constructor_3427_);
lean_ctor_set_uint8(v_reuseFailAlloc_3440_, sizeof(void*)*1 + 3, v_suggestions_3428_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*1, v___x_3434_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3438_, 0, v_g_3419_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3436_, v_lemmas_3417_, v_ctx_3433_, v___x_3438_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
return v___x_3439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3442_, lean_object* v_lemmas_3443_, lean_object* v_only_3444_, lean_object* v_g_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
uint8_t v_only_boxed_3451_; lean_object* v_res_3452_; 
v_only_boxed_3451_ = lean_unbox(v_only_3444_);
v_res_3452_ = l_Lean_MVarId_applyRules(v_cfg_3442_, v_lemmas_3443_, v_only_boxed_3451_, v_g_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3453_, size_t v_sz_3454_, size_t v_i_3455_, lean_object* v_b_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3453_, v_sz_3454_, v_i_3455_, v_b_3456_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3465_, lean_object* v_sz_3466_, lean_object* v_i_3467_, lean_object* v_b_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3466_);
lean_dec(v_sz_3466_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3467_);
lean_dec(v_i_3467_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3465_, v_sz_boxed_3476_, v_i_boxed_3477_, v_b_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec_ref(v_as_3465_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3479_, size_t v_sz_3480_, size_t v_i_3481_, lean_object* v_b_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3479_, v_sz_3480_, v_i_3481_, v_b_3482_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3491_, lean_object* v_sz_3492_, lean_object* v_i_3493_, lean_object* v_b_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3492_);
lean_dec(v_sz_3492_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3493_);
lean_dec(v_i_3493_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3491_, v_sz_boxed_3502_, v_i_boxed_3503_, v_b_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec_ref(v_as_3491_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v___x_3513_; uint8_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_box(0);
v___x_3514_ = 1;
v___x_3515_ = l_Lean_Elab_Term_elabTerm(v_t_3505_, v___x_3513_, v___x_3514_, v___x_3514_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_ref_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_ref_3530_ = lean_ctor_get(v___y_3527_, 5);
v___x_3531_ = 0;
v___x_3532_ = l_Lean_SourceInfo_fromRef(v_ref_3530_, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3540_, lean_object* v_x_3541_){
_start:
{
if (lean_obj_tag(v_x_3541_) == 0)
{
uint8_t v___x_3542_; 
v___x_3542_ = 0;
return v___x_3542_;
}
else
{
lean_object* v_head_3543_; lean_object* v_tail_3544_; uint8_t v___x_3545_; 
v_head_3543_ = lean_ctor_get(v_x_3541_, 0);
v_tail_3544_ = lean_ctor_get(v_x_3541_, 1);
v___x_3545_ = lean_expr_eqv(v_a_3540_, v_head_3543_);
if (v___x_3545_ == 0)
{
v_x_3541_ = v_tail_3544_;
goto _start;
}
else
{
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3547_, lean_object* v_x_3548_){
_start:
{
uint8_t v_res_3549_; lean_object* v_r_3550_; 
v_res_3549_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3547_, v_x_3548_);
lean_dec(v_x_3548_);
lean_dec_ref(v_a_3547_);
v_r_3550_ = lean_box(v_res_3549_);
return v_r_3550_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3551_, lean_object* v_x_3552_){
_start:
{
uint8_t v___x_3553_; 
v___x_3553_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3552_, v_ys_3551_);
if (v___x_3553_ == 0)
{
uint8_t v___x_3554_; 
v___x_3554_ = 1;
return v___x_3554_;
}
else
{
uint8_t v___x_3555_; 
v___x_3555_ = 0;
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3556_, lean_object* v_x_3557_){
_start:
{
uint8_t v_res_3558_; lean_object* v_r_3559_; 
v_res_3558_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3556_, v_x_3557_);
lean_dec_ref(v_x_3557_);
lean_dec(v_ys_3556_);
v_r_3559_ = lean_box(v_res_3558_);
return v_r_3559_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3560_, lean_object* v_ys_3561_){
_start:
{
lean_object* v___f_3562_; lean_object* v___x_3563_; 
v___f_3562_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3562_, 0, v_ys_3561_);
v___x_3563_ = l_List_filter___redArg(v___f_3562_, v_xs_3560_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3564_, lean_object* v_x_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
if (lean_obj_tag(v_x_3564_) == 0)
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = l_List_reverse___redArg(v_x_3565_);
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
return v___x_3574_;
}
else
{
lean_object* v_head_3575_; lean_object* v_tail_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3594_; 
v_head_3575_ = lean_ctor_get(v_x_3564_, 0);
v_tail_3576_ = lean_ctor_get(v_x_3564_, 1);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_x_3564_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3578_ = v_x_3564_;
v_isShared_3579_ = v_isSharedCheck_3594_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_tail_3576_);
lean_inc(v_head_3575_);
lean_dec(v_x_3564_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3594_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; 
v___x_3580_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3575_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v_x_3565_);
lean_ctor_set(v___x_3578_, 0, v_a_3581_);
v___x_3583_ = v___x_3578_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3581_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_x_3565_);
v___x_3583_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
v_x_3564_ = v_tail_3576_;
v_x_3565_ = v___x_3583_;
goto _start;
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_del_object(v___x_3578_);
lean_dec(v_tail_3576_);
lean_dec(v_x_3565_);
v_a_3586_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3580_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3580_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3595_, v_x_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3605_, uint8_t v_noDefaults_3606_, uint8_t v_star_3607_, lean_object* v_cfg_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
if (v_noDefaults_3606_ == 0)
{
goto v___jp_3616_;
}
else
{
if (v_star_3607_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec(v_remove_3605_);
v___x_3635_ = lean_box(0);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
else
{
goto v___jp_3616_;
}
}
v___jp_3616_:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = lean_box(0);
v___x_3620_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3605_, v___x_3619_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_toApplyRulesConfig_3621_; lean_object* v_a_3622_; uint8_t v_symm_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_toApplyRulesConfig_3621_ = lean_ctor_get(v_cfg_3608_, 0);
v_a_3622_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3620_, 1);
v_symm_3623_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3621_, sizeof(void*)*2 + 1);
v___x_3624_ = lean_array_to_list(v_a_3618_);
v___x_3625_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3624_, v_a_3622_);
v___x_3626_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3623_, v___x_3625_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3626_;
}
else
{
lean_dec(v_a_3618_);
return v___x_3620_;
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v_remove_3605_);
v_a_3627_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3617_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3617_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3637_, lean_object* v_noDefaults_3638_, lean_object* v_star_3639_, lean_object* v_cfg_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
uint8_t v_noDefaults_boxed_3648_; uint8_t v_star_boxed_3649_; lean_object* v_res_3650_; 
v_noDefaults_boxed_3648_ = lean_unbox(v_noDefaults_3638_);
v_star_boxed_3649_ = lean_unbox(v_star_3639_);
v_res_3650_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3637_, v_noDefaults_boxed_3648_, v_star_boxed_3649_, v_cfg_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v_cfg_3640_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3651_, size_t v_i_3652_, size_t v_stop_3653_, lean_object* v_b_3654_){
_start:
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_usize_dec_eq(v_i_3652_, v_stop_3653_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; lean_object* v___x_3657_; size_t v___x_3658_; size_t v___x_3659_; 
v___x_3656_ = lean_array_uget_borrowed(v_as_3651_, v_i_3652_);
v___x_3657_ = l_Array_append___redArg(v_b_3654_, v___x_3656_);
v___x_3658_ = ((size_t)1ULL);
v___x_3659_ = lean_usize_add(v_i_3652_, v___x_3658_);
v_i_3652_ = v___x_3659_;
v_b_3654_ = v___x_3657_;
goto _start;
}
else
{
return v_b_3654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3661_, lean_object* v_i_3662_, lean_object* v_stop_3663_, lean_object* v_b_3664_){
_start:
{
size_t v_i_boxed_3665_; size_t v_stop_boxed_3666_; lean_object* v_res_3667_; 
v_i_boxed_3665_ = lean_unbox_usize(v_i_3662_);
lean_dec(v_i_3662_);
v_stop_boxed_3666_ = lean_unbox_usize(v_stop_3663_);
lean_dec(v_stop_3663_);
v_res_3667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3661_, v_i_boxed_3665_, v_stop_boxed_3666_, v_b_3664_);
lean_dec_ref(v_as_3661_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
if (lean_obj_tag(v_a_3668_) == 0)
{
lean_object* v___x_3670_; 
v___x_3670_ = l_List_reverse___redArg(v_a_3669_);
return v___x_3670_;
}
else
{
lean_object* v_head_3671_; lean_object* v_tail_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3681_; 
v_head_3671_ = lean_ctor_get(v_a_3668_, 0);
v_tail_3672_ = lean_ctor_get(v_a_3668_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_a_3668_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3674_ = v_a_3668_;
v_isShared_3675_ = v_isSharedCheck_3681_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_tail_3672_);
lean_inc(v_head_3671_);
lean_dec(v_a_3668_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3681_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3676_, 0, v_head_3671_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 1, v_a_3669_);
lean_ctor_set(v___x_3674_, 0, v___x_3676_);
v___x_3678_ = v___x_3674_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_a_3669_);
v___x_3678_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
v_a_3668_ = v_tail_3672_;
v_a_3669_ = v___x_3678_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3682_, size_t v_i_3683_, lean_object* v_bs_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
uint8_t v___x_3688_; 
v___x_3688_ = lean_usize_dec_lt(v_i_3683_, v_sz_3682_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_bs_3684_);
return v___x_3689_;
}
else
{
lean_object* v_v_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_v_3690_ = lean_array_uget_borrowed(v_bs_3684_, v_i_3683_);
v___x_3691_ = l_Lean_Syntax_getId(v_v_3690_);
v___x_3692_ = l_Lean_labelled(v___x_3691_, v___y_3685_, v___y_3686_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v_bs_x27_3695_; size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v___x_3694_ = lean_unsigned_to_nat(0u);
v_bs_x27_3695_ = lean_array_uset(v_bs_3684_, v_i_3683_, v___x_3694_);
v___x_3696_ = ((size_t)1ULL);
v___x_3697_ = lean_usize_add(v_i_3683_, v___x_3696_);
v___x_3698_ = lean_array_uset(v_bs_x27_3695_, v_i_3683_, v_a_3693_);
v_i_3683_ = v___x_3697_;
v_bs_3684_ = v___x_3698_;
goto _start;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v_bs_3684_);
v_a_3700_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3692_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3692_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3708_, lean_object* v_i_3709_, lean_object* v_bs_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3708_);
lean_dec(v_sz_3708_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3709_);
lean_dec(v_i_3709_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3714_, v_i_boxed_3715_, v_bs_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3717_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
if (lean_obj_tag(v_a_3735_) == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = l_List_reverse___redArg(v_a_3736_);
return v___x_3737_;
}
else
{
lean_object* v_head_3738_; lean_object* v_tail_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3748_; 
v_head_3738_ = lean_ctor_get(v_a_3735_, 0);
v_tail_3739_ = lean_ctor_get(v_a_3735_, 1);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3735_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3741_ = v_a_3735_;
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_tail_3739_);
lean_inc(v_head_3738_);
lean_dec(v_a_3735_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___f_3743_; lean_object* v___x_3745_; 
v___f_3743_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3743_, 0, v_head_3738_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v_a_3736_);
lean_ctor_set(v___x_3741_, 0, v___f_3743_);
v___x_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___f_3743_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_a_3736_);
v___x_3745_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
v_a_3735_ = v_tail_3739_;
v_a_3736_ = v___x_3745_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3751_ = l_Lean_stringToMessageData(v___x_3750_);
return v___x_3751_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3754_ = l_String_toRawSubstring_x27(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3759_ = l_String_toRawSubstring_x27(v___x_3758_);
return v___x_3759_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3764_ = l_String_toRawSubstring_x27(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3769_ = l_String_toRawSubstring_x27(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3800_ = l_Lean_stringToMessageData(v___x_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3801_, uint8_t v_star_3802_, lean_object* v_add_3803_, lean_object* v_remove_3804_, lean_object* v_use_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___f_3836_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; 
v___x_3834_ = lean_box(v_noDefaults_3801_);
v___x_3835_ = lean_box(v_star_3802_);
lean_inc(v_remove_3804_);
v___f_3836_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3836_, 0, v_remove_3804_);
lean_closure_set(v___f_3836_, 1, v___x_3834_);
lean_closure_set(v___f_3836_, 2, v___x_3835_);
if (v_star_3802_ == 0)
{
v___y_3853_ = v_a_3806_;
v___y_3854_ = v_a_3807_;
v___y_3855_ = v_a_3808_;
v___y_3856_ = v_a_3809_;
goto v___jp_3852_;
}
else
{
if (v_noDefaults_3801_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref(v___f_3836_);
lean_dec_ref(v_use_3805_);
lean_dec(v_remove_3804_);
lean_dec(v_add_3803_);
v___x_3912_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3913_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3912_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
else
{
v___y_3853_ = v_a_3806_;
v___y_3854_ = v_a_3807_;
v___y_3855_ = v_a_3808_;
v___y_3856_ = v_a_3809_;
goto v___jp_3852_;
}
}
v___jp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___y_3812_);
lean_ctor_set(v___x_3814_, 1, v___y_3813_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
v___jp_3816_:
{
uint8_t v___x_3823_; 
v___x_3823_ = l_List_isEmpty___redArg(v_remove_3804_);
lean_dec(v_remove_3804_);
if (v___x_3823_ == 0)
{
if (v_noDefaults_3801_ == 0)
{
v___y_3812_ = v___y_3822_;
v___y_3813_ = v___y_3821_;
goto v___jp_3811_;
}
else
{
if (v_star_3802_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
v___x_3824_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3825_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3824_, v___y_3819_, v___y_3820_, v___y_3817_, v___y_3818_);
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
else
{
v___y_3812_ = v___y_3822_;
v___y_3813_ = v___y_3821_;
goto v___jp_3811_;
}
}
}
else
{
v___y_3812_ = v___y_3822_;
v___y_3813_ = v___y_3821_;
goto v___jp_3811_;
}
}
v___jp_3837_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_array_to_list(v___y_3844_);
lean_inc(v___y_3838_);
v___x_3846_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3845_, v___y_3838_);
if (v_noDefaults_3801_ == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3803_, v___y_3838_);
v___x_3848_ = l_List_appendTR___redArg(v___x_3847_, v___x_3846_);
v___x_3849_ = l_List_appendTR___redArg(v___x_3848_, v___y_3839_);
v___y_3817_ = v___y_3840_;
v___y_3818_ = v___y_3842_;
v___y_3819_ = v___y_3841_;
v___y_3820_ = v___y_3843_;
v___y_3821_ = v___f_3836_;
v___y_3822_ = v___x_3849_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec(v___y_3839_);
v___x_3850_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3803_, v___y_3838_);
v___x_3851_ = l_List_appendTR___redArg(v___x_3850_, v___x_3846_);
v___y_3817_ = v___y_3840_;
v___y_3818_ = v___y_3842_;
v___y_3819_ = v___y_3841_;
v___y_3820_ = v___y_3843_;
v___y_3821_ = v___f_3836_;
v___y_3822_ = v___x_3851_;
goto v___jp_3816_;
}
}
v___jp_3852_:
{
lean_object* v_ref_3857_; lean_object* v_quotContext_3858_; lean_object* v_currMacroScope_3859_; lean_object* v___x_3860_; lean_object* v_a_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_a_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; size_t v_sz_3873_; size_t v___x_3874_; lean_object* v___x_3875_; 
v_ref_3857_ = lean_ctor_get(v___y_3855_, 5);
v_quotContext_3858_ = lean_ctor_get(v___y_3855_, 10);
v_currMacroScope_3859_ = lean_ctor_get(v___y_3855_, 11);
v___x_3860_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
v___x_3862_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3863_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref(v___x_3863_);
v___x_3865_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3859_, 2);
lean_inc_n(v_quotContext_3858_, 2);
v___x_3866_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3865_, v_currMacroScope_3859_);
v___x_3867_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_3868_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3868_);
v___x_3870_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3871_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3870_, v_currMacroScope_3859_);
v___x_3872_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_3873_ = lean_array_size(v_use_3805_);
v___x_3874_ = ((size_t)0ULL);
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3873_, v___x_3874_, v_use_3805_, v___y_3855_, v___y_3856_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
v___x_3877_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3859_, 2);
lean_inc_n(v_quotContext_3858_, 2);
v___x_3878_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3877_, v_currMacroScope_3859_);
v___x_3879_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_3880_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_3881_ = l_Lean_addMacroScope(v_quotContext_3858_, v___x_3880_, v_currMacroScope_3859_);
v___x_3882_ = 0;
v___x_3883_ = l_Lean_SourceInfo_fromRef(v_ref_3857_, v___x_3882_);
v___x_3884_ = lean_box(0);
v___x_3885_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_3886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3883_);
lean_ctor_set(v___x_3886_, 1, v___x_3862_);
lean_ctor_set(v___x_3886_, 2, v___x_3866_);
lean_ctor_set(v___x_3886_, 3, v___x_3885_);
v___x_3887_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3888_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3888_, 0, v_a_3861_);
lean_ctor_set(v___x_3888_, 1, v___x_3867_);
lean_ctor_set(v___x_3888_, 2, v___x_3871_);
lean_ctor_set(v___x_3888_, 3, v___x_3887_);
v___x_3889_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3890_, 0, v_a_3864_);
lean_ctor_set(v___x_3890_, 1, v___x_3872_);
lean_ctor_set(v___x_3890_, 2, v___x_3878_);
lean_ctor_set(v___x_3890_, 3, v___x_3889_);
v___x_3891_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3892_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3892_, 0, v_a_3869_);
lean_ctor_set(v___x_3892_, 1, v___x_3879_);
lean_ctor_set(v___x_3892_, 2, v___x_3881_);
lean_ctor_set(v___x_3892_, 3, v___x_3891_);
v___x_3893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3884_);
v___x_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3890_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3888_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3886_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_3896_, v___x_3884_);
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3900_ = lean_array_get_size(v_a_3876_);
v___x_3901_ = lean_nat_dec_lt(v___x_3898_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_dec(v_a_3876_);
v___y_3838_ = v___x_3884_;
v___y_3839_ = v___x_3897_;
v___y_3840_ = v___y_3855_;
v___y_3841_ = v___y_3853_;
v___y_3842_ = v___y_3856_;
v___y_3843_ = v___y_3854_;
v___y_3844_ = v___x_3899_;
goto v___jp_3837_;
}
else
{
size_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_usize_of_nat(v___x_3900_);
v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3876_, v___x_3874_, v___x_3902_, v___x_3899_);
lean_dec(v_a_3876_);
v___y_3838_ = v___x_3884_;
v___y_3839_ = v___x_3897_;
v___y_3840_ = v___y_3855_;
v___y_3841_ = v___y_3853_;
v___y_3842_ = v___y_3856_;
v___y_3843_ = v___y_3854_;
v___y_3844_ = v___x_3903_;
goto v___jp_3837_;
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec(v___x_3871_);
lean_dec(v_a_3869_);
lean_dec(v___x_3866_);
lean_dec(v_a_3864_);
lean_dec(v_a_3861_);
lean_dec_ref(v___f_3836_);
lean_dec(v_remove_3804_);
lean_dec(v_add_3803_);
v_a_3904_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3875_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3875_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3922_, lean_object* v_star_3923_, lean_object* v_add_3924_, lean_object* v_remove_3925_, lean_object* v_use_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
uint8_t v_noDefaults_boxed_3932_; uint8_t v_star_boxed_3933_; lean_object* v_res_3934_; 
v_noDefaults_boxed_3932_ = lean_unbox(v_noDefaults_3922_);
v_star_boxed_3933_ = lean_unbox(v_star_3923_);
v_res_3934_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3932_, v_star_boxed_3933_, v_add_3924_, v_remove_3925_, v_use_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_3935_, size_t v_i_3936_, lean_object* v_bs_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3935_, v_i_3936_, v_bs_3937_, v___y_3940_, v___y_3941_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_3944_, lean_object* v_i_3945_, lean_object* v_bs_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
size_t v_sz_boxed_3952_; size_t v_i_boxed_3953_; lean_object* v_res_3954_; 
v_sz_boxed_3952_ = lean_unbox_usize(v_sz_3944_);
lean_dec(v_sz_3944_);
v_i_boxed_3953_ = lean_unbox_usize(v_i_3945_);
lean_dec(v_i_3945_);
v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_3952_, v_i_boxed_3953_, v_bs_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
return v_res_3954_;
}
}
lean_object* runtime_initialize_Init_Data_Sum(uint8_t builtin);
lean_object* runtime_initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Sum(uint8_t builtin);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_SolveByElim(builtin);
}
#ifdef __cplusplus
}
#endif

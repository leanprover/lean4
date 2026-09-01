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
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_13917__boxed_297_; uint8_t v___x_13918__boxed_298_; lean_object* v_res_299_; 
v___x_13917__boxed_297_ = lean_unbox(v___x_288_);
v___x_13918__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13917__boxed_297_, v___x_13918__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
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
v_options_311_ = lean_ctor_get(v___y_303_, 1);
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
lean_object* v_toCold_349_; lean_object* v_options_350_; lean_object* v_currRecDepth_351_; lean_object* v_maxRecDepth_352_; lean_object* v_ref_353_; lean_object* v_currNamespace_354_; lean_object* v_openDecls_355_; lean_object* v_initHeartbeats_356_; lean_object* v_maxHeartbeats_357_; lean_object* v_currMacroScope_358_; uint8_t v_diag_359_; uint8_t v_suppressElabErrors_360_; lean_object* v___x_361_; lean_object* v_traceState_362_; lean_object* v_traces_363_; lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v___x_366_; size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v_msg_370_; lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_409_; 
v_toCold_349_ = lean_ctor_get(v___y_346_, 0);
v_options_350_ = lean_ctor_get(v___y_346_, 1);
v_currRecDepth_351_ = lean_ctor_get(v___y_346_, 2);
v_maxRecDepth_352_ = lean_ctor_get(v___y_346_, 3);
v_ref_353_ = lean_ctor_get(v___y_346_, 4);
v_currNamespace_354_ = lean_ctor_get(v___y_346_, 5);
v_openDecls_355_ = lean_ctor_get(v___y_346_, 6);
v_initHeartbeats_356_ = lean_ctor_get(v___y_346_, 7);
v_maxHeartbeats_357_ = lean_ctor_get(v___y_346_, 8);
v_currMacroScope_358_ = lean_ctor_get(v___y_346_, 9);
v_diag_359_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*10);
v_suppressElabErrors_360_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*10 + 1);
v___x_361_ = lean_st_ref_get(v___y_347_);
v_traceState_362_ = lean_ctor_get(v___x_361_, 4);
lean_inc_ref(v_traceState_362_);
lean_dec(v___x_361_);
v_traces_363_ = lean_ctor_get(v_traceState_362_, 0);
lean_inc_ref(v_traces_363_);
lean_dec_ref(v_traceState_362_);
v_ref_364_ = l_Lean_replaceRef(v_ref_342_, v_ref_353_);
lean_inc(v_currMacroScope_358_);
lean_inc(v_maxHeartbeats_357_);
lean_inc(v_initHeartbeats_356_);
lean_inc(v_openDecls_355_);
lean_inc(v_currNamespace_354_);
lean_inc(v_maxRecDepth_352_);
lean_inc(v_currRecDepth_351_);
lean_inc_ref(v_options_350_);
lean_inc_ref(v_toCold_349_);
v___x_365_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_365_, 0, v_toCold_349_);
lean_ctor_set(v___x_365_, 1, v_options_350_);
lean_ctor_set(v___x_365_, 2, v_currRecDepth_351_);
lean_ctor_set(v___x_365_, 3, v_maxRecDepth_352_);
lean_ctor_set(v___x_365_, 4, v_ref_364_);
lean_ctor_set(v___x_365_, 5, v_currNamespace_354_);
lean_ctor_set(v___x_365_, 6, v_openDecls_355_);
lean_ctor_set(v___x_365_, 7, v_initHeartbeats_356_);
lean_ctor_set(v___x_365_, 8, v_maxHeartbeats_357_);
lean_ctor_set(v___x_365_, 9, v_currMacroScope_358_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*10, v_diag_359_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*10 + 1, v_suppressElabErrors_360_);
v___x_366_ = l_Lean_PersistentArray_toArray___redArg(v_traces_363_);
lean_dec_ref(v_traces_363_);
v_sz_367_ = lean_array_size(v___x_366_);
v___x_368_ = ((size_t)0ULL);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_367_, v___x_368_, v___x_366_);
v_msg_370_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_370_, 0, v_data_341_);
lean_ctor_set(v_msg_370_, 1, v_msg_343_);
lean_ctor_set(v_msg_370_, 2, v___x_369_);
v___x_371_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_370_, v___y_344_, v___y_345_, v___x_365_, v___y_347_);
lean_dec_ref_known(v___x_365_, 10);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_409_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_409_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_409_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v_traceState_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_cache_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_408_; 
v___x_376_ = lean_st_ref_take(v___y_347_);
v_traceState_377_ = lean_ctor_get(v___x_376_, 4);
v_env_378_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_376_, 1);
v_ngen_380_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_376_, 3);
v_cache_382_ = lean_ctor_get(v___x_376_, 5);
v_messages_383_ = lean_ctor_get(v___x_376_, 6);
v_infoState_384_ = lean_ctor_get(v___x_376_, 7);
v_snapshotTasks_385_ = lean_ctor_get(v___x_376_, 8);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_408_ == 0)
{
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snapshotTasks_385_);
lean_inc(v_infoState_384_);
lean_inc(v_messages_383_);
lean_inc(v_cache_382_);
lean_inc(v_traceState_377_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint64_t v_tid_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_406_; 
v_tid_389_ = lean_ctor_get_uint64(v_traceState_377_, sizeof(void*)*1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_traceState_377_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_traceState_377_, 0);
lean_dec(v_unused_407_);
v___x_391_ = v_traceState_377_;
v_isShared_392_ = v_isSharedCheck_406_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_traceState_377_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_406_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_ref_342_);
lean_ctor_set(v___x_393_, 1, v_a_372_);
v___x_394_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_340_, v___x_393_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_394_);
lean_ctor_set_uint64(v_reuseFailAlloc_405_, sizeof(void*)*1, v_tid_389_);
v___x_396_ = v_reuseFailAlloc_405_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v___x_396_);
v___x_398_ = v___x_387_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_env_378_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 5, v_cache_382_);
lean_ctor_set(v_reuseFailAlloc_404_, 6, v_messages_383_);
lean_ctor_set(v_reuseFailAlloc_404_, 7, v_infoState_384_);
lean_ctor_set(v_reuseFailAlloc_404_, 8, v_snapshotTasks_385_);
v___x_398_ = v_reuseFailAlloc_404_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_st_ref_put(v___y_347_, v___x_398_);
v___x_400_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_400_);
v___x_402_ = v___x_374_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_410_, lean_object* v_data_411_, lean_object* v_ref_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_410_, v_data_411_, v_ref_412_, v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_420_){
_start:
{
if (lean_obj_tag(v_e_420_) == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 2;
return v___x_421_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_423_);
lean_dec_ref(v_e_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_426_, lean_object* v_opt_427_){
_start:
{
lean_object* v_name_428_; lean_object* v_defValue_429_; lean_object* v_map_430_; lean_object* v___x_431_; 
v_name_428_ = lean_ctor_get(v_opt_427_, 0);
v_defValue_429_ = lean_ctor_get(v_opt_427_, 1);
v_map_430_ = lean_ctor_get(v_opts_426_, 0);
v___x_431_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_430_, v_name_428_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_inc(v_defValue_429_);
return v_defValue_429_;
}
else
{
lean_object* v_val_432_; 
v_val_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v___x_431_, 1);
if (lean_obj_tag(v_val_432_) == 3)
{
lean_object* v_v_433_; 
v_v_433_ = lean_ctor_get(v_val_432_, 0);
lean_inc(v_v_433_);
lean_dec_ref_known(v_val_432_, 1);
return v_v_433_;
}
else
{
lean_dec(v_val_432_);
lean_inc(v_defValue_429_);
return v_defValue_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_434_, lean_object* v_opt_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_434_, v_opt_435_);
lean_dec_ref(v_opt_435_);
lean_dec_ref(v_opts_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_a_439_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 1);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_437_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_x_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 0);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_455_);
return v_res_457_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_458_; double v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_float_of_nat(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_463_; double v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(1000u);
v___x_464_ = lean_float_of_nat(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_465_, uint8_t v_collapsed_466_, lean_object* v_tag_467_, lean_object* v_opts_468_, uint8_t v_clsEnabled_469_, lean_object* v_oldTraces_470_, lean_object* v_msg_471_, lean_object* v_resStartStop_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_data_483_; lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___y_499_; lean_object* v_a_500_; uint8_t v___y_515_; double v___y_546_; 
v_fst_478_ = lean_ctor_get(v_resStartStop_472_, 0);
lean_inc(v_fst_478_);
v_snd_479_ = lean_ctor_get(v_resStartStop_472_, 1);
lean_inc(v_snd_479_);
lean_dec_ref(v_resStartStop_472_);
v_fst_494_ = lean_ctor_get(v_snd_479_, 0);
lean_inc(v_fst_494_);
v_snd_495_ = lean_ctor_get(v_snd_479_, 1);
lean_inc(v_snd_495_);
lean_dec(v_snd_479_);
v___x_496_ = l_Lean_trace_profiler;
v___x_497_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_468_, v___x_496_);
if (v___x_497_ == 0)
{
v___y_515_ = v___x_497_;
goto v___jp_514_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = l_Lean_trace_profiler_useHeartbeats;
v___x_552_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_468_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; double v___x_555_; double v___x_556_; double v___x_557_; 
v___x_553_ = l_Lean_trace_profiler_threshold;
v___x_554_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_468_, v___x_553_);
v___x_555_ = lean_float_of_nat(v___x_554_);
v___x_556_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_557_ = lean_float_div(v___x_555_, v___x_556_);
v___y_546_ = v___x_557_;
goto v___jp_545_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; double v___x_560_; 
v___x_558_ = l_Lean_trace_profiler_threshold;
v___x_559_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_468_, v___x_558_);
v___x_560_ = lean_float_of_nat(v___x_559_);
v___y_546_ = v___x_560_;
goto v___jp_545_;
}
}
v___jp_480_:
{
lean_object* v___x_484_; 
lean_inc(v___y_481_);
v___x_484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_470_, v_data_483_, v___y_481_, v___y_482_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; 
lean_dec_ref_known(v___x_484_, 1);
v___x_485_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_478_);
return v___x_485_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_fst_478_);
v_a_486_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
v___jp_498_:
{
uint8_t v_result_501_; lean_object* v___x_502_; lean_object* v___x_503_; double v___x_504_; lean_object* v_data_505_; 
v_result_501_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_478_);
v___x_502_ = lean_box(v_result_501_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_467_);
lean_inc_ref(v___x_503_);
lean_inc(v_cls_465_);
v_data_505_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_505_, 0, v_cls_465_);
lean_ctor_set(v_data_505_, 1, v___x_503_);
lean_ctor_set(v_data_505_, 2, v_tag_467_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3, v___x_504_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3 + 8, v___x_504_);
lean_ctor_set_uint8(v_data_505_, sizeof(void*)*3 + 16, v_collapsed_466_);
if (v___x_497_ == 0)
{
lean_dec_ref_known(v___x_503_, 1);
lean_dec(v_snd_495_);
lean_dec(v_fst_494_);
lean_dec_ref(v_tag_467_);
lean_dec(v_cls_465_);
v___y_481_ = v___y_499_;
v___y_482_ = v_a_500_;
v_data_483_ = v_data_505_;
goto v___jp_480_;
}
else
{
lean_object* v_data_506_; double v___x_507_; double v___x_508_; 
lean_dec_ref_known(v_data_505_, 3);
v_data_506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_506_, 0, v_cls_465_);
lean_ctor_set(v_data_506_, 1, v___x_503_);
lean_ctor_set(v_data_506_, 2, v_tag_467_);
v___x_507_ = lean_unbox_float(v_fst_494_);
lean_dec(v_fst_494_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3, v___x_507_);
v___x_508_ = lean_unbox_float(v_snd_495_);
lean_dec(v_snd_495_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3 + 8, v___x_508_);
lean_ctor_set_uint8(v_data_506_, sizeof(void*)*3 + 16, v_collapsed_466_);
v___y_481_ = v___y_499_;
v___y_482_ = v_a_500_;
v_data_483_ = v_data_506_;
goto v___jp_480_;
}
}
v___jp_509_:
{
lean_object* v_ref_510_; lean_object* v___x_511_; 
v_ref_510_ = lean_ctor_get(v___y_475_, 4);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
lean_inc(v_fst_478_);
v___x_511_ = lean_apply_6(v_msg_471_, v_fst_478_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, lean_box(0));
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___y_499_ = v_ref_510_;
v_a_500_ = v_a_512_;
goto v___jp_498_;
}
else
{
lean_object* v___x_513_; 
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_499_ = v_ref_510_;
v_a_500_ = v___x_513_;
goto v___jp_498_;
}
}
v___jp_514_:
{
if (v_clsEnabled_469_ == 0)
{
if (v___y_515_ == 0)
{
lean_object* v___x_516_; lean_object* v_traceState_517_; lean_object* v_env_518_; lean_object* v_nextMacroScope_519_; lean_object* v_ngen_520_; lean_object* v_auxDeclNGen_521_; lean_object* v_cache_522_; lean_object* v_messages_523_; lean_object* v_infoState_524_; lean_object* v_snapshotTasks_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_snd_495_);
lean_dec(v_fst_494_);
lean_dec_ref(v_msg_471_);
lean_dec_ref(v_tag_467_);
lean_dec(v_cls_465_);
v___x_516_ = lean_st_ref_take(v___y_476_);
v_traceState_517_ = lean_ctor_get(v___x_516_, 4);
v_env_518_ = lean_ctor_get(v___x_516_, 0);
v_nextMacroScope_519_ = lean_ctor_get(v___x_516_, 1);
v_ngen_520_ = lean_ctor_get(v___x_516_, 2);
v_auxDeclNGen_521_ = lean_ctor_get(v___x_516_, 3);
v_cache_522_ = lean_ctor_get(v___x_516_, 5);
v_messages_523_ = lean_ctor_get(v___x_516_, 6);
v_infoState_524_ = lean_ctor_get(v___x_516_, 7);
v_snapshotTasks_525_ = lean_ctor_get(v___x_516_, 8);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_544_ == 0)
{
v___x_527_ = v___x_516_;
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snapshotTasks_525_);
lean_inc(v_infoState_524_);
lean_inc(v_messages_523_);
lean_inc(v_cache_522_);
lean_inc(v_traceState_517_);
lean_inc(v_auxDeclNGen_521_);
lean_inc(v_ngen_520_);
lean_inc(v_nextMacroScope_519_);
lean_inc(v_env_518_);
lean_dec(v___x_516_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint64_t v_tid_529_; lean_object* v_traces_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_543_; 
v_tid_529_ = lean_ctor_get_uint64(v_traceState_517_, sizeof(void*)*1);
v_traces_530_ = lean_ctor_get(v_traceState_517_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_traceState_517_);
if (v_isSharedCheck_543_ == 0)
{
v___x_532_ = v_traceState_517_;
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_traces_530_);
lean_dec(v_traceState_517_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_470_, v_traces_530_);
lean_dec_ref(v_traces_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_534_);
lean_ctor_set_uint64(v_reuseFailAlloc_542_, sizeof(void*)*1, v_tid_529_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 4, v___x_536_);
v___x_538_ = v___x_527_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_env_518_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_ngen_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_auxDeclNGen_521_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v_cache_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v_messages_523_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v_infoState_524_);
lean_ctor_set(v_reuseFailAlloc_541_, 8, v_snapshotTasks_525_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_put(v___y_476_, v___x_538_);
v___x_540_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_478_);
return v___x_540_;
}
}
}
}
}
else
{
goto v___jp_509_;
}
}
else
{
goto v___jp_509_;
}
}
v___jp_545_:
{
double v___x_547_; double v___x_548_; double v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unbox_float(v_snd_495_);
v___x_548_ = lean_unbox_float(v_fst_494_);
v___x_549_ = lean_float_sub(v___x_547_, v___x_548_);
v___x_550_ = lean_float_decLt(v___y_546_, v___x_549_);
v___y_515_ = v___x_550_;
goto v___jp_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_561_, lean_object* v_collapsed_562_, lean_object* v_tag_563_, lean_object* v_opts_564_, lean_object* v_clsEnabled_565_, lean_object* v_oldTraces_566_, lean_object* v_msg_567_, lean_object* v_resStartStop_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v_collapsed_boxed_574_; uint8_t v_clsEnabled_boxed_575_; lean_object* v_res_576_; 
v_collapsed_boxed_574_ = lean_unbox(v_collapsed_562_);
v_clsEnabled_boxed_575_ = lean_unbox(v_clsEnabled_565_);
v_res_576_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_561_, v_collapsed_boxed_574_, v_tag_563_, v_opts_564_, v_clsEnabled_boxed_575_, v_oldTraces_566_, v_msg_567_, v_resStartStop_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v_opts_564_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v_x_579_);
return v___x_585_;
}
else
{
lean_object* v_head_586_; lean_object* v_tail_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_610_; 
v_head_586_ = lean_ctor_get(v_x_578_, 0);
v_tail_587_ = lean_ctor_get(v_x_578_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_610_ == 0)
{
v___x_589_ = v_x_578_;
v_isShared_590_ = v_isSharedCheck_610_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_tail_587_);
lean_inc(v_head_586_);
lean_dec(v_x_578_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_610_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; 
lean_inc(v_head_586_);
v___x_591_ = l_Lean_MVarId_inferInstance(v_head_586_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_dec_ref_known(v___x_591_, 1);
lean_del_object(v___x_589_);
lean_dec(v_head_586_);
v_x_578_ = v_tail_587_;
goto _start;
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_609_; 
v_a_593_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_609_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_609_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_609_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___y_598_; uint8_t v___x_607_; 
v___x_607_ = l_Lean_Exception_isInterrupt(v_a_593_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
lean_inc(v_a_593_);
v___x_608_ = l_Lean_Exception_isRuntime(v_a_593_);
v___y_598_ = v___x_608_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_607_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_del_object(v___x_595_);
lean_dec(v_a_593_);
if (v___x_577_ == 0)
{
lean_del_object(v___x_589_);
lean_dec(v_head_586_);
v_x_578_ = v_tail_587_;
goto _start;
}
else
{
lean_object* v___x_601_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_x_579_);
v___x_601_ = v___x_589_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_head_586_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_x_579_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
v_x_578_ = v_tail_587_;
v_x_579_ = v___x_601_;
goto _start;
}
}
}
else
{
lean_object* v___x_605_; 
lean_del_object(v___x_589_);
lean_dec(v_tail_587_);
lean_dec(v_head_586_);
lean_dec(v_x_579_);
if (v_isShared_596_ == 0)
{
v___x_605_ = v___x_595_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_593_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
uint8_t v___x_14342__boxed_619_; lean_object* v_res_620_; 
v___x_14342__boxed_619_ = lean_unbox(v___x_611_);
v_res_620_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14342__boxed_619_, v_x_612_, v_x_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_x_623_);
return v___x_629_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_654_; 
v_head_630_ = lean_ctor_get(v_x_622_, 0);
v_tail_631_ = lean_ctor_get(v_x_622_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_654_ == 0)
{
v___x_633_ = v_x_622_;
v_isShared_634_ = v_isSharedCheck_654_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_tail_631_);
lean_inc(v_head_630_);
lean_dec(v_x_622_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_654_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_640_; 
lean_inc(v_head_630_);
v___x_640_ = l_Lean_MVarId_inferInstance(v_head_630_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref_known(v___x_640_, 1);
if (v___x_621_ == 0)
{
lean_del_object(v___x_633_);
lean_dec(v_head_630_);
v_x_622_ = v_tail_631_;
goto _start;
}
else
{
goto v___jp_635_;
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_a_642_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v___x_640_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___y_647_; uint8_t v___x_651_; 
v___x_651_ = l_Lean_Exception_isInterrupt(v_a_642_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; 
lean_inc(v_a_642_);
v___x_652_ = l_Lean_Exception_isRuntime(v_a_642_);
v___y_647_ = v___x_652_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___x_651_;
goto v___jp_646_;
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
lean_del_object(v___x_644_);
lean_dec(v_a_642_);
goto v___jp_635_;
}
else
{
lean_object* v___x_649_; 
lean_del_object(v___x_633_);
lean_dec(v_tail_631_);
lean_dec(v_head_630_);
lean_dec(v_x_623_);
if (v_isShared_645_ == 0)
{
v___x_649_ = v___x_644_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_642_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
v___jp_635_:
{
lean_object* v___x_637_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_x_623_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_head_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_x_623_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v_x_622_ = v_tail_631_;
v_x_623_ = v___x_637_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_14419__boxed_663_; lean_object* v_res_664_; 
v___x_14419__boxed_663_ = lean_unbox(v___x_655_);
v_res_664_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14419__boxed_663_, v_x_656_, v_x_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_664_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_668_; double v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(1000000000u);
v___x_669_ = lean_float_of_nat(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_670_, lean_object* v_g_671_, lean_object* v_e_672_, lean_object* v_cfg_673_, lean_object* v___x_674_, lean_object* v___x_675_, uint8_t v___x_676_, lean_object* v___x_677_, lean_object* v___f_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_options_684_; lean_object* v_toCold_685_; uint8_t v_hasTrace_686_; lean_object* v___y_688_; 
v_options_684_ = lean_ctor_get(v___y_681_, 1);
v_toCold_685_ = lean_ctor_get(v___y_681_, 0);
v_hasTrace_686_ = lean_ctor_get_uint8(v_options_684_, sizeof(void*)*1);
if (v_hasTrace_686_ == 0)
{
lean_object* v___x_709_; uint8_t v_transparency_710_; uint8_t v___x_711_; 
lean_dec_ref(v___f_678_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_675_);
v___x_709_ = l_Lean_Meta_Context_config(v___y_679_);
v_transparency_710_ = lean_ctor_get_uint8(v___x_709_, 9);
lean_dec_ref(v___x_709_);
v___x_711_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_710_, v_transparency_670_);
if (v___x_711_ == 0)
{
lean_object* v_keyedConfig_712_; uint8_t v_trackZetaDelta_713_; lean_object* v_zetaDeltaSet_714_; lean_object* v_lctx_715_; lean_object* v_localInstances_716_; lean_object* v_defEqCtx_x3f_717_; lean_object* v_synthPendingDepth_718_; lean_object* v_customCanUnfoldPredicate_x3f_719_; uint8_t v_univApprox_720_; uint8_t v_inTypeClassResolution_721_; uint8_t v_cacheInferType_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_keyedConfig_712_ = lean_ctor_get(v___y_679_, 0);
v_trackZetaDelta_713_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7);
v_zetaDeltaSet_714_ = lean_ctor_get(v___y_679_, 1);
v_lctx_715_ = lean_ctor_get(v___y_679_, 2);
v_localInstances_716_ = lean_ctor_get(v___y_679_, 3);
v_defEqCtx_x3f_717_ = lean_ctor_get(v___y_679_, 4);
v_synthPendingDepth_718_ = lean_ctor_get(v___y_679_, 5);
v_customCanUnfoldPredicate_x3f_719_ = lean_ctor_get(v___y_679_, 6);
v_univApprox_720_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_721_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 2);
v_cacheInferType_722_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_712_);
v___x_723_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_670_, v_keyedConfig_712_);
lean_inc(v_customCanUnfoldPredicate_x3f_719_);
lean_inc(v_synthPendingDepth_718_);
lean_inc(v_defEqCtx_x3f_717_);
lean_inc_ref(v_localInstances_716_);
lean_inc_ref(v_lctx_715_);
lean_inc(v_zetaDeltaSet_714_);
v___x_724_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_zetaDeltaSet_714_);
lean_ctor_set(v___x_724_, 2, v_lctx_715_);
lean_ctor_set(v___x_724_, 3, v_localInstances_716_);
lean_ctor_set(v___x_724_, 4, v_defEqCtx_x3f_717_);
lean_ctor_set(v___x_724_, 5, v_synthPendingDepth_718_);
lean_ctor_set(v___x_724_, 6, v_customCanUnfoldPredicate_x3f_719_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*7, v_trackZetaDelta_713_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*7 + 1, v_univApprox_720_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*7 + 2, v_inTypeClassResolution_721_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*7 + 3, v_cacheInferType_722_);
v___x_725_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___x_724_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref_known(v___x_724_, 7);
v___y_688_ = v___x_725_;
goto v___jp_687_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v___y_688_ = v___x_726_;
goto v___jp_687_;
}
}
else
{
lean_object* v_inheritedTraceOptions_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v_a_734_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v_a_749_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_a_772_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v_a_784_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v_a_789_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; 
v_inheritedTraceOptions_727_ = lean_ctor_get(v_toCold_685_, 4);
v___x_728_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_675_);
v___x_729_ = l_Lean_Name_append(v___x_728_, v___x_675_);
v___x_730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_727_, v_options_684_, v___x_729_);
lean_dec(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___y_850_; 
v___x_847_ = l_Lean_trace_profiler;
v___x_848_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_684_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_871_; uint8_t v_transparency_872_; uint8_t v___x_873_; 
lean_dec_ref(v___f_678_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_675_);
v___x_871_ = l_Lean_Meta_Context_config(v___y_679_);
v_transparency_872_ = lean_ctor_get_uint8(v___x_871_, 9);
lean_dec_ref(v___x_871_);
v___x_873_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_872_, v_transparency_670_);
if (v___x_873_ == 0)
{
lean_object* v_keyedConfig_874_; uint8_t v_trackZetaDelta_875_; lean_object* v_zetaDeltaSet_876_; lean_object* v_lctx_877_; lean_object* v_localInstances_878_; lean_object* v_defEqCtx_x3f_879_; lean_object* v_synthPendingDepth_880_; lean_object* v_customCanUnfoldPredicate_x3f_881_; uint8_t v_univApprox_882_; uint8_t v_inTypeClassResolution_883_; uint8_t v_cacheInferType_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_keyedConfig_874_ = lean_ctor_get(v___y_679_, 0);
v_trackZetaDelta_875_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7);
v_zetaDeltaSet_876_ = lean_ctor_get(v___y_679_, 1);
v_lctx_877_ = lean_ctor_get(v___y_679_, 2);
v_localInstances_878_ = lean_ctor_get(v___y_679_, 3);
v_defEqCtx_x3f_879_ = lean_ctor_get(v___y_679_, 4);
v_synthPendingDepth_880_ = lean_ctor_get(v___y_679_, 5);
v_customCanUnfoldPredicate_x3f_881_ = lean_ctor_get(v___y_679_, 6);
v_univApprox_882_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_883_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 2);
v_cacheInferType_884_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_874_);
v___x_885_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_670_, v_keyedConfig_874_);
lean_inc(v_customCanUnfoldPredicate_x3f_881_);
lean_inc(v_synthPendingDepth_880_);
lean_inc(v_defEqCtx_x3f_879_);
lean_inc_ref(v_localInstances_878_);
lean_inc_ref(v_lctx_877_);
lean_inc(v_zetaDeltaSet_876_);
v___x_886_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v_zetaDeltaSet_876_);
lean_ctor_set(v___x_886_, 2, v_lctx_877_);
lean_ctor_set(v___x_886_, 3, v_localInstances_878_);
lean_ctor_set(v___x_886_, 4, v_defEqCtx_x3f_879_);
lean_ctor_set(v___x_886_, 5, v_synthPendingDepth_880_);
lean_ctor_set(v___x_886_, 6, v_customCanUnfoldPredicate_x3f_881_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*7, v_trackZetaDelta_875_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*7 + 1, v_univApprox_882_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*7 + 2, v_inTypeClassResolution_883_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*7 + 3, v_cacheInferType_884_);
v___x_887_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___x_886_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref_known(v___x_886_, 7);
v___y_850_ = v___x_887_;
goto v___jp_849_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v___y_850_ = v___x_888_;
goto v___jp_849_;
}
}
else
{
goto v___jp_804_;
}
v___jp_849_:
{
if (lean_obj_tag(v___y_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_a_851_ = lean_ctor_get(v___y_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___y_850_, 1);
v___x_852_ = lean_box(0);
v___x_853_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_848_, v_hasTrace_686_, v_a_851_, v___x_852_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_679_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = l_List_reverse___redArg(v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
return v___x_853_;
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v___y_679_);
v_a_863_ = lean_ctor_get(v___y_850_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___y_850_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___y_850_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___y_850_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
else
{
goto v___jp_804_;
}
v___jp_731_:
{
lean_object* v___x_735_; double v___x_736_; double v___x_737_; double v___x_738_; double v___x_739_; double v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_735_ = lean_io_mono_nanos_now();
v___x_736_ = lean_float_of_nat(v___y_732_);
v___x_737_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_738_ = lean_float_div(v___x_736_, v___x_737_);
v___x_739_ = lean_float_of_nat(v___x_735_);
v___x_740_ = lean_float_div(v___x_739_, v___x_737_);
v___x_741_ = lean_box_float(v___x_738_);
v___x_742_ = lean_box_float(v___x_740_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_a_734_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_675_, v___x_676_, v___x_677_, v_options_684_, v___x_730_, v___y_733_, v___f_678_, v___x_744_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_679_);
return v___x_745_;
}
v___jp_746_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_a_749_);
v___y_732_ = v___y_747_;
v___y_733_ = v___y_748_;
v_a_734_ = v___x_750_;
goto v___jp_731_;
}
v___jp_751_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_a_754_);
v___y_732_ = v___y_752_;
v___y_733_ = v___y_753_;
v_a_734_ = v___x_755_;
goto v___jp_731_;
}
v___jp_756_:
{
if (lean_obj_tag(v___y_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_a_761_ = lean_ctor_get(v___y_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___y_760_, 1);
v___x_762_ = lean_box(0);
v___x_763_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_758_, v_hasTrace_686_, v_a_761_, v___x_762_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_List_reverse___redArg(v_a_764_);
v___y_752_ = v___y_757_;
v___y_753_ = v___y_759_;
v_a_754_ = v___x_765_;
goto v___jp_751_;
}
else
{
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_763_, 1);
v___y_752_ = v___y_757_;
v___y_753_ = v___y_759_;
v_a_754_ = v_a_766_;
goto v___jp_751_;
}
else
{
lean_object* v_a_767_; 
v_a_767_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_763_, 1);
v___y_747_ = v___y_757_;
v___y_748_ = v___y_759_;
v_a_749_ = v_a_767_;
goto v___jp_746_;
}
}
}
else
{
lean_object* v_a_768_; 
v_a_768_ = lean_ctor_get(v___y_760_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___y_760_, 1);
v___y_747_ = v___y_757_;
v___y_748_ = v___y_759_;
v_a_749_ = v_a_768_;
goto v___jp_746_;
}
}
v___jp_769_:
{
lean_object* v___x_773_; double v___x_774_; double v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_773_ = lean_io_get_num_heartbeats();
v___x_774_ = lean_float_of_nat(v___y_770_);
v___x_775_ = lean_float_of_nat(v___x_773_);
v___x_776_ = lean_box_float(v___x_774_);
v___x_777_ = lean_box_float(v___x_775_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_a_772_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_675_, v___x_676_, v___x_677_, v_options_684_, v___x_730_, v___y_771_, v___f_678_, v___x_779_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_679_);
return v___x_780_;
}
v___jp_781_:
{
lean_object* v___x_785_; 
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v_a_784_);
v___y_770_ = v___y_782_;
v___y_771_ = v___y_783_;
v_a_772_ = v___x_785_;
goto v___jp_769_;
}
v___jp_786_:
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v_a_789_);
v___y_770_ = v___y_787_;
v___y_771_ = v___y_788_;
v_a_772_ = v___x_790_;
goto v___jp_769_;
}
v___jp_791_:
{
if (lean_obj_tag(v___y_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_796_ = lean_ctor_get(v___y_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___y_795_, 1);
v___x_797_ = lean_box(0);
v___x_798_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_792_, v_a_796_, v___x_797_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_List_reverse___redArg(v_a_799_);
v___y_787_ = v___y_793_;
v___y_788_ = v___y_794_;
v_a_789_ = v___x_800_;
goto v___jp_786_;
}
else
{
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_801_; 
v_a_801_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_798_, 1);
v___y_787_ = v___y_793_;
v___y_788_ = v___y_794_;
v_a_789_ = v_a_801_;
goto v___jp_786_;
}
else
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_798_, 1);
v___y_782_ = v___y_793_;
v___y_783_ = v___y_794_;
v_a_784_ = v_a_802_;
goto v___jp_781_;
}
}
}
else
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___y_795_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___y_795_, 1);
v___y_782_ = v___y_793_;
v___y_783_ = v___y_794_;
v_a_784_ = v_a_803_;
goto v___jp_781_;
}
}
v___jp_804_:
{
lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_805_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_682_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___x_805_);
v___x_807_ = l_Lean_trace_profiler_useHeartbeats;
v___x_808_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_684_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v_transparency_811_; uint8_t v___x_812_; 
v___x_809_ = lean_io_mono_nanos_now();
v___x_810_ = l_Lean_Meta_Context_config(v___y_679_);
v_transparency_811_ = lean_ctor_get_uint8(v___x_810_, 9);
lean_dec_ref(v___x_810_);
v___x_812_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_811_, v_transparency_670_);
if (v___x_812_ == 0)
{
lean_object* v_keyedConfig_813_; uint8_t v_trackZetaDelta_814_; lean_object* v_zetaDeltaSet_815_; lean_object* v_lctx_816_; lean_object* v_localInstances_817_; lean_object* v_defEqCtx_x3f_818_; lean_object* v_synthPendingDepth_819_; lean_object* v_customCanUnfoldPredicate_x3f_820_; uint8_t v_univApprox_821_; uint8_t v_inTypeClassResolution_822_; uint8_t v_cacheInferType_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_keyedConfig_813_ = lean_ctor_get(v___y_679_, 0);
v_trackZetaDelta_814_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7);
v_zetaDeltaSet_815_ = lean_ctor_get(v___y_679_, 1);
v_lctx_816_ = lean_ctor_get(v___y_679_, 2);
v_localInstances_817_ = lean_ctor_get(v___y_679_, 3);
v_defEqCtx_x3f_818_ = lean_ctor_get(v___y_679_, 4);
v_synthPendingDepth_819_ = lean_ctor_get(v___y_679_, 5);
v_customCanUnfoldPredicate_x3f_820_ = lean_ctor_get(v___y_679_, 6);
v_univApprox_821_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_822_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 2);
v_cacheInferType_823_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_813_);
v___x_824_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_670_, v_keyedConfig_813_);
lean_inc(v_customCanUnfoldPredicate_x3f_820_);
lean_inc(v_synthPendingDepth_819_);
lean_inc(v_defEqCtx_x3f_818_);
lean_inc_ref(v_localInstances_817_);
lean_inc_ref(v_lctx_816_);
lean_inc(v_zetaDeltaSet_815_);
v___x_825_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_zetaDeltaSet_815_);
lean_ctor_set(v___x_825_, 2, v_lctx_816_);
lean_ctor_set(v___x_825_, 3, v_localInstances_817_);
lean_ctor_set(v___x_825_, 4, v_defEqCtx_x3f_818_);
lean_ctor_set(v___x_825_, 5, v_synthPendingDepth_819_);
lean_ctor_set(v___x_825_, 6, v_customCanUnfoldPredicate_x3f_820_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*7, v_trackZetaDelta_814_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*7 + 1, v_univApprox_821_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*7 + 2, v_inTypeClassResolution_822_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*7 + 3, v_cacheInferType_823_);
v___x_826_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___x_825_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref_known(v___x_825_, 7);
v___y_757_ = v___x_809_;
v___y_758_ = v___x_808_;
v___y_759_ = v_a_806_;
v___y_760_ = v___x_826_;
goto v___jp_756_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v___y_757_ = v___x_809_;
v___y_758_ = v___x_808_;
v___y_759_ = v_a_806_;
v___y_760_ = v___x_827_;
goto v___jp_756_;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v_transparency_830_; uint8_t v___x_831_; 
v___x_828_ = lean_io_get_num_heartbeats();
v___x_829_ = l_Lean_Meta_Context_config(v___y_679_);
v_transparency_830_ = lean_ctor_get_uint8(v___x_829_, 9);
lean_dec_ref(v___x_829_);
v___x_831_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_830_, v_transparency_670_);
if (v___x_831_ == 0)
{
lean_object* v_keyedConfig_832_; uint8_t v_trackZetaDelta_833_; lean_object* v_zetaDeltaSet_834_; lean_object* v_lctx_835_; lean_object* v_localInstances_836_; lean_object* v_defEqCtx_x3f_837_; lean_object* v_synthPendingDepth_838_; lean_object* v_customCanUnfoldPredicate_x3f_839_; uint8_t v_univApprox_840_; uint8_t v_inTypeClassResolution_841_; uint8_t v_cacheInferType_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_keyedConfig_832_ = lean_ctor_get(v___y_679_, 0);
v_trackZetaDelta_833_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7);
v_zetaDeltaSet_834_ = lean_ctor_get(v___y_679_, 1);
v_lctx_835_ = lean_ctor_get(v___y_679_, 2);
v_localInstances_836_ = lean_ctor_get(v___y_679_, 3);
v_defEqCtx_x3f_837_ = lean_ctor_get(v___y_679_, 4);
v_synthPendingDepth_838_ = lean_ctor_get(v___y_679_, 5);
v_customCanUnfoldPredicate_x3f_839_ = lean_ctor_get(v___y_679_, 6);
v_univApprox_840_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_841_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 2);
v_cacheInferType_842_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_832_);
v___x_843_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_670_, v_keyedConfig_832_);
lean_inc(v_customCanUnfoldPredicate_x3f_839_);
lean_inc(v_synthPendingDepth_838_);
lean_inc(v_defEqCtx_x3f_837_);
lean_inc_ref(v_localInstances_836_);
lean_inc_ref(v_lctx_835_);
lean_inc(v_zetaDeltaSet_834_);
v___x_844_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_zetaDeltaSet_834_);
lean_ctor_set(v___x_844_, 2, v_lctx_835_);
lean_ctor_set(v___x_844_, 3, v_localInstances_836_);
lean_ctor_set(v___x_844_, 4, v_defEqCtx_x3f_837_);
lean_ctor_set(v___x_844_, 5, v_synthPendingDepth_838_);
lean_ctor_set(v___x_844_, 6, v_customCanUnfoldPredicate_x3f_839_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*7, v_trackZetaDelta_833_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*7 + 1, v_univApprox_840_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*7 + 2, v_inTypeClassResolution_841_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*7 + 3, v_cacheInferType_842_);
v___x_845_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___x_844_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref_known(v___x_844_, 7);
v___y_792_ = v___x_808_;
v___y_793_ = v___x_828_;
v___y_794_ = v_a_806_;
v___y_795_ = v___x_845_;
goto v___jp_791_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v___y_792_ = v___x_808_;
v___y_793_ = v___x_828_;
v___y_794_ = v_a_806_;
v___y_795_ = v___x_846_;
goto v___jp_791_;
}
}
}
}
v___jp_687_:
{
if (lean_obj_tag(v___y_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_a_689_ = lean_ctor_get(v___y_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___y_688_, 1);
v___x_690_ = lean_box(0);
v___x_691_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_686_, v_a_689_, v___x_690_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_679_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = l_List_reverse___redArg(v_a_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
return v___x_691_;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v___y_679_);
v_a_701_ = lean_ctor_get(v___y_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___y_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___y_688_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___y_688_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_889_, lean_object* v_g_890_, lean_object* v_e_891_, lean_object* v_cfg_892_, lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v___f_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v_transparency_boxed_903_; uint8_t v___x_14507__boxed_904_; lean_object* v_res_905_; 
v_transparency_boxed_903_ = lean_unbox(v_transparency_889_);
v___x_14507__boxed_904_ = lean_unbox(v___x_895_);
v_res_905_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_903_, v_g_890_, v_e_891_, v_cfg_892_, v___x_893_, v___x_894_, v___x_14507__boxed_904_, v___x_896_, v___f_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_907_, lean_object* v_g_908_, lean_object* v_cfg_909_, lean_object* v_e_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___x_924_; 
lean_inc_ref(v_e_910_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_916_, 0, v_e_910_);
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_918_ = lean_box(0);
v___x_919_ = 1;
v___x_920_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_921_ = lean_box(v_transparency_907_);
v___x_922_ = lean_box(v___x_919_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_923_, 0, v___x_921_);
lean_closure_set(v___f_923_, 1, v_g_908_);
lean_closure_set(v___f_923_, 2, v_e_910_);
lean_closure_set(v___f_923_, 3, v_cfg_909_);
lean_closure_set(v___f_923_, 4, v___x_918_);
lean_closure_set(v___f_923_, 5, v___x_917_);
lean_closure_set(v___f_923_, 6, v___x_922_);
lean_closure_set(v___f_923_, 7, v___x_920_);
lean_closure_set(v___f_923_, 8, v___f_916_);
v___x_924_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_923_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_925_, lean_object* v_g_926_, lean_object* v_cfg_927_, lean_object* v_e_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v_transparency_boxed_934_; lean_object* v_res_935_; 
v_transparency_boxed_934_ = lean_unbox(v_transparency_925_);
v_res_935_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_934_, v_g_926_, v_cfg_927_, v_e_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_936_, uint8_t v_transparency_937_, lean_object* v_lemmas_938_, lean_object* v_g_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_938_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_954_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_954_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_948_ = lean_box(v_transparency_937_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_949_, 0, v___x_948_);
lean_closure_set(v___f_949_, 1, v_g_939_);
lean_closure_set(v___f_949_, 2, v_cfg_936_);
v___x_950_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_950_, 0, lean_box(0));
lean_closure_set(v___x_950_, 1, lean_box(0));
lean_closure_set(v___x_950_, 2, v___f_949_);
lean_closure_set(v___x_950_, 3, v_a_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_950_);
v___x_952_ = v___x_946_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v_g_939_);
lean_dec_ref(v_cfg_936_);
v_a_955_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_943_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_943_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_963_, lean_object* v_transparency_964_, lean_object* v_lemmas_965_, lean_object* v_g_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
uint8_t v_transparency_boxed_970_; lean_object* v_res_971_; 
v_transparency_boxed_970_ = lean_unbox(v_transparency_964_);
v_res_971_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_963_, v_transparency_boxed_970_, v_lemmas_965_, v_g_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_972_, uint8_t v_transparency_973_, lean_object* v_lemmas_974_, lean_object* v_g_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_972_, v_transparency_973_, v_lemmas_974_, v_g_975_, v_a_977_, v_a_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_982_, lean_object* v_transparency_983_, lean_object* v_lemmas_984_, lean_object* v_g_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
uint8_t v_transparency_boxed_991_; lean_object* v_res_992_; 
v_transparency_boxed_991_ = lean_unbox(v_transparency_983_);
v_res_992_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_982_, v_transparency_boxed_991_, v_lemmas_984_, v_g_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_994_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1001_, v_x_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1009_, uint8_t v_transparency_1010_, lean_object* v_lemmas_1011_, lean_object* v_g_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1009_, v_transparency_1010_, v_lemmas_1011_, v_g_1012_, v_a_1014_, v_a_1016_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = l_Lean_Meta_Iterator_head___redArg(v_a_1019_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1020_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1018_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1018_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1029_, lean_object* v_transparency_1030_, lean_object* v_lemmas_1031_, lean_object* v_g_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
uint8_t v_transparency_boxed_1038_; lean_object* v_res_1039_; 
v_transparency_boxed_1038_ = lean_unbox(v_transparency_1030_);
v_res_1039_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1029_, v_transparency_boxed_1038_, v_lemmas_1031_, v_g_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1040_){
_start:
{
lean_object* v_toApplyRulesConfig_1041_; lean_object* v_toBacktrackConfig_1042_; 
v_toApplyRulesConfig_1041_ = lean_ctor_get(v_x_1040_, 0);
v_toBacktrackConfig_1042_ = lean_ctor_get(v_toApplyRulesConfig_1041_, 0);
lean_inc_ref(v_toBacktrackConfig_1042_);
return v_toBacktrackConfig_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1043_);
lean_dec_ref(v_x_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1047_, lean_object* v_discharge_1048_, lean_object* v_g_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v_g_1049_);
v___x_1055_ = lean_apply_6(v_test_1047_, v_g_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1066_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_unbox(v_a_1056_);
lean_dec(v_a_1056_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_del_object(v___x_1058_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
v___x_1061_ = lean_apply_6(v_discharge_1048_, v_g_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec(v_g_1049_);
lean_dec_ref(v_discharge_1048_);
v___x_1062_ = lean_box(0);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1062_);
v___x_1064_ = v___x_1058_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_g_1049_);
lean_dec_ref(v_discharge_1048_);
v_a_1067_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1055_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1075_, lean_object* v_discharge_1076_, lean_object* v_g_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1075_, v_discharge_1076_, v_g_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1084_, lean_object* v_test_1085_){
_start:
{
lean_object* v_toApplyRulesConfig_1086_; lean_object* v_toBacktrackConfig_1087_; uint8_t v_backtracking_1088_; uint8_t v_intro_1089_; uint8_t v_constructor_1090_; uint8_t v_suggestions_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1123_; 
v_toApplyRulesConfig_1086_ = lean_ctor_get(v_cfg_1084_, 0);
lean_inc_ref(v_toApplyRulesConfig_1086_);
v_toBacktrackConfig_1087_ = lean_ctor_get(v_toApplyRulesConfig_1086_, 0);
lean_inc_ref(v_toBacktrackConfig_1087_);
v_backtracking_1088_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*1);
v_intro_1089_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*1 + 1);
v_constructor_1090_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*1 + 2);
v_suggestions_1091_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*1 + 3);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_cfg_1084_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_cfg_1084_, 0);
lean_dec(v_unused_1124_);
v___x_1093_ = v_cfg_1084_;
v_isShared_1094_ = v_isSharedCheck_1123_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v_cfg_1084_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1123_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_toApplyConfig_1095_; uint8_t v_transparency_1096_; uint8_t v_symm_1097_; uint8_t v_exfalso_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1121_; 
v_toApplyConfig_1095_ = lean_ctor_get(v_toApplyRulesConfig_1086_, 1);
v_transparency_1096_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1086_, sizeof(void*)*2);
v_symm_1097_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1086_, sizeof(void*)*2 + 1);
v_exfalso_1098_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1086_, sizeof(void*)*2 + 2);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_toApplyRulesConfig_1086_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_toApplyRulesConfig_1086_, 0);
lean_dec(v_unused_1122_);
v___x_1100_ = v_toApplyRulesConfig_1086_;
v_isShared_1101_ = v_isSharedCheck_1121_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_toApplyConfig_1095_);
lean_dec(v_toApplyRulesConfig_1086_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1121_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_maxDepth_1102_; lean_object* v_proc_1103_; lean_object* v_suspend_1104_; lean_object* v_discharge_1105_; uint8_t v_commitIndependentGoals_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1120_; 
v_maxDepth_1102_ = lean_ctor_get(v_toBacktrackConfig_1087_, 0);
v_proc_1103_ = lean_ctor_get(v_toBacktrackConfig_1087_, 1);
v_suspend_1104_ = lean_ctor_get(v_toBacktrackConfig_1087_, 2);
v_discharge_1105_ = lean_ctor_get(v_toBacktrackConfig_1087_, 3);
v_commitIndependentGoals_1106_ = lean_ctor_get_uint8(v_toBacktrackConfig_1087_, sizeof(void*)*4);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_toBacktrackConfig_1087_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1108_ = v_toBacktrackConfig_1087_;
v_isShared_1109_ = v_isSharedCheck_1120_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_discharge_1105_);
lean_inc(v_suspend_1104_);
lean_inc(v_proc_1103_);
lean_inc(v_maxDepth_1102_);
lean_dec(v_toBacktrackConfig_1087_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1120_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___f_1110_; lean_object* v___x_1112_; 
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1110_, 0, v_test_1085_);
lean_closure_set(v___f_1110_, 1, v_discharge_1105_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v___f_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_maxDepth_1102_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_proc_1103_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_suspend_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 3, v___f_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*4, v_commitIndependentGoals_1106_);
v___x_1112_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1112_);
v___x_1114_ = v___x_1100_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_toApplyConfig_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1118_, sizeof(void*)*2, v_transparency_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1118_, sizeof(void*)*2 + 1, v_symm_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1118_, sizeof(void*)*2 + 2, v_exfalso_1098_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1114_);
v___x_1116_ = v___x_1093_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1117_, sizeof(void*)*1, v_backtracking_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1117_, sizeof(void*)*1 + 1, v_intro_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1117_, sizeof(void*)*1 + 2, v_constructor_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1117_, sizeof(void*)*1 + 3, v_suggestions_1091_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1125_, lean_object* v_proc_1126_, lean_object* v_orig_1127_, lean_object* v_goals_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
if (lean_obj_tag(v_goals_1128_) == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_proc_1126_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
v___x_1134_ = lean_apply_7(v_proc_1125_, v_orig_1127_, v_goals_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, lean_box(0));
return v___x_1134_;
}
else
{
lean_object* v_head_1135_; lean_object* v_tail_1136_; lean_object* v___x_1137_; 
v_head_1135_ = lean_ctor_get(v_goals_1128_, 0);
v_tail_1136_ = lean_ctor_get(v_goals_1128_, 1);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v_head_1135_);
v___x_1137_ = lean_apply_6(v_proc_1126_, v_head_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, lean_box(0));
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
lean_inc(v_tail_1136_);
lean_dec_ref_known(v_goals_1128_, 2);
lean_dec(v_orig_1127_);
lean_dec_ref(v_proc_1125_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = l_List_appendTR___redArg(v_a_1138_, v_tail_1136_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1160_; 
v_a_1148_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1150_ = v___x_1137_;
v_isShared_1151_ = v_isSharedCheck_1160_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1137_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1160_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v___y_1153_; uint8_t v___x_1158_; 
v___x_1158_ = l_Lean_Exception_isInterrupt(v_a_1148_);
if (v___x_1158_ == 0)
{
uint8_t v___x_1159_; 
lean_inc(v_a_1148_);
v___x_1159_ = l_Lean_Exception_isRuntime(v_a_1148_);
v___y_1153_ = v___x_1159_;
goto v___jp_1152_;
}
else
{
v___y_1153_ = v___x_1158_;
goto v___jp_1152_;
}
v___jp_1152_:
{
if (v___y_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_del_object(v___x_1150_);
lean_dec(v_a_1148_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
v___x_1154_ = lean_apply_7(v_proc_1125_, v_orig_1127_, v_goals_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, lean_box(0));
return v___x_1154_;
}
else
{
lean_object* v___x_1156_; 
lean_dec_ref_known(v_goals_1128_, 2);
lean_dec(v_orig_1127_);
lean_dec_ref(v_proc_1125_);
if (v_isShared_1151_ == 0)
{
v___x_1156_ = v___x_1150_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1148_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1161_, lean_object* v_proc_1162_, lean_object* v_orig_1163_, lean_object* v_goals_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1161_, v_proc_1162_, v_orig_1163_, v_goals_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1171_, lean_object* v_proc_1172_){
_start:
{
lean_object* v_toApplyRulesConfig_1173_; lean_object* v_toBacktrackConfig_1174_; uint8_t v_backtracking_1175_; uint8_t v_intro_1176_; uint8_t v_constructor_1177_; uint8_t v_suggestions_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1210_; 
v_toApplyRulesConfig_1173_ = lean_ctor_get(v_cfg_1171_, 0);
lean_inc_ref(v_toApplyRulesConfig_1173_);
v_toBacktrackConfig_1174_ = lean_ctor_get(v_toApplyRulesConfig_1173_, 0);
lean_inc_ref(v_toBacktrackConfig_1174_);
v_backtracking_1175_ = lean_ctor_get_uint8(v_cfg_1171_, sizeof(void*)*1);
v_intro_1176_ = lean_ctor_get_uint8(v_cfg_1171_, sizeof(void*)*1 + 1);
v_constructor_1177_ = lean_ctor_get_uint8(v_cfg_1171_, sizeof(void*)*1 + 2);
v_suggestions_1178_ = lean_ctor_get_uint8(v_cfg_1171_, sizeof(void*)*1 + 3);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_cfg_1171_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v_cfg_1171_, 0);
lean_dec(v_unused_1211_);
v___x_1180_ = v_cfg_1171_;
v_isShared_1181_ = v_isSharedCheck_1210_;
goto v_resetjp_1179_;
}
else
{
lean_dec(v_cfg_1171_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1210_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_toApplyConfig_1182_; uint8_t v_transparency_1183_; uint8_t v_symm_1184_; uint8_t v_exfalso_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1208_; 
v_toApplyConfig_1182_ = lean_ctor_get(v_toApplyRulesConfig_1173_, 1);
v_transparency_1183_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1173_, sizeof(void*)*2);
v_symm_1184_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1173_, sizeof(void*)*2 + 1);
v_exfalso_1185_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1173_, sizeof(void*)*2 + 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_toApplyRulesConfig_1173_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_toApplyRulesConfig_1173_, 0);
lean_dec(v_unused_1209_);
v___x_1187_ = v_toApplyRulesConfig_1173_;
v_isShared_1188_ = v_isSharedCheck_1208_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_toApplyConfig_1182_);
lean_dec(v_toApplyRulesConfig_1173_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1208_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_maxDepth_1189_; lean_object* v_proc_1190_; lean_object* v_suspend_1191_; lean_object* v_discharge_1192_; uint8_t v_commitIndependentGoals_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1207_; 
v_maxDepth_1189_ = lean_ctor_get(v_toBacktrackConfig_1174_, 0);
v_proc_1190_ = lean_ctor_get(v_toBacktrackConfig_1174_, 1);
v_suspend_1191_ = lean_ctor_get(v_toBacktrackConfig_1174_, 2);
v_discharge_1192_ = lean_ctor_get(v_toBacktrackConfig_1174_, 3);
v_commitIndependentGoals_1193_ = lean_ctor_get_uint8(v_toBacktrackConfig_1174_, sizeof(void*)*4);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_toBacktrackConfig_1174_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1195_ = v_toBacktrackConfig_1174_;
v_isShared_1196_ = v_isSharedCheck_1207_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_discharge_1192_);
lean_inc(v_suspend_1191_);
lean_inc(v_proc_1190_);
lean_inc(v_maxDepth_1189_);
lean_dec(v_toBacktrackConfig_1174_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1207_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___f_1197_; lean_object* v___x_1199_; 
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1197_, 0, v_proc_1190_);
lean_closure_set(v___f_1197_, 1, v_proc_1172_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___f_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_maxDepth_1189_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___f_1197_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_suspend_1191_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_discharge_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*4, v_commitIndependentGoals_1193_);
v___x_1199_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1199_);
v___x_1201_ = v___x_1187_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_toApplyConfig_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*2, v_transparency_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*2 + 1, v_symm_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*2 + 2, v_exfalso_1185_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1201_);
v___x_1203_ = v___x_1180_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*1, v_backtracking_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*1 + 1, v_intro_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*1 + 2, v_constructor_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*1 + 3, v_suggestions_1178_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = 1;
v___x_1219_ = l_Lean_Meta_intro1Core(v_g_1212_, v___x_1218_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1237_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1237_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1237_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_snd_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1235_; 
v_snd_1224_ = lean_ctor_get(v_a_1220_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_a_1220_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_a_1220_, 0);
lean_dec(v_unused_1236_);
v___x_1226_ = v_a_1220_;
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1224_);
lean_dec(v_a_1220_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(0);
if (v_isShared_1227_ == 0)
{
lean_ctor_set_tag(v___x_1226_, 1);
lean_ctor_set(v___x_1226_, 1, v___x_1228_);
lean_ctor_set(v___x_1226_, 0, v_snd_1224_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_snd_1224_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1230_);
v___x_1232_ = v___x_1222_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1219_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1219_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1254_){
_start:
{
lean_object* v___f_1255_; lean_object* v___x_1256_; 
v___f_1255_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1256_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1254_, v___f_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_ks_1261_; lean_object* v_vs_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1286_; 
v_ks_1261_ = lean_ctor_get(v_x_1257_, 0);
v_vs_1262_ = lean_ctor_get(v_x_1257_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_x_1257_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1264_ = v_x_1257_;
v_isShared_1265_ = v_isSharedCheck_1286_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_vs_1262_);
lean_inc(v_ks_1261_);
lean_dec(v_x_1257_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1286_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = lean_array_get_size(v_ks_1261_);
v___x_1267_ = lean_nat_dec_lt(v_x_1258_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_dec(v_x_1258_);
v___x_1268_ = lean_array_push(v_ks_1261_, v_x_1259_);
v___x_1269_ = lean_array_push(v_vs_1262_, v_x_1260_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1269_);
lean_ctor_set(v___x_1264_, 0, v___x_1268_);
v___x_1271_ = v___x_1264_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_object* v_k_x27_1273_; uint8_t v___x_1274_; 
v_k_x27_1273_ = lean_array_fget_borrowed(v_ks_1261_, v_x_1258_);
v___x_1274_ = l_Lean_instBEqMVarId_beq(v_x_1259_, v_k_x27_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1276_; 
if (v_isShared_1265_ == 0)
{
v___x_1276_ = v___x_1264_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_ks_1261_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_vs_1262_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v_x_1258_, v___x_1277_);
lean_dec(v_x_1258_);
v_x_1257_ = v___x_1276_;
v_x_1258_ = v___x_1278_;
goto _start;
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1281_ = lean_array_fset(v_ks_1261_, v_x_1258_, v_x_1259_);
v___x_1282_ = lean_array_fset(v_vs_1262_, v_x_1258_, v_x_1260_);
lean_dec(v_x_1258_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1282_);
lean_ctor_set(v___x_1264_, 0, v___x_1281_);
v___x_1284_ = v___x_1264_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1287_, lean_object* v_k_1288_, lean_object* v_v_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1287_, v___x_1290_, v_k_1288_, v_v_1289_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1293_, size_t v_x_1294_, size_t v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_object* v_es_1298_; size_t v___x_1299_; size_t v___x_1300_; lean_object* v_j_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_es_1298_ = lean_ctor_get(v_x_1293_, 0);
v___x_1299_ = ((size_t)31ULL);
v___x_1300_ = lean_usize_land(v_x_1294_, v___x_1299_);
v_j_1301_ = lean_usize_to_nat(v___x_1300_);
v___x_1302_ = lean_array_get_size(v_es_1298_);
v___x_1303_ = lean_nat_dec_lt(v_j_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v_j_1301_);
lean_dec(v_x_1297_);
lean_dec(v_x_1296_);
return v_x_1293_;
}
else
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1342_; 
lean_inc_ref(v_es_1298_);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_x_1293_, 0);
lean_dec(v_unused_1343_);
v___x_1305_ = v_x_1293_;
v_isShared_1306_ = v_isSharedCheck_1342_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_x_1293_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1342_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_v_1307_; lean_object* v___x_1308_; lean_object* v_xs_x27_1309_; lean_object* v___y_1311_; 
v_v_1307_ = lean_array_fget(v_es_1298_, v_j_1301_);
v___x_1308_ = lean_box(0);
v_xs_x27_1309_ = lean_array_fset(v_es_1298_, v_j_1301_, v___x_1308_);
switch(lean_obj_tag(v_v_1307_))
{
case 0:
{
lean_object* v_key_1316_; lean_object* v_val_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1327_; 
v_key_1316_ = lean_ctor_get(v_v_1307_, 0);
v_val_1317_ = lean_ctor_get(v_v_1307_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_v_1307_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1319_ = v_v_1307_;
v_isShared_1320_ = v_isSharedCheck_1327_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_val_1317_);
lean_inc(v_key_1316_);
lean_dec(v_v_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1327_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
uint8_t v___x_1321_; 
v___x_1321_ = l_Lean_instBEqMVarId_beq(v_x_1296_, v_key_1316_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1319_);
v___x_1322_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1316_, v_val_1317_, v_x_1296_, v_x_1297_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___y_1311_ = v___x_1323_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1325_; 
lean_dec(v_val_1317_);
lean_dec(v_key_1316_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_x_1297_);
lean_ctor_set(v___x_1319_, 0, v_x_1296_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_x_1296_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_x_1297_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v___y_1311_ = v___x_1325_;
goto v___jp_1310_;
}
}
}
}
case 1:
{
lean_object* v_node_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1340_; 
v_node_1328_ = lean_ctor_get(v_v_1307_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_v_1307_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1330_ = v_v_1307_;
v_isShared_1331_ = v_isSharedCheck_1340_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_node_1328_);
lean_dec(v_v_1307_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1340_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1332_ = ((size_t)5ULL);
v___x_1333_ = lean_usize_shift_right(v_x_1294_, v___x_1332_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_x_1295_, v___x_1334_);
v___x_1336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1328_, v___x_1333_, v___x_1335_, v_x_1296_, v_x_1297_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1336_);
v___x_1338_ = v___x_1330_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
v___y_1311_ = v___x_1338_;
goto v___jp_1310_;
}
}
}
default: 
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_x_1296_);
lean_ctor_set(v___x_1341_, 1, v_x_1297_);
v___y_1311_ = v___x_1341_;
goto v___jp_1310_;
}
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_array_fset(v_xs_x27_1309_, v_j_1301_, v___y_1311_);
lean_dec(v_j_1301_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1312_);
v___x_1314_ = v___x_1305_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
else
{
lean_object* v_ks_1344_; lean_object* v_vs_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1363_; 
v_ks_1344_ = lean_ctor_get(v_x_1293_, 0);
v_vs_1345_ = lean_ctor_get(v_x_1293_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1347_ = v_x_1293_;
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_vs_1345_);
lean_inc(v_ks_1344_);
lean_dec(v_x_1293_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_ks_1344_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_vs_1345_);
v___x_1350_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v_newNode_1351_; size_t v___x_1352_; uint8_t v___x_1353_; 
v_newNode_1351_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1350_, v_x_1296_, v_x_1297_);
v___x_1352_ = ((size_t)7ULL);
v___x_1353_ = lean_usize_dec_le(v___x_1352_, v_x_1295_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1351_);
v___x_1355_ = lean_unsigned_to_nat(4u);
v___x_1356_ = lean_nat_dec_lt(v___x_1354_, v___x_1355_);
lean_dec(v___x_1354_);
if (v___x_1356_ == 0)
{
lean_object* v_ks_1357_; lean_object* v_vs_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_ks_1357_ = lean_ctor_get(v_newNode_1351_, 0);
lean_inc_ref(v_ks_1357_);
v_vs_1358_ = lean_ctor_get(v_newNode_1351_, 1);
lean_inc_ref(v_vs_1358_);
lean_dec_ref(v_newNode_1351_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1295_, v_ks_1357_, v_vs_1358_, v___x_1359_, v___x_1360_);
lean_dec_ref(v_vs_1358_);
lean_dec_ref(v_ks_1357_);
return v___x_1361_;
}
else
{
return v_newNode_1351_;
}
}
else
{
return v_newNode_1351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1364_, lean_object* v_keys_1365_, lean_object* v_vals_1366_, lean_object* v_i_1367_, lean_object* v_entries_1368_){
_start:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_keys_1365_);
v___x_1370_ = lean_nat_dec_lt(v_i_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v_i_1367_);
return v_entries_1368_;
}
else
{
lean_object* v_k_1371_; lean_object* v_v_1372_; uint64_t v___x_1373_; size_t v_h_1374_; size_t v___x_1375_; lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; size_t v_h_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_k_1371_ = lean_array_fget_borrowed(v_keys_1365_, v_i_1367_);
v_v_1372_ = lean_array_fget_borrowed(v_vals_1366_, v_i_1367_);
v___x_1373_ = l_Lean_instHashableMVarId_hash(v_k_1371_);
v_h_1374_ = lean_uint64_to_usize(v___x_1373_);
v___x_1375_ = ((size_t)5ULL);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_sub(v_depth_1364_, v___x_1377_);
v___x_1379_ = lean_usize_mul(v___x_1375_, v___x_1378_);
v_h_1380_ = lean_usize_shift_right(v_h_1374_, v___x_1379_);
v___x_1381_ = lean_nat_add(v_i_1367_, v___x_1376_);
lean_dec(v_i_1367_);
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
v___x_1382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1368_, v_h_1380_, v_depth_1364_, v_k_1371_, v_v_1372_);
v_i_1367_ = v___x_1381_;
v_entries_1368_ = v___x_1382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1384_, lean_object* v_keys_1385_, lean_object* v_vals_1386_, lean_object* v_i_1387_, lean_object* v_entries_1388_){
_start:
{
size_t v_depth_boxed_1389_; lean_object* v_res_1390_; 
v_depth_boxed_1389_ = lean_unbox_usize(v_depth_1384_);
lean_dec(v_depth_1384_);
v_res_1390_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1389_, v_keys_1385_, v_vals_1386_, v_i_1387_, v_entries_1388_);
lean_dec_ref(v_vals_1386_);
lean_dec_ref(v_keys_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
size_t v_x_832__boxed_1396_; size_t v_x_833__boxed_1397_; lean_object* v_res_1398_; 
v_x_832__boxed_1396_ = lean_unbox_usize(v_x_1392_);
lean_dec(v_x_1392_);
v_x_833__boxed_1397_ = lean_unbox_usize(v_x_1393_);
lean_dec(v_x_1393_);
v_res_1398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1391_, v_x_832__boxed_1396_, v_x_833__boxed_1397_, v_x_1394_, v_x_1395_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
uint64_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = l_Lean_instHashableMVarId_hash(v_x_1400_);
v___x_1403_ = lean_uint64_to_usize(v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1399_, v___x_1403_, v___x_1404_, v_x_1400_, v_x_1401_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1406_, lean_object* v_val_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_mctx_1411_; lean_object* v_cache_1412_; lean_object* v_zetaDeltaFVarIds_1413_; lean_object* v_postponed_1414_; lean_object* v_diag_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1444_; 
v___x_1410_ = lean_st_ref_take(v___y_1408_);
v_mctx_1411_ = lean_ctor_get(v___x_1410_, 0);
v_cache_1412_ = lean_ctor_get(v___x_1410_, 1);
v_zetaDeltaFVarIds_1413_ = lean_ctor_get(v___x_1410_, 2);
v_postponed_1414_ = lean_ctor_get(v___x_1410_, 3);
v_diag_1415_ = lean_ctor_get(v___x_1410_, 4);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1417_ = v___x_1410_;
v_isShared_1418_ = v_isSharedCheck_1444_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_diag_1415_);
lean_inc(v_postponed_1414_);
lean_inc(v_zetaDeltaFVarIds_1413_);
lean_inc(v_cache_1412_);
lean_inc(v_mctx_1411_);
lean_dec(v___x_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1444_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_depth_1419_; lean_object* v_levelAssignDepth_1420_; lean_object* v_lmvarCounter_1421_; lean_object* v_mvarCounter_1422_; lean_object* v_lDecls_1423_; lean_object* v_decls_1424_; lean_object* v_userNames_1425_; lean_object* v_lAssignment_1426_; lean_object* v_eAssignment_1427_; lean_object* v_dAssignment_1428_; lean_object* v_instanceTypedMVars_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1443_; 
v_depth_1419_ = lean_ctor_get(v_mctx_1411_, 0);
v_levelAssignDepth_1420_ = lean_ctor_get(v_mctx_1411_, 1);
v_lmvarCounter_1421_ = lean_ctor_get(v_mctx_1411_, 2);
v_mvarCounter_1422_ = lean_ctor_get(v_mctx_1411_, 3);
v_lDecls_1423_ = lean_ctor_get(v_mctx_1411_, 4);
v_decls_1424_ = lean_ctor_get(v_mctx_1411_, 5);
v_userNames_1425_ = lean_ctor_get(v_mctx_1411_, 6);
v_lAssignment_1426_ = lean_ctor_get(v_mctx_1411_, 7);
v_eAssignment_1427_ = lean_ctor_get(v_mctx_1411_, 8);
v_dAssignment_1428_ = lean_ctor_get(v_mctx_1411_, 9);
v_instanceTypedMVars_1429_ = lean_ctor_get(v_mctx_1411_, 10);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_mctx_1411_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1431_ = v_mctx_1411_;
v_isShared_1432_ = v_isSharedCheck_1443_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_instanceTypedMVars_1429_);
lean_inc(v_dAssignment_1428_);
lean_inc(v_eAssignment_1427_);
lean_inc(v_lAssignment_1426_);
lean_inc(v_userNames_1425_);
lean_inc(v_decls_1424_);
lean_inc(v_lDecls_1423_);
lean_inc(v_mvarCounter_1422_);
lean_inc(v_lmvarCounter_1421_);
lean_inc(v_levelAssignDepth_1420_);
lean_inc(v_depth_1419_);
lean_dec(v_mctx_1411_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1443_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1427_, v_mvarId_1406_, v_val_1407_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 8, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_depth_1419_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_levelAssignDepth_1420_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_lmvarCounter_1421_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_mvarCounter_1422_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v_lDecls_1423_);
lean_ctor_set(v_reuseFailAlloc_1442_, 5, v_decls_1424_);
lean_ctor_set(v_reuseFailAlloc_1442_, 6, v_userNames_1425_);
lean_ctor_set(v_reuseFailAlloc_1442_, 7, v_lAssignment_1426_);
lean_ctor_set(v_reuseFailAlloc_1442_, 8, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1442_, 9, v_dAssignment_1428_);
lean_ctor_set(v_reuseFailAlloc_1442_, 10, v_instanceTypedMVars_1429_);
v___x_1435_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1435_);
v___x_1437_ = v___x_1417_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_cache_1412_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_zetaDeltaFVarIds_1413_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_postponed_1414_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_diag_1415_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_st_ref_put(v___y_1408_, v___x_1437_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1445_, lean_object* v_val_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1445_, v_val_1446_, v___y_1447_);
lean_dec(v___y_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
lean_inc(v_g_1450_);
v___x_1456_ = l_Lean_MVarId_getType(v_g_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = lean_box(0);
v___x_1459_ = l_Lean_Meta_synthInstance(v_a_1457_, v___x_1458_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1450_, v_a_1460_, v___y_1452_);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1461_, 0);
lean_dec(v_unused_1470_);
v___x_1463_ = v___x_1461_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1461_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_box(0);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_g_1450_);
v_a_1471_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1459_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1459_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_g_1450_);
v_a_1479_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1456_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1456_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1495_){
_start:
{
lean_object* v___f_1496_; lean_object* v___x_1497_; 
v___f_1496_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1497_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1495_, v___f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1498_, lean_object* v_val_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1498_, v_val_1499_, v___y_1501_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1506_, lean_object* v_val_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1506_, v_val_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1515_, v_x_1516_, v_x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1519_, lean_object* v_x_1520_, size_t v_x_1521_, size_t v_x_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1520_, v_x_1521_, v_x_1522_, v_x_1523_, v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
size_t v_x_1153__boxed_1532_; size_t v_x_1154__boxed_1533_; lean_object* v_res_1534_; 
v_x_1153__boxed_1532_ = lean_unbox_usize(v_x_1528_);
lean_dec(v_x_1528_);
v_x_1154__boxed_1533_ = lean_unbox_usize(v_x_1529_);
lean_dec(v_x_1529_);
v_res_1534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1526_, v_x_1527_, v_x_1153__boxed_1532_, v_x_1154__boxed_1533_, v_x_1530_, v_x_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1535_, lean_object* v_n_1536_, lean_object* v_k_1537_, lean_object* v_v_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1536_, v_k_1537_, v_v_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1540_, size_t v_depth_1541_, lean_object* v_keys_1542_, lean_object* v_vals_1543_, lean_object* v_heq_1544_, lean_object* v_i_1545_, lean_object* v_entries_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1541_, v_keys_1542_, v_vals_1543_, v_i_1545_, v_entries_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_depth_1549_, lean_object* v_keys_1550_, lean_object* v_vals_1551_, lean_object* v_heq_1552_, lean_object* v_i_1553_, lean_object* v_entries_1554_){
_start:
{
size_t v_depth_boxed_1555_; lean_object* v_res_1556_; 
v_depth_boxed_1555_ = lean_unbox_usize(v_depth_1549_);
lean_dec(v_depth_1549_);
v_res_1556_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1548_, v_depth_boxed_1555_, v_keys_1550_, v_vals_1551_, v_heq_1552_, v_i_1553_, v_entries_1554_);
lean_dec_ref(v_vals_1551_);
lean_dec_ref(v_keys_1550_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1558_, v_x_1559_, v_x_1560_, v_x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1563_, lean_object* v_discharge_1564_, lean_object* v_g_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v_g_1565_);
v___x_1571_ = lean_apply_6(v_discharge_1563_, v_g_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, lean_box(0));
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec(v_g_1565_);
lean_dec_ref(v_discharge_1564_);
return v___x_1571_;
}
else
{
lean_object* v_a_1572_; uint8_t v___y_1574_; uint8_t v___x_1576_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
v___x_1576_ = l_Lean_Exception_isInterrupt(v_a_1572_);
if (v___x_1576_ == 0)
{
uint8_t v___x_1577_; 
v___x_1577_ = l_Lean_Exception_isRuntime(v_a_1572_);
v___y_1574_ = v___x_1577_;
goto v___jp_1573_;
}
else
{
lean_dec(v_a_1572_);
v___y_1574_ = v___x_1576_;
goto v___jp_1573_;
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1571_, 1);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
v___x_1575_ = lean_apply_6(v_discharge_1564_, v_g_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, lean_box(0));
return v___x_1575_;
}
else
{
lean_dec(v_g_1565_);
lean_dec_ref(v_discharge_1564_);
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1578_, lean_object* v_discharge_1579_, lean_object* v_g_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1578_, v_discharge_1579_, v_g_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1587_, lean_object* v_discharge_1588_){
_start:
{
lean_object* v_toApplyRulesConfig_1589_; lean_object* v_toBacktrackConfig_1590_; uint8_t v_backtracking_1591_; uint8_t v_intro_1592_; uint8_t v_constructor_1593_; uint8_t v_suggestions_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1626_; 
v_toApplyRulesConfig_1589_ = lean_ctor_get(v_cfg_1587_, 0);
lean_inc_ref(v_toApplyRulesConfig_1589_);
v_toBacktrackConfig_1590_ = lean_ctor_get(v_toApplyRulesConfig_1589_, 0);
lean_inc_ref(v_toBacktrackConfig_1590_);
v_backtracking_1591_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*1);
v_intro_1592_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*1 + 1);
v_constructor_1593_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*1 + 2);
v_suggestions_1594_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*1 + 3);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_cfg_1587_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v_cfg_1587_, 0);
lean_dec(v_unused_1627_);
v___x_1596_ = v_cfg_1587_;
v_isShared_1597_ = v_isSharedCheck_1626_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_cfg_1587_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1626_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_toApplyConfig_1598_; uint8_t v_transparency_1599_; uint8_t v_symm_1600_; uint8_t v_exfalso_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1624_; 
v_toApplyConfig_1598_ = lean_ctor_get(v_toApplyRulesConfig_1589_, 1);
v_transparency_1599_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1589_, sizeof(void*)*2);
v_symm_1600_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1589_, sizeof(void*)*2 + 1);
v_exfalso_1601_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1589_, sizeof(void*)*2 + 2);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_toApplyRulesConfig_1589_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v_toApplyRulesConfig_1589_, 0);
lean_dec(v_unused_1625_);
v___x_1603_ = v_toApplyRulesConfig_1589_;
v_isShared_1604_ = v_isSharedCheck_1624_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_toApplyConfig_1598_);
lean_dec(v_toApplyRulesConfig_1589_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1624_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_maxDepth_1605_; lean_object* v_proc_1606_; lean_object* v_suspend_1607_; lean_object* v_discharge_1608_; uint8_t v_commitIndependentGoals_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1623_; 
v_maxDepth_1605_ = lean_ctor_get(v_toBacktrackConfig_1590_, 0);
v_proc_1606_ = lean_ctor_get(v_toBacktrackConfig_1590_, 1);
v_suspend_1607_ = lean_ctor_get(v_toBacktrackConfig_1590_, 2);
v_discharge_1608_ = lean_ctor_get(v_toBacktrackConfig_1590_, 3);
v_commitIndependentGoals_1609_ = lean_ctor_get_uint8(v_toBacktrackConfig_1590_, sizeof(void*)*4);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_toBacktrackConfig_1590_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1611_ = v_toBacktrackConfig_1590_;
v_isShared_1612_ = v_isSharedCheck_1623_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_discharge_1608_);
lean_inc(v_suspend_1607_);
lean_inc(v_proc_1606_);
lean_inc(v_maxDepth_1605_);
lean_dec(v_toBacktrackConfig_1590_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1623_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___f_1613_; lean_object* v___x_1615_; 
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1613_, 0, v_discharge_1588_);
lean_closure_set(v___f_1613_, 1, v_discharge_1608_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 3, v___f_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_maxDepth_1605_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_proc_1606_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_suspend_1607_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v___f_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1622_, sizeof(void*)*4, v_commitIndependentGoals_1609_);
v___x_1615_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1617_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1615_);
v___x_1617_ = v___x_1603_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_toApplyConfig_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*2, v_transparency_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*2 + 1, v_symm_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*2 + 2, v_exfalso_1601_);
v___x_1617_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1617_);
v___x_1619_ = v___x_1596_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*1, v_backtracking_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*1 + 1, v_intro_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*1 + 2, v_constructor_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*1 + 3, v_suggestions_1594_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = 1;
v___x_1635_ = l_Lean_Meta_intro1Core(v_g_1628_, v___x_1634_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1654_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1654_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1654_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_snd_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1652_; 
v_snd_1640_ = lean_ctor_get(v_a_1636_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_a_1636_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v_a_1636_, 0);
lean_dec(v_unused_1653_);
v___x_1642_ = v_a_1636_;
v_isShared_1643_ = v_isSharedCheck_1652_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_snd_1640_);
lean_dec(v_a_1636_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1652_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
lean_ctor_set(v___x_1642_, 1, v___x_1644_);
lean_ctor_set(v___x_1642_, 0, v_snd_1640_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_snd_1640_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1647_);
v___x_1649_ = v___x_1638_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1655_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1635_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1635_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1671_){
_start:
{
lean_object* v___f_1672_; lean_object* v___x_1673_; 
v___f_1672_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1673_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1671_, v___f_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1685_ = l_Lean_MVarId_constructor(v_g_1678_, v___x_1684_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_a_1686_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1685_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1685_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1711_){
_start:
{
lean_object* v___f_1712_; lean_object* v___x_1713_; 
v___f_1712_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1713_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1711_, v___f_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
lean_inc(v_g_1716_);
v___x_1722_ = l_Lean_MVarId_getType(v_g_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = lean_box(0);
v___x_1725_ = l_Lean_Meta_synthInstance(v_a_1723_, v___x_1724_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1735_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1716_, v_a_1726_, v___y_1718_);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v___x_1727_, 0);
lean_dec(v_unused_1736_);
v___x_1729_ = v___x_1727_;
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v___x_1727_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1731_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_g_1716_);
v_a_1737_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1725_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_g_1716_);
v_a_1745_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1722_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1722_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1761_){
_start:
{
lean_object* v___f_1762_; lean_object* v___x_1763_; 
v___f_1762_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1763_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1761_, v___f_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = l_Lean_Expr_hasMVar(v_e_1764_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_e_1764_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; lean_object* v_mctx_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___x_1774_; lean_object* v_cache_1775_; lean_object* v_zetaDeltaFVarIds_1776_; lean_object* v_postponed_1777_; lean_object* v_diag_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1787_; 
v___x_1769_ = lean_st_ref_get(v___y_1765_);
v_mctx_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc_ref(v_mctx_1770_);
lean_dec(v___x_1769_);
v___x_1771_ = l_Lean_instantiateMVarsCore(v_mctx_1770_, v_e_1764_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v___x_1771_);
v___x_1774_ = lean_st_ref_take(v___y_1765_);
v_cache_1775_ = lean_ctor_get(v___x_1774_, 1);
v_zetaDeltaFVarIds_1776_ = lean_ctor_get(v___x_1774_, 2);
v_postponed_1777_ = lean_ctor_get(v___x_1774_, 3);
v_diag_1778_ = lean_ctor_get(v___x_1774_, 4);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v___x_1774_, 0);
lean_dec(v_unused_1788_);
v___x_1780_ = v___x_1774_;
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_diag_1778_);
lean_inc(v_postponed_1777_);
lean_inc(v_zetaDeltaFVarIds_1776_);
lean_inc(v_cache_1775_);
lean_dec(v___x_1774_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_snd_1773_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_snd_1773_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_cache_1775_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_zetaDeltaFVarIds_1776_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_postponed_1777_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_diag_1778_);
v___x_1783_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_st_ref_put(v___y_1765_, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_fst_1772_);
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1789_, v___y_1790_);
lean_dec(v___y_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1793_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1807_, lean_object* v_x_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1807_, v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1814_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1814_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1831_, lean_object* v_x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1831_, v_x_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1839_, lean_object* v_mvarId_1840_, lean_object* v_x_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1840_, v_x_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_mvarId_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1848_, v_mvarId_1849_, v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_ref_1863_; lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_ref_1863_ = lean_ctor_get(v___y_1860_, 4);
v___x_1864_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_inc(v_ref_1863_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_ref_1863_);
lean_ctor_set(v___x_1869_, 1, v_a_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 1);
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
if (lean_obj_tag(v_x_1881_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = l_List_reverse___redArg(v_x_1882_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
else
{
lean_object* v_head_1890_; lean_object* v_tail_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1911_; 
v_head_1890_ = lean_ctor_get(v_x_1881_, 0);
v_tail_1891_ = lean_ctor_get(v_x_1881_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1881_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1893_ = v_x_1881_;
v_isShared_1894_ = v_isSharedCheck_1911_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_tail_1891_);
lean_inc(v_head_1890_);
lean_dec(v_x_1881_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1911_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_inc(v_head_1890_);
v___x_1895_ = l_Lean_Expr_mvar___override(v_head_1890_);
v___x_1896_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1896_, 0, v___x_1895_);
v___x_1897_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1890_, v___x_1896_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v_x_1882_);
lean_ctor_set(v___x_1893_, 0, v_a_1898_);
v___x_1900_ = v___x_1893_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1898_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_x_1882_);
v___x_1900_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
v_x_1881_ = v_tail_1891_;
v_x_1882_ = v___x_1900_;
goto _start;
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_del_object(v___x_1893_);
lean_dec(v_tail_1891_);
lean_dec(v_x_1882_);
v_a_1903_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1897_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1897_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1912_, lean_object* v_x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1912_, v_x_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1919_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1923_, lean_object* v_proc_1924_, lean_object* v_orig_1925_, lean_object* v_goals_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_box(0);
lean_inc(v_orig_1925_);
v___x_1933_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1925_, v___x_1932_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
lean_inc(v___y_1930_);
lean_inc_ref(v___y_1929_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
v___x_1935_ = lean_apply_6(v_test_1923_, v_a_1934_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, lean_box(0));
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; uint8_t v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = lean_unbox(v_a_1936_);
lean_dec(v_a_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_goals_1926_);
lean_dec(v_orig_1925_);
lean_dec_ref(v_proc_1924_);
v___x_1938_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1939_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1938_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v___x_1948_; 
lean_inc(v___y_1930_);
lean_inc_ref(v___y_1929_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
v___x_1948_ = lean_apply_7(v_proc_1924_, v_orig_1925_, v_goals_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, lean_box(0));
return v___x_1948_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_goals_1926_);
lean_dec(v_orig_1925_);
lean_dec_ref(v_proc_1924_);
v_a_1949_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1935_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1935_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_goals_1926_);
lean_dec(v_orig_1925_);
lean_dec_ref(v_proc_1924_);
lean_dec_ref(v_test_1923_);
v_a_1957_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1933_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1933_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1965_, lean_object* v_proc_1966_, lean_object* v_orig_1967_, lean_object* v_goals_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1965_, v_proc_1966_, v_orig_1967_, v_goals_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1975_, lean_object* v_test_1976_){
_start:
{
lean_object* v_toApplyRulesConfig_1977_; lean_object* v_toBacktrackConfig_1978_; uint8_t v_backtracking_1979_; uint8_t v_intro_1980_; uint8_t v_constructor_1981_; uint8_t v_suggestions_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2014_; 
v_toApplyRulesConfig_1977_ = lean_ctor_get(v_cfg_1975_, 0);
lean_inc_ref(v_toApplyRulesConfig_1977_);
v_toBacktrackConfig_1978_ = lean_ctor_get(v_toApplyRulesConfig_1977_, 0);
lean_inc_ref(v_toBacktrackConfig_1978_);
v_backtracking_1979_ = lean_ctor_get_uint8(v_cfg_1975_, sizeof(void*)*1);
v_intro_1980_ = lean_ctor_get_uint8(v_cfg_1975_, sizeof(void*)*1 + 1);
v_constructor_1981_ = lean_ctor_get_uint8(v_cfg_1975_, sizeof(void*)*1 + 2);
v_suggestions_1982_ = lean_ctor_get_uint8(v_cfg_1975_, sizeof(void*)*1 + 3);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_cfg_1975_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; 
v_unused_2015_ = lean_ctor_get(v_cfg_1975_, 0);
lean_dec(v_unused_2015_);
v___x_1984_ = v_cfg_1975_;
v_isShared_1985_ = v_isSharedCheck_2014_;
goto v_resetjp_1983_;
}
else
{
lean_dec(v_cfg_1975_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2014_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_toApplyConfig_1986_; uint8_t v_transparency_1987_; uint8_t v_symm_1988_; uint8_t v_exfalso_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2012_; 
v_toApplyConfig_1986_ = lean_ctor_get(v_toApplyRulesConfig_1977_, 1);
v_transparency_1987_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1977_, sizeof(void*)*2);
v_symm_1988_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1977_, sizeof(void*)*2 + 1);
v_exfalso_1989_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1977_, sizeof(void*)*2 + 2);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_toApplyRulesConfig_1977_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v_toApplyRulesConfig_1977_, 0);
lean_dec(v_unused_2013_);
v___x_1991_ = v_toApplyRulesConfig_1977_;
v_isShared_1992_ = v_isSharedCheck_2012_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_toApplyConfig_1986_);
lean_dec(v_toApplyRulesConfig_1977_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2012_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_maxDepth_1993_; lean_object* v_proc_1994_; lean_object* v_suspend_1995_; lean_object* v_discharge_1996_; uint8_t v_commitIndependentGoals_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2011_; 
v_maxDepth_1993_ = lean_ctor_get(v_toBacktrackConfig_1978_, 0);
v_proc_1994_ = lean_ctor_get(v_toBacktrackConfig_1978_, 1);
v_suspend_1995_ = lean_ctor_get(v_toBacktrackConfig_1978_, 2);
v_discharge_1996_ = lean_ctor_get(v_toBacktrackConfig_1978_, 3);
v_commitIndependentGoals_1997_ = lean_ctor_get_uint8(v_toBacktrackConfig_1978_, sizeof(void*)*4);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_toBacktrackConfig_1978_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1999_ = v_toBacktrackConfig_1978_;
v_isShared_2000_ = v_isSharedCheck_2011_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_discharge_1996_);
lean_inc(v_suspend_1995_);
lean_inc(v_proc_1994_);
lean_inc(v_maxDepth_1993_);
lean_dec(v_toBacktrackConfig_1978_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2011_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___f_2001_; lean_object* v___x_2003_; 
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2001_, 0, v_test_1976_);
lean_closure_set(v___f_2001_, 1, v_proc_1994_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 1, v___f_2001_);
v___x_2003_ = v___x_1999_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_maxDepth_1993_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___f_2001_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_suspend_1995_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_discharge_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*4, v_commitIndependentGoals_1997_);
v___x_2003_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2003_);
v___x_2005_ = v___x_1991_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_toApplyConfig_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*2, v_transparency_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*2 + 1, v_symm_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*2 + 2, v_exfalso_1989_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_2005_);
v___x_2007_ = v___x_1984_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*1, v_backtracking_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*1 + 1, v_intro_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*1 + 2, v_constructor_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*1 + 3, v_suggestions_1982_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2016_, lean_object* v_msg_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_msg_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2024_, v_msg_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2032_){
_start:
{
if (lean_obj_tag(v_x_2032_) == 0)
{
uint8_t v___x_2033_; 
v___x_2033_ = 0;
return v___x_2033_;
}
else
{
lean_object* v_head_2034_; lean_object* v_tail_2035_; uint8_t v___x_2036_; 
v_head_2034_ = lean_ctor_get(v_x_2032_, 0);
v_tail_2035_ = lean_ctor_get(v_x_2032_, 1);
v___x_2036_ = l_Lean_Expr_hasMVar(v_head_2034_);
if (v___x_2036_ == 0)
{
v_x_2032_ = v_tail_2035_;
goto _start;
}
else
{
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2038_){
_start:
{
uint8_t v_res_2039_; lean_object* v_r_2040_; 
v_res_2039_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2038_);
lean_dec(v_x_2038_);
v_r_2040_ = lean_box(v_res_2039_);
return v_r_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2041_, lean_object* v_sols_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2042_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
v___x_2049_ = lean_apply_6(v_test_2041_, v_sols_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, lean_box(0));
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v_sols_2042_);
lean_dec_ref(v_test_2041_);
v___x_2050_ = lean_box(v___x_2048_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2052_, lean_object* v_sols_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2052_, v_sols_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2060_, lean_object* v_test_2061_){
_start:
{
lean_object* v___f_2062_; lean_object* v___x_2063_; 
v___f_2062_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2062_, 0, v_test_2061_);
v___x_2063_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2060_, v___f_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2065_) == 0)
{
uint8_t v___x_2066_; 
lean_dec_ref(v_e_2064_);
v___x_2066_ = 0;
return v___x_2066_;
}
else
{
lean_object* v_head_2067_; lean_object* v_tail_2068_; uint8_t v___x_2069_; 
v_head_2067_ = lean_ctor_get(v_x_2065_, 0);
v_tail_2068_ = lean_ctor_get(v_x_2065_, 1);
lean_inc_ref(v_e_2064_);
v___x_2069_ = l_Lean_Expr_occurs(v_e_2064_, v_head_2067_);
if (v___x_2069_ == 0)
{
v_x_2065_ = v_tail_2068_;
goto _start;
}
else
{
lean_dec_ref(v_e_2064_);
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2071_, lean_object* v_x_2072_){
_start:
{
uint8_t v_res_2073_; lean_object* v_r_2074_; 
v_res_2073_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2071_, v_x_2072_);
lean_dec(v_x_2072_);
v_r_2074_ = lean_box(v_res_2073_);
return v_r_2074_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
uint8_t v___x_2077_; 
v___x_2077_ = 1;
return v___x_2077_;
}
else
{
lean_object* v_head_2078_; lean_object* v_tail_2079_; uint8_t v___x_2080_; 
v_head_2078_ = lean_ctor_get(v_x_2076_, 0);
lean_inc(v_head_2078_);
v_tail_2079_ = lean_ctor_get(v_x_2076_, 1);
lean_inc(v_tail_2079_);
lean_dec_ref_known(v_x_2076_, 2);
v___x_2080_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2078_, v_sols_2075_);
if (v___x_2080_ == 0)
{
lean_dec(v_tail_2079_);
return v___x_2080_;
}
else
{
v_x_2076_ = v_tail_2079_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2082_, lean_object* v_x_2083_){
_start:
{
uint8_t v_res_2084_; lean_object* v_r_2085_; 
v_res_2084_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2082_, v_x_2083_);
lean_dec(v_sols_2082_);
v_r_2085_ = lean_box(v_res_2084_);
return v_r_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2086_, lean_object* v_sols_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2087_, v_use_2086_);
v___x_2094_ = lean_box(v___x_2093_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2096_, lean_object* v_sols_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2096_, v_sols_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v_sols_2097_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2104_, lean_object* v_use_2105_){
_start:
{
lean_object* v___f_2106_; lean_object* v___x_2107_; 
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2106_, 0, v_use_2105_);
v___x_2107_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2104_, v___f_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2108_){
_start:
{
lean_object* v___y_2110_; lean_object* v_toApplyRulesConfig_2111_; uint8_t v_backtracking_2112_; uint8_t v_intro_2113_; uint8_t v_constructor_2114_; uint8_t v_suggestions_2115_; uint8_t v_intro_2119_; 
v_intro_2119_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1 + 1);
if (v_intro_2119_ == 0)
{
lean_object* v_toApplyRulesConfig_2120_; uint8_t v_backtracking_2121_; uint8_t v_constructor_2122_; uint8_t v_suggestions_2123_; 
v_toApplyRulesConfig_2120_ = lean_ctor_get(v_cfg_2108_, 0);
lean_inc_ref(v_toApplyRulesConfig_2120_);
v_backtracking_2121_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1);
v_constructor_2122_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1 + 2);
v_suggestions_2123_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1 + 3);
v___y_2110_ = v_cfg_2108_;
v_toApplyRulesConfig_2111_ = v_toApplyRulesConfig_2120_;
v_backtracking_2112_ = v_backtracking_2121_;
v_intro_2113_ = v_intro_2119_;
v_constructor_2114_ = v_constructor_2122_;
v_suggestions_2115_ = v_suggestions_2123_;
goto v___jp_2109_;
}
else
{
lean_object* v_toApplyRulesConfig_2124_; uint8_t v_backtracking_2125_; uint8_t v_constructor_2126_; uint8_t v_suggestions_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2141_; 
v_toApplyRulesConfig_2124_ = lean_ctor_get(v_cfg_2108_, 0);
v_backtracking_2125_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1);
v_constructor_2126_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1 + 2);
v_suggestions_2127_ = lean_ctor_get_uint8(v_cfg_2108_, sizeof(void*)*1 + 3);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_cfg_2108_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2129_ = v_cfg_2108_;
v_isShared_2130_ = v_isSharedCheck_2141_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_toApplyRulesConfig_2124_);
lean_dec(v_cfg_2108_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2141_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
uint8_t v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = 0;
if (v_isShared_2130_ == 0)
{
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_toApplyRulesConfig_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2140_, sizeof(void*)*1, v_backtracking_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2140_, sizeof(void*)*1 + 2, v_constructor_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2140_, sizeof(void*)*1 + 3, v_suggestions_2127_);
v___x_2133_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v_toApplyRulesConfig_2135_; uint8_t v_backtracking_2136_; uint8_t v_intro_2137_; uint8_t v_constructor_2138_; uint8_t v_suggestions_2139_; 
lean_ctor_set_uint8(v___x_2133_, sizeof(void*)*1 + 1, v___x_2131_);
v___x_2134_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2133_);
v_toApplyRulesConfig_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc_ref(v_toApplyRulesConfig_2135_);
v_backtracking_2136_ = lean_ctor_get_uint8(v___x_2134_, sizeof(void*)*1);
v_intro_2137_ = lean_ctor_get_uint8(v___x_2134_, sizeof(void*)*1 + 1);
v_constructor_2138_ = lean_ctor_get_uint8(v___x_2134_, sizeof(void*)*1 + 2);
v_suggestions_2139_ = lean_ctor_get_uint8(v___x_2134_, sizeof(void*)*1 + 3);
v___y_2110_ = v___x_2134_;
v_toApplyRulesConfig_2111_ = v_toApplyRulesConfig_2135_;
v_backtracking_2112_ = v_backtracking_2136_;
v_intro_2113_ = v_intro_2137_;
v_constructor_2114_ = v_constructor_2138_;
v_suggestions_2115_ = v_suggestions_2139_;
goto v___jp_2109_;
}
}
}
v___jp_2109_:
{
if (v_constructor_2114_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2111_);
return v___y_2110_;
}
else
{
uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v___y_2110_);
v___x_2116_ = 0;
v___x_2117_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2117_, 0, v_toApplyRulesConfig_2111_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1, v_backtracking_2112_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1 + 1, v_intro_2113_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1 + 2, v___x_2116_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1 + 3, v_suggestions_2115_);
v___x_2118_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2117_);
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2142_, lean_object* v_x_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
if (lean_obj_tag(v_x_2142_) == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = l_List_reverse___redArg(v_x_2143_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
else
{
lean_object* v_head_2153_; lean_object* v_tail_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2172_; 
v_head_2153_ = lean_ctor_get(v_x_2142_, 0);
v_tail_2154_ = lean_ctor_get(v_x_2142_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2142_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2156_ = v_x_2142_;
v_isShared_2157_ = v_isSharedCheck_2172_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_tail_2154_);
lean_inc(v_head_2153_);
lean_dec(v_x_2142_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2172_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; 
lean_inc(v___y_2149_);
lean_inc_ref(v___y_2148_);
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
lean_inc(v___y_2145_);
lean_inc_ref(v___y_2144_);
v___x_2158_ = lean_apply_7(v_head_2153_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, lean_box(0));
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v_x_2143_);
lean_ctor_set(v___x_2156_, 0, v_a_2159_);
v___x_2161_ = v___x_2156_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2159_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_x_2143_);
v___x_2161_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
v_x_2142_ = v_tail_2154_;
v_x_2143_ = v___x_2161_;
goto _start;
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_del_object(v___x_2156_);
lean_dec(v_tail_2154_);
lean_dec(v_x_2143_);
v_a_2164_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2158_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2158_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2173_, v_x_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2183_, lean_object* v_cfg_2184_, lean_object* v_lemmas_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
v___x_2193_ = lean_apply_8(v_ctx_2183_, v_cfg_2184_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, lean_box(0));
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v___x_2195_ = lean_box(0);
v___x_2196_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2185_, v___x_2195_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2205_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = l_List_appendTR___redArg(v_a_2194_, v_a_2197_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_dec(v_a_2194_);
return v___x_2196_;
}
}
else
{
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v_lemmas_2185_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2206_, lean_object* v_cfg_2207_, lean_object* v_lemmas_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2206_, v_cfg_2207_, v_lemmas_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = 0;
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2219_){
_start:
{
uint8_t v_res_2220_; lean_object* v_r_2221_; 
v_res_2220_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2219_);
lean_dec(v_x_2219_);
v_r_2221_ = lean_box(v_res_2220_);
return v_r_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2222_, lean_object* v___x_2223_, lean_object* v___x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2222_, v___x_2223_, v___x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2239_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2239_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2239_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v_fst_2235_; lean_object* v___x_2237_; 
v_fst_2235_ = lean_ctor_get(v_a_2231_, 0);
lean_inc(v_fst_2235_);
lean_dec(v_a_2231_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v_fst_2235_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_fst_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_a_2240_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2230_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2230_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2248_, lean_object* v___x_2249_, lean_object* v___x_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2248_, v___x_2249_, v___x_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2271_, lean_object* v_g_2272_, lean_object* v_lemmas_2273_, lean_object* v_ctx_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___f_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; 
v___f_2280_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2280_, 0, v_ctx_2274_);
lean_closure_set(v___f_2280_, 1, v_cfg_2271_);
lean_closure_set(v___f_2280_, 2, v_lemmas_2273_);
v___x_2281_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2282_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2283_, 0, v___f_2280_);
lean_closure_set(v___f_2283_, 1, v___x_2281_);
lean_closure_set(v___f_2283_, 2, v___x_2282_);
v___x_2284_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2272_, v___f_2283_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2285_, lean_object* v_g_2286_, lean_object* v_lemmas_2287_, lean_object* v_ctx_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2285_, v_g_2286_, v_lemmas_2287_, v_ctx_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2295_, lean_object* v_lemmas_2296_, lean_object* v_ctx_2297_, lean_object* v_g_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
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
v___x_2309_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2307_, v_transparency_2308_, v_a_2306_, v_g_2298_, v_a_2300_, v_a_2302_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2318_, lean_object* v_lemmas_2319_, lean_object* v_ctx_2320_, lean_object* v_g_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2318_, v_lemmas_2319_, v_ctx_2320_, v_g_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2328_, lean_object* v_lemmas_2329_, lean_object* v_ctx_2330_, lean_object* v_g_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; 
lean_inc(v_g_2331_);
lean_inc_ref(v_cfg_2328_);
v___x_2337_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2328_, v_g_2331_, v_lemmas_2329_, v_ctx_2330_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_toApplyRulesConfig_2338_; lean_object* v_a_2339_; lean_object* v_toApplyConfig_2340_; uint8_t v_transparency_2341_; lean_object* v___x_2342_; 
v_toApplyRulesConfig_2338_ = lean_ctor_get(v_cfg_2328_, 0);
lean_inc_ref(v_toApplyRulesConfig_2338_);
lean_dec_ref(v_cfg_2328_);
v_a_2339_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2337_, 1);
v_toApplyConfig_2340_ = lean_ctor_get(v_toApplyRulesConfig_2338_, 1);
lean_inc_ref(v_toApplyConfig_2340_);
v_transparency_2341_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2338_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2338_);
v___x_2342_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2340_, v_transparency_2341_, v_a_2339_, v_g_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2342_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_g_2331_);
lean_dec_ref(v_cfg_2328_);
v_a_2343_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2337_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2337_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2351_, lean_object* v_lemmas_2352_, lean_object* v_ctx_2353_, lean_object* v_g_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2351_, v_lemmas_2352_, v_ctx_2353_, v_g_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2361_, lean_object* v_i_2362_, lean_object* v_k_2363_){
_start:
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = lean_array_get_size(v_keys_2361_);
v___x_2365_ = lean_nat_dec_lt(v_i_2362_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_dec(v_i_2362_);
return v___x_2365_;
}
else
{
lean_object* v_k_x27_2366_; uint8_t v___x_2367_; 
v_k_x27_2366_ = lean_array_fget_borrowed(v_keys_2361_, v_i_2362_);
v___x_2367_ = l_Lean_instBEqMVarId_beq(v_k_2363_, v_k_x27_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_add(v_i_2362_, v___x_2368_);
lean_dec(v_i_2362_);
v_i_2362_ = v___x_2369_;
goto _start;
}
else
{
lean_dec(v_i_2362_);
return v___x_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2371_, lean_object* v_i_2372_, lean_object* v_k_2373_){
_start:
{
uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_res_2374_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2371_, v_i_2372_, v_k_2373_);
lean_dec(v_k_2373_);
lean_dec_ref(v_keys_2371_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2376_, size_t v_x_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 0)
{
lean_object* v_es_2379_; lean_object* v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; lean_object* v_j_2383_; lean_object* v___x_2384_; 
v_es_2379_ = lean_ctor_get(v_x_2376_, 0);
v___x_2380_ = lean_box(2);
v___x_2381_ = ((size_t)31ULL);
v___x_2382_ = lean_usize_land(v_x_2377_, v___x_2381_);
v_j_2383_ = lean_usize_to_nat(v___x_2382_);
v___x_2384_ = lean_array_get_borrowed(v___x_2380_, v_es_2379_, v_j_2383_);
lean_dec(v_j_2383_);
switch(lean_obj_tag(v___x_2384_))
{
case 0:
{
lean_object* v_key_2385_; uint8_t v___x_2386_; 
v_key_2385_ = lean_ctor_get(v___x_2384_, 0);
v___x_2386_ = l_Lean_instBEqMVarId_beq(v_x_2378_, v_key_2385_);
return v___x_2386_;
}
case 1:
{
lean_object* v_node_2387_; size_t v___x_2388_; size_t v___x_2389_; 
v_node_2387_ = lean_ctor_get(v___x_2384_, 0);
v___x_2388_ = ((size_t)5ULL);
v___x_2389_ = lean_usize_shift_right(v_x_2377_, v___x_2388_);
v_x_2376_ = v_node_2387_;
v_x_2377_ = v___x_2389_;
goto _start;
}
default: 
{
uint8_t v___x_2391_; 
v___x_2391_ = 0;
return v___x_2391_;
}
}
}
else
{
lean_object* v_ks_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v_ks_2392_ = lean_ctor_get(v_x_2376_, 0);
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2394_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2392_, v___x_2393_, v_x_2378_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_){
_start:
{
size_t v_x_1986__boxed_2398_; uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_x_1986__boxed_2398_ = lean_unbox_usize(v_x_2396_);
lean_dec(v_x_2396_);
v_res_2399_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2395_, v_x_1986__boxed_2398_, v_x_2397_);
lean_dec(v_x_2397_);
lean_dec_ref(v_x_2395_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
uint64_t v___x_2403_; size_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = l_Lean_instHashableMVarId_hash(v_x_2402_);
v___x_2404_ = lean_uint64_to_usize(v___x_2403_);
v___x_2405_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2401_, v___x_2404_, v_x_2402_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2406_, v_x_2407_);
lean_dec(v_x_2407_);
lean_dec_ref(v_x_2406_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_mctx_2414_; lean_object* v_eAssignment_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2413_ = lean_st_ref_get(v___y_2411_);
v_mctx_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_mctx_2414_);
lean_dec(v___x_2413_);
v_eAssignment_2415_ = lean_ctor_get(v_mctx_2414_, 8);
lean_inc_ref(v_eAssignment_2415_);
lean_dec_ref(v_mctx_2414_);
v___x_2416_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2415_, v_mvarId_2410_);
lean_dec_ref(v_eAssignment_2415_);
v___x_2417_ = lean_box(v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec(v_mvarId_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2423_, lean_object* v_x_2424_){
_start:
{
if (lean_obj_tag(v_x_2424_) == 0)
{
return v_x_2423_;
}
else
{
lean_object* v_head_2425_; lean_object* v_tail_2426_; lean_object* v___x_2427_; 
v_head_2425_ = lean_ctor_get(v_x_2424_, 0);
lean_inc(v_head_2425_);
v_tail_2426_ = lean_ctor_get(v_x_2424_, 1);
lean_inc(v_tail_2426_);
lean_dec_ref_known(v_x_2424_, 2);
v___x_2427_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2423_, v_head_2425_);
v_x_2423_ = v___x_2427_;
v_x_2424_ = v_tail_2426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2429_, lean_object* v_a_2430_, uint8_t v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
if (lean_obj_tag(v_a_2432_) == 0)
{
if (lean_obj_tag(v_a_2433_) == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v_a_2430_);
lean_dec_ref(v_f_2429_);
v___x_2440_ = lean_box(v_a_2431_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v_a_2434_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
else
{
lean_object* v_head_2443_; lean_object* v_tail_2444_; 
v_head_2443_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_head_2443_);
v_tail_2444_ = lean_ctor_get(v_a_2433_, 1);
lean_inc(v_tail_2444_);
lean_dec_ref_known(v_a_2433_, 2);
v_a_2432_ = v_head_2443_;
v_a_2433_ = v_tail_2444_;
goto _start;
}
}
else
{
lean_object* v_head_2446_; lean_object* v_tail_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2490_; 
v_head_2446_ = lean_ctor_get(v_a_2432_, 0);
v_tail_2447_ = lean_ctor_get(v_a_2432_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_a_2432_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2449_ = v_a_2432_;
v_isShared_2450_ = v_isSharedCheck_2490_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_tail_2447_);
lean_inc(v_head_2446_);
lean_dec(v_a_2432_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2490_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2489_; 
v___x_2451_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2446_, v___y_2436_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2489_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2489_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_unbox(v_a_2452_);
lean_dec(v_a_2452_);
if (v___x_2456_ == 0)
{
lean_object* v_zero_2457_; uint8_t v_isZero_2458_; 
v_zero_2457_ = lean_unsigned_to_nat(0u);
v_isZero_2458_ = lean_nat_dec_eq(v_a_2430_, v_zero_2457_);
if (v_isZero_2458_ == 1)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_del_object(v___x_2449_);
lean_dec(v_a_2430_);
lean_dec_ref(v_f_2429_);
v___x_2459_ = lean_array_push(v_a_2434_, v_head_2446_);
v___x_2460_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2459_, v_tail_2447_);
v___x_2461_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2460_, v_a_2433_);
v___x_2462_ = lean_box(v_a_2431_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___x_2461_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2463_);
v___x_2465_ = v___x_2454_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_del_object(v___x_2454_);
lean_inc_ref(v_f_2429_);
lean_inc(v_head_2446_);
v___x_2467_ = lean_apply_1(v_f_2429_, v_head_2446_);
v___x_2468_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2467_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v_one_2470_; lean_object* v_n_2471_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v_one_2470_ = lean_unsigned_to_nat(1u);
v_n_2471_ = lean_nat_sub(v_a_2430_, v_one_2470_);
lean_dec(v_a_2430_);
if (lean_obj_tag(v_a_2469_) == 0)
{
lean_object* v___x_2472_; 
lean_del_object(v___x_2449_);
v___x_2472_ = lean_array_push(v_a_2434_, v_head_2446_);
v_a_2430_ = v_n_2471_;
v_a_2432_ = v_tail_2447_;
v_a_2434_ = v___x_2472_;
goto _start;
}
else
{
lean_object* v_val_2474_; uint8_t v___x_2475_; lean_object* v___x_2477_; 
lean_dec(v_head_2446_);
v_val_2474_ = lean_ctor_get(v_a_2469_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v_a_2469_, 1);
v___x_2475_ = 1;
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_a_2433_);
lean_ctor_set(v___x_2449_, 0, v_tail_2447_);
v___x_2477_ = v___x_2449_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_tail_2447_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_a_2433_);
v___x_2477_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
v_a_2430_ = v_n_2471_;
v_a_2431_ = v___x_2475_;
v_a_2432_ = v_val_2474_;
v_a_2433_ = v___x_2477_;
goto _start;
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_del_object(v___x_2449_);
lean_dec(v_tail_2447_);
lean_dec(v_head_2446_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec(v_a_2430_);
lean_dec_ref(v_f_2429_);
v_a_2480_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2468_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2468_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
else
{
lean_del_object(v___x_2454_);
lean_del_object(v___x_2449_);
lean_dec(v_head_2446_);
v_a_2432_ = v_tail_2447_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_a_2065__boxed_2502_; lean_object* v_res_2503_; 
v_a_2065__boxed_2502_ = lean_unbox(v_a_2493_);
v_res_2503_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2491_, v_a_2492_, v_a_2065__boxed_2502_, v_a_2494_, v_a_2495_, v_a_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2504_, size_t v_i_2505_, size_t v_stop_2506_, lean_object* v_b_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_a_2514_; uint8_t v___x_2518_; 
v___x_2518_ = lean_usize_dec_eq(v_i_2505_, v_stop_2506_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2522_; 
v___x_2519_ = lean_array_uget_borrowed(v_as_2504_, v_i_2505_);
v___x_2522_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2519_, v___y_2509_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; uint8_t v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
v___x_2524_ = lean_unbox(v_a_2523_);
lean_dec(v_a_2523_);
if (v___x_2524_ == 0)
{
goto v___jp_2520_;
}
else
{
v_a_2514_ = v_b_2507_;
goto v___jp_2513_;
}
}
else
{
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2525_; uint8_t v___x_2526_; 
v_a_2525_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2522_, 1);
v___x_2526_ = lean_unbox(v_a_2525_);
lean_dec(v_a_2525_);
if (v___x_2526_ == 0)
{
v_a_2514_ = v_b_2507_;
goto v___jp_2513_;
}
else
{
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v_b_2507_);
v_a_2527_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2522_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2522_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
v___jp_2520_:
{
lean_object* v___x_2521_; 
lean_inc(v___x_2519_);
v___x_2521_ = lean_array_push(v_b_2507_, v___x_2519_);
v_a_2514_ = v___x_2521_;
goto v___jp_2513_;
}
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_b_2507_);
return v___x_2535_;
}
v___jp_2513_:
{
size_t v___x_2515_; size_t v___x_2516_; 
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2505_, v___x_2515_);
v_i_2505_ = v___x_2516_;
v_b_2507_ = v_a_2514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2536_, lean_object* v_i_2537_, lean_object* v_stop_2538_, lean_object* v_b_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
size_t v_i_boxed_2545_; size_t v_stop_boxed_2546_; lean_object* v_res_2547_; 
v_i_boxed_2545_ = lean_unbox_usize(v_i_2537_);
lean_dec(v_i_2537_);
v_stop_boxed_2546_ = lean_unbox_usize(v_stop_2538_);
lean_dec(v_stop_2538_);
v_res_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2536_, v_i_boxed_2545_, v_stop_boxed_2546_, v_b_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec_ref(v_as_2536_);
return v_res_2547_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2551_ = lean_array_to_list(v___x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2552_, lean_object* v_goals_2553_, lean_object* v_maxIters_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2560_ = 0;
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2564_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2552_, v_maxIters_2554_, v___x_2560_, v_goals_2553_, v___x_2561_, v___x_2563_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2607_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2607_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2607_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_fst_2569_; lean_object* v_snd_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2606_; 
v_fst_2569_ = lean_ctor_get(v_a_2565_, 0);
v_snd_2570_ = lean_ctor_get(v_a_2565_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_a_2565_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2572_ = v_a_2565_;
v_isShared_2573_ = v_isSharedCheck_2606_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snd_2570_);
lean_inc(v_fst_2569_);
lean_dec(v_a_2565_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2606_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2574_ = lean_array_get_size(v_snd_2570_);
v___x_2575_ = lean_nat_dec_lt(v___x_2562_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_dec(v_snd_2570_);
v___x_2576_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 1, v___x_2576_);
v___x_2578_ = v___x_2572_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_fst_2569_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2578_);
v___x_2580_ = v___x_2567_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
lean_del_object(v___x_2567_);
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2574_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2570_, v___x_2583_, v___x_2584_, v___x_2563_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v_snd_2570_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2597_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2597_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2597_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = lean_array_to_list(v_a_2586_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 1, v___x_2590_);
v___x_2592_ = v___x_2572_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_fst_2569_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2592_);
v___x_2594_ = v___x_2588_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2572_);
lean_dec(v_fst_2569_);
v_a_2598_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2585_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2585_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2608_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2564_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2564_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2616_, lean_object* v_goals_2617_, lean_object* v_maxIters_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2616_, v_goals_2617_, v_maxIters_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2628_, lean_object* v_goals_2629_, lean_object* v_maxIters_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2628_, v_goals_2629_, v_maxIters_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2649_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2649_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2649_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_fst_2641_; uint8_t v___x_2642_; 
v_fst_2641_ = lean_ctor_get(v_a_2637_, 0);
v___x_2642_ = lean_unbox(v_fst_2641_);
if (v___x_2642_ == 1)
{
lean_object* v_snd_2643_; lean_object* v___x_2645_; 
v_snd_2643_ = lean_ctor_get(v_a_2637_, 1);
lean_inc(v_snd_2643_);
lean_dec(v_a_2637_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_snd_2643_);
v___x_2645_ = v___x_2639_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_snd_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_del_object(v___x_2639_);
lean_dec(v_a_2637_);
v___x_2647_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2648_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2647_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2636_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2636_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2658_, lean_object* v_goals_2659_, lean_object* v_maxIters_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2658_, v_goals_2659_, v_maxIters_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2667_, lean_object* v_ctx_2668_, lean_object* v_cfg_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
uint8_t v_backtracking_2676_; 
v_backtracking_2676_ = lean_ctor_get_uint8(v_cfg_2669_, sizeof(void*)*1);
if (v_backtracking_2676_ == 0)
{
lean_object* v_toApplyRulesConfig_2677_; lean_object* v_toBacktrackConfig_2678_; lean_object* v_maxDepth_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_toApplyRulesConfig_2677_ = lean_ctor_get(v_cfg_2669_, 0);
v_toBacktrackConfig_2678_ = lean_ctor_get(v_toApplyRulesConfig_2677_, 0);
v_maxDepth_2679_ = lean_ctor_get(v_toBacktrackConfig_2678_, 0);
lean_inc(v_maxDepth_2679_);
v___x_2680_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2680_, 0, v_cfg_2669_);
lean_closure_set(v___x_2680_, 1, v_lemmas_2667_);
lean_closure_set(v___x_2680_, 2, v_ctx_2668_);
v___x_2681_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2680_, v_a_2670_, v_maxDepth_2679_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
return v___x_2681_;
}
else
{
lean_object* v_toApplyRulesConfig_2682_; lean_object* v_toBacktrackConfig_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_toApplyRulesConfig_2682_ = lean_ctor_get(v_cfg_2669_, 0);
v_toBacktrackConfig_2683_ = lean_ctor_get(v_toApplyRulesConfig_2682_, 0);
lean_inc_ref(v_toBacktrackConfig_2683_);
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2685_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2685_, 0, v_cfg_2669_);
lean_closure_set(v___x_2685_, 1, v_lemmas_2667_);
lean_closure_set(v___x_2685_, 2, v_ctx_2668_);
v___x_2686_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2683_, v___x_2684_, v___x_2685_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2687_, lean_object* v_ctx_2688_, lean_object* v_cfg_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2687_, v_ctx_2688_, v_cfg_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2697_, v___y_2699_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v_mvarId_2704_);
return v_res_2710_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2711_, lean_object* v_x_2712_, lean_object* v_x_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2712_, v_x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
uint8_t v_res_2718_; lean_object* v_r_2719_; 
v_res_2718_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2715_, v_x_2716_, v_x_2717_);
lean_dec(v_x_2717_);
lean_dec_ref(v_x_2716_);
v_r_2719_ = lean_box(v_res_2718_);
return v_r_2719_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2720_, lean_object* v_x_2721_, size_t v_x_2722_, lean_object* v_x_2723_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2721_, v_x_2722_, v_x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2725_, lean_object* v_x_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_){
_start:
{
size_t v_x_2511__boxed_2729_; uint8_t v_res_2730_; lean_object* v_r_2731_; 
v_x_2511__boxed_2729_ = lean_unbox_usize(v_x_2727_);
lean_dec(v_x_2727_);
v_res_2730_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2725_, v_x_2726_, v_x_2511__boxed_2729_, v_x_2728_);
lean_dec(v_x_2728_);
lean_dec_ref(v_x_2726_);
v_r_2731_ = lean_box(v_res_2730_);
return v_r_2731_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2732_, lean_object* v_keys_2733_, lean_object* v_vals_2734_, lean_object* v_heq_2735_, lean_object* v_i_2736_, lean_object* v_k_2737_){
_start:
{
uint8_t v___x_2738_; 
v___x_2738_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2733_, v_i_2736_, v_k_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2739_, lean_object* v_keys_2740_, lean_object* v_vals_2741_, lean_object* v_heq_2742_, lean_object* v_i_2743_, lean_object* v_k_2744_){
_start:
{
uint8_t v_res_2745_; lean_object* v_r_2746_; 
v_res_2745_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2739_, v_keys_2740_, v_vals_2741_, v_heq_2742_, v_i_2743_, v_k_2744_);
lean_dec(v_k_2744_);
lean_dec_ref(v_vals_2741_);
lean_dec_ref(v_keys_2740_);
v_r_2746_ = lean_box(v_res_2745_);
return v_r_2746_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v_x_2758_);
return v_res_2764_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2767_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2768_ = l_Lean_Name_append(v___x_2767_, v___x_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2769_, lean_object* v_lemmas_2770_, lean_object* v_ctx_2771_, lean_object* v_goals_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_cfg_2778_; lean_object* v___x_2779_; 
v_cfg_2778_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2769_);
lean_inc(v_goals_2772_);
lean_inc_ref(v_cfg_2778_);
lean_inc_ref(v_ctx_2771_);
lean_inc(v_lemmas_2770_);
v___x_2779_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2770_, v_ctx_2771_, v_cfg_2778_, v_goals_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_dec_ref(v_cfg_2778_);
lean_dec(v_goals_2772_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
return v___x_2779_;
}
else
{
lean_object* v_a_2780_; lean_object* v___f_2781_; uint8_t v___y_2783_; lean_object* v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_a_2790_; uint8_t v___y_2803_; lean_object* v___y_2804_; uint8_t v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v_a_2810_; uint8_t v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v_a_2820_; uint8_t v___y_2830_; lean_object* v___y_2831_; uint8_t v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v_a_2837_; uint8_t v___y_2840_; lean_object* v___y_2841_; uint8_t v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; uint8_t v___y_2882_; uint8_t v___x_2936_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
v___f_2781_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_2936_ = l_Lean_Exception_isInterrupt(v_a_2780_);
if (v___x_2936_ == 0)
{
uint8_t v___x_2937_; 
v___x_2937_ = l_Lean_Exception_isRuntime(v_a_2780_);
v___y_2882_ = v___x_2937_;
goto v___jp_2881_;
}
else
{
lean_dec(v_a_2780_);
v___y_2882_ = v___x_2936_;
goto v___jp_2881_;
}
v___jp_2782_:
{
lean_object* v___x_2791_; double v___x_2792_; double v___x_2793_; double v___x_2794_; double v___x_2795_; double v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2791_ = lean_io_mono_nanos_now();
v___x_2792_ = lean_float_of_nat(v___y_2787_);
v___x_2793_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2794_ = lean_float_div(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_float_of_nat(v___x_2791_);
v___x_2796_ = lean_float_div(v___x_2795_, v___x_2793_);
v___x_2797_ = lean_box_float(v___x_2794_);
v___x_2798_ = lean_box_float(v___x_2796_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_a_2790_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2789_);
v___x_2801_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2789_, v___y_2785_, v___y_2786_, v___y_2784_, v___y_2783_, v___y_2788_, v___f_2781_, v___x_2800_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
return v___x_2801_;
}
v___jp_2802_:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2810_);
v___y_2783_ = v___y_2803_;
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v___y_2807_;
v___y_2788_ = v___y_2808_;
v___y_2789_ = v___y_2809_;
v_a_2790_ = v___x_2811_;
goto v___jp_2782_;
}
v___jp_2812_:
{
lean_object* v___x_2821_; double v___x_2822_; double v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2821_ = lean_io_get_num_heartbeats();
v___x_2822_ = lean_float_of_nat(v___y_2817_);
v___x_2823_ = lean_float_of_nat(v___x_2821_);
v___x_2824_ = lean_box_float(v___x_2822_);
v___x_2825_ = lean_box_float(v___x_2823_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2820_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
lean_inc_ref(v___y_2816_);
lean_inc(v___y_2819_);
v___x_2828_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2819_, v___y_2815_, v___y_2816_, v___y_2814_, v___y_2813_, v___y_2818_, v___f_2781_, v___x_2827_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
return v___x_2828_;
}
v___jp_2829_:
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2837_);
v___y_2813_ = v___y_2830_;
v___y_2814_ = v___y_2831_;
v___y_2815_ = v___y_2832_;
v___y_2816_ = v___y_2833_;
v___y_2817_ = v___y_2834_;
v___y_2818_ = v___y_2835_;
v___y_2819_ = v___y_2836_;
v_a_2820_ = v___x_2838_;
goto v___jp_2812_;
}
v___jp_2839_:
{
lean_object* v___x_2847_; lean_object* v_a_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2847_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2776_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2850_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2841_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_io_mono_nanos_now();
v___x_2852_ = l_Lean_MVarId_exfalso(v___y_2845_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_a_2853_);
lean_ctor_set(v___x_2854_, 1, v___y_2844_);
v___x_2855_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2770_, v_ctx_2771_, v_cfg_2778_, v___x_2854_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set_tag(v___x_2858_, 1);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
v___y_2783_ = v___y_2840_;
v___y_2784_ = v___y_2841_;
v___y_2785_ = v___y_2842_;
v___y_2786_ = v___y_2843_;
v___y_2787_ = v___x_2851_;
v___y_2788_ = v_a_2848_;
v___y_2789_ = v___y_2846_;
v_a_2790_ = v___x_2861_;
goto v___jp_2782_;
}
}
}
else
{
lean_object* v_a_2864_; 
v_a_2864_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2855_, 1);
v___y_2803_ = v___y_2840_;
v___y_2804_ = v___y_2841_;
v___y_2805_ = v___y_2842_;
v___y_2806_ = v___y_2843_;
v___y_2807_ = v___x_2851_;
v___y_2808_ = v_a_2848_;
v___y_2809_ = v___y_2846_;
v_a_2810_ = v_a_2864_;
goto v___jp_2802_;
}
}
else
{
lean_object* v_a_2865_; 
lean_dec(v___y_2844_);
lean_dec_ref(v_cfg_2778_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
v_a_2865_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2852_, 1);
v___y_2803_ = v___y_2840_;
v___y_2804_ = v___y_2841_;
v___y_2805_ = v___y_2842_;
v___y_2806_ = v___y_2843_;
v___y_2807_ = v___x_2851_;
v___y_2808_ = v_a_2848_;
v___y_2809_ = v___y_2846_;
v_a_2810_ = v_a_2865_;
goto v___jp_2802_;
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_io_get_num_heartbeats();
v___x_2867_ = l_Lean_MVarId_exfalso(v___y_2845_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2869_, 0, v_a_2868_);
lean_ctor_set(v___x_2869_, 1, v___y_2844_);
v___x_2870_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2770_, v_ctx_2771_, v_cfg_2778_, v___x_2869_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set_tag(v___x_2873_, 1);
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
v___y_2813_ = v___y_2840_;
v___y_2814_ = v___y_2841_;
v___y_2815_ = v___y_2842_;
v___y_2816_ = v___y_2843_;
v___y_2817_ = v___x_2866_;
v___y_2818_ = v_a_2848_;
v___y_2819_ = v___y_2846_;
v_a_2820_ = v___x_2876_;
goto v___jp_2812_;
}
}
}
else
{
lean_object* v_a_2879_; 
v_a_2879_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2870_, 1);
v___y_2830_ = v___y_2840_;
v___y_2831_ = v___y_2841_;
v___y_2832_ = v___y_2842_;
v___y_2833_ = v___y_2843_;
v___y_2834_ = v___x_2866_;
v___y_2835_ = v_a_2848_;
v___y_2836_ = v___y_2846_;
v_a_2837_ = v_a_2879_;
goto v___jp_2829_;
}
}
else
{
lean_object* v_a_2880_; 
lean_dec(v___y_2844_);
lean_dec_ref(v_cfg_2778_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
v_a_2880_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2867_, 1);
v___y_2830_ = v___y_2840_;
v___y_2831_ = v___y_2841_;
v___y_2832_ = v___y_2842_;
v___y_2833_ = v___y_2843_;
v___y_2834_ = v___x_2866_;
v___y_2835_ = v_a_2848_;
v___y_2836_ = v___y_2846_;
v_a_2837_ = v_a_2880_;
goto v___jp_2829_;
}
}
}
v___jp_2881_:
{
if (v___y_2882_ == 0)
{
if (lean_obj_tag(v_goals_2772_) == 1)
{
lean_object* v_tail_2883_; 
v_tail_2883_ = lean_ctor_get(v_goals_2772_, 1);
lean_inc(v_tail_2883_);
if (lean_obj_tag(v_tail_2883_) == 0)
{
lean_object* v_toApplyRulesConfig_2884_; uint8_t v_exfalso_2885_; 
v_toApplyRulesConfig_2884_ = lean_ctor_get(v_cfg_2778_, 0);
lean_inc_ref(v_toApplyRulesConfig_2884_);
v_exfalso_2885_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2884_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2884_);
if (v_exfalso_2885_ == 1)
{
lean_object* v_options_2886_; uint8_t v_hasTrace_2887_; 
lean_dec_ref_known(v___x_2779_, 1);
v_options_2886_ = lean_ctor_get(v_a_2775_, 1);
v_hasTrace_2887_ = lean_ctor_get_uint8(v_options_2886_, sizeof(void*)*1);
if (v_hasTrace_2887_ == 0)
{
lean_object* v_head_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2906_; 
v_head_2888_ = lean_ctor_get(v_goals_2772_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_goals_2772_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v_goals_2772_, 1);
lean_dec(v_unused_2907_);
v___x_2890_ = v_goals_2772_;
v_isShared_2891_ = v_isSharedCheck_2906_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_head_2888_);
lean_dec(v_goals_2772_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2906_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_MVarId_exfalso(v_head_2888_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v_a_2893_);
v___x_2895_ = v___x_2890_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2893_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_tail_2883_);
v___x_2895_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; 
v___x_2896_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2770_, v_ctx_2771_, v_cfg_2778_, v___x_2895_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
return v___x_2896_;
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_del_object(v___x_2890_);
lean_dec_ref(v_cfg_2778_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
v_a_2898_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2892_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2892_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
else
{
lean_object* v_toCold_2908_; lean_object* v_head_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2934_; 
v_toCold_2908_ = lean_ctor_get(v_a_2775_, 0);
v_head_2909_ = lean_ctor_get(v_goals_2772_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_goals_2772_);
if (v_isSharedCheck_2934_ == 0)
{
lean_object* v_unused_2935_; 
v_unused_2935_ = lean_ctor_get(v_goals_2772_, 1);
lean_dec(v_unused_2935_);
v___x_2911_ = v_goals_2772_;
v_isShared_2912_ = v_isSharedCheck_2934_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_head_2909_);
lean_dec(v_goals_2772_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2934_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_inheritedTraceOptions_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_inheritedTraceOptions_2913_ = lean_ctor_get(v_toCold_2908_, 4);
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2915_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2916_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2913_, v_options_2886_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = l_Lean_trace_profiler;
v___x_2919_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2886_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_MVarId_exfalso(v_head_2909_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v_a_2921_);
v___x_2923_ = v___x_2911_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2921_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_tail_2883_);
v___x_2923_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; 
v___x_2924_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2770_, v_ctx_2771_, v_cfg_2778_, v___x_2923_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
return v___x_2924_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_del_object(v___x_2911_);
lean_dec_ref(v_cfg_2778_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
v_a_2926_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2920_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2920_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_del_object(v___x_2911_);
v___y_2840_ = v___x_2917_;
v___y_2841_ = v_options_2886_;
v___y_2842_ = v_exfalso_2885_;
v___y_2843_ = v___x_2915_;
v___y_2844_ = v_tail_2883_;
v___y_2845_ = v_head_2909_;
v___y_2846_ = v___x_2914_;
goto v___jp_2839_;
}
}
else
{
lean_del_object(v___x_2911_);
v___y_2840_ = v___x_2917_;
v___y_2841_ = v_options_2886_;
v___y_2842_ = v_exfalso_2885_;
v___y_2843_ = v___x_2915_;
v___y_2844_ = v_tail_2883_;
v___y_2845_ = v_head_2909_;
v___y_2846_ = v___x_2914_;
goto v___jp_2839_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2772_, 2);
lean_dec_ref(v_cfg_2778_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
return v___x_2779_;
}
}
else
{
lean_dec(v_tail_2883_);
lean_dec_ref_known(v_goals_2772_, 2);
lean_dec_ref(v_cfg_2778_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
return v___x_2779_;
}
}
else
{
lean_dec_ref(v_cfg_2778_);
lean_dec(v_goals_2772_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
return v___x_2779_;
}
}
else
{
lean_dec_ref(v_cfg_2778_);
lean_dec(v_goals_2772_);
lean_dec_ref(v_ctx_2771_);
lean_dec(v_lemmas_2770_);
return v___x_2779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2938_, lean_object* v_lemmas_2939_, lean_object* v_ctx_2940_, lean_object* v_goals_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2938_, v_lemmas_2939_, v_ctx_2940_, v_goals_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
if (lean_obj_tag(v_x_2948_) == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = l_List_reverse___redArg(v_x_2949_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
else
{
lean_object* v_head_2957_; lean_object* v_tail_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2981_; 
v_head_2957_ = lean_ctor_get(v_x_2948_, 0);
v_tail_2958_ = lean_ctor_get(v_x_2948_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2948_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2960_ = v_x_2948_;
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_tail_2958_);
lean_inc(v_head_2957_);
lean_dec(v_x_2948_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Expr_applySymm(v_head_2957_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 1, v_x_2949_);
lean_ctor_set(v___x_2960_, 0, v_a_2963_);
v___x_2965_ = v___x_2960_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2963_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_x_2949_);
v___x_2965_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
v_x_2948_ = v_tail_2958_;
v_x_2949_ = v___x_2965_;
goto _start;
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2980_; 
lean_del_object(v___x_2960_);
v_a_2968_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2970_ = v___x_2962_;
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2962_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v___y_2973_; uint8_t v___x_2978_; 
v___x_2978_ = l_Lean_Exception_isInterrupt(v_a_2968_);
if (v___x_2978_ == 0)
{
uint8_t v___x_2979_; 
lean_inc(v_a_2968_);
v___x_2979_ = l_Lean_Exception_isRuntime(v_a_2968_);
v___y_2973_ = v___x_2979_;
goto v___jp_2972_;
}
else
{
v___y_2973_ = v___x_2978_;
goto v___jp_2972_;
}
v___jp_2972_:
{
if (v___y_2973_ == 0)
{
lean_del_object(v___x_2970_);
lean_dec(v_a_2968_);
v_x_2948_ = v_tail_2958_;
goto _start;
}
else
{
lean_object* v___x_2976_; 
lean_dec(v_tail_2958_);
lean_dec(v_x_2949_);
if (v_isShared_2971_ == 0)
{
v___x_2976_ = v___x_2970_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2968_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2982_, v_x_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2990_, lean_object* v_hyps_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
if (v_symm_2990_ == 0)
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_hyps_2991_);
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_box(0);
lean_inc(v_hyps_2991_);
v___x_2999_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2991_, v___x_2998_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3008_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3008_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3008_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3004_ = l_List_appendTR___redArg(v_hyps_2991_, v_a_3000_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3004_);
v___x_3006_ = v___x_3002_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
lean_dec(v_hyps_2991_);
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3009_, lean_object* v_hyps_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
uint8_t v_symm_boxed_3016_; lean_object* v_res_3017_; 
v_symm_boxed_3016_ = lean_unbox(v_symm_3009_);
v_res_3017_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3016_, v_hyps_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3018_, size_t v_sz_3019_, size_t v_i_3020_, lean_object* v_b_3021_){
_start:
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_usize_dec_lt(v_i_3020_, v_sz_3019_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v_b_3021_);
return v___x_3024_;
}
else
{
lean_object* v_snd_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3043_; 
v_snd_3025_ = lean_ctor_get(v_b_3021_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_b_3021_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; 
v_unused_3044_ = lean_ctor_get(v_b_3021_, 0);
lean_dec(v_unused_3044_);
v___x_3027_ = v_b_3021_;
v_isShared_3028_ = v_isSharedCheck_3043_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_snd_3025_);
lean_dec(v_b_3021_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3043_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v_a_3031_; lean_object* v_a_3038_; 
v___x_3029_ = lean_box(0);
v_a_3038_ = lean_array_uget_borrowed(v_as_3018_, v_i_3020_);
if (lean_obj_tag(v_a_3038_) == 0)
{
v_a_3031_ = v_snd_3025_;
goto v___jp_3030_;
}
else
{
lean_object* v_val_3039_; uint8_t v___x_3040_; 
v_val_3039_ = lean_ctor_get(v_a_3038_, 0);
v___x_3040_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_inc(v_val_3039_);
v___x_3041_ = l_Lean_LocalDecl_toExpr(v_val_3039_);
v___x_3042_ = lean_array_push(v_snd_3025_, v___x_3041_);
v_a_3031_ = v___x_3042_;
goto v___jp_3030_;
}
else
{
v_a_3031_ = v_snd_3025_;
goto v___jp_3030_;
}
}
v___jp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v_a_3031_);
lean_ctor_set(v___x_3027_, 0, v___x_3029_);
v___x_3033_ = v___x_3027_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_a_3031_);
v___x_3033_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
size_t v___x_3034_; size_t v___x_3035_; 
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_add(v_i_3020_, v___x_3034_);
v_i_3020_ = v___x_3035_;
v_b_3021_ = v___x_3033_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3045_, lean_object* v_sz_3046_, lean_object* v_i_3047_, lean_object* v_b_3048_, lean_object* v___y_3049_){
_start:
{
size_t v_sz_boxed_3050_; size_t v_i_boxed_3051_; lean_object* v_res_3052_; 
v_sz_boxed_3050_ = lean_unbox_usize(v_sz_3046_);
lean_dec(v_sz_3046_);
v_i_boxed_3051_ = lean_unbox_usize(v_i_3047_);
lean_dec(v_i_3047_);
v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3045_, v_sz_boxed_3050_, v_i_boxed_3051_, v_b_3048_);
lean_dec_ref(v_as_3045_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3053_, size_t v_sz_3054_, size_t v_i_3055_, lean_object* v_b_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_usize_dec_lt(v_i_3055_, v_sz_3054_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_b_3056_);
return v___x_3065_;
}
else
{
lean_object* v_snd_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3084_; 
v_snd_3066_ = lean_ctor_get(v_b_3056_, 1);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_b_3056_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v_b_3056_, 0);
lean_dec(v_unused_3085_);
v___x_3068_ = v_b_3056_;
v_isShared_3069_ = v_isSharedCheck_3084_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_snd_3066_);
lean_dec(v_b_3056_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3084_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v_a_3072_; lean_object* v_a_3079_; 
v___x_3070_ = lean_box(0);
v_a_3079_ = lean_array_uget_borrowed(v_as_3053_, v_i_3055_);
if (lean_obj_tag(v_a_3079_) == 0)
{
v_a_3072_ = v_snd_3066_;
goto v___jp_3071_;
}
else
{
lean_object* v_val_3080_; uint8_t v___x_3081_; 
v_val_3080_ = lean_ctor_get(v_a_3079_, 0);
v___x_3081_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc(v_val_3080_);
v___x_3082_ = l_Lean_LocalDecl_toExpr(v_val_3080_);
v___x_3083_ = lean_array_push(v_snd_3066_, v___x_3082_);
v_a_3072_ = v___x_3083_;
goto v___jp_3071_;
}
else
{
v_a_3072_ = v_snd_3066_;
goto v___jp_3071_;
}
}
v___jp_3071_:
{
lean_object* v___x_3074_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 1, v_a_3072_);
lean_ctor_set(v___x_3068_, 0, v___x_3070_);
v___x_3074_ = v___x_3068_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_a_3072_);
v___x_3074_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((size_t)1ULL);
v___x_3076_ = lean_usize_add(v_i_3055_, v___x_3075_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3053_, v_sz_3054_, v___x_3076_, v___x_3074_);
return v___x_3077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3086_, lean_object* v_sz_3087_, lean_object* v_i_3088_, lean_object* v_b_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
size_t v_sz_boxed_3097_; size_t v_i_boxed_3098_; lean_object* v_res_3099_; 
v_sz_boxed_3097_ = lean_unbox_usize(v_sz_3087_);
lean_dec(v_sz_3087_);
v_i_boxed_3098_ = lean_unbox_usize(v_i_3088_);
lean_dec(v_i_3088_);
v_res_3099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3086_, v_sz_boxed_3097_, v_i_boxed_3098_, v_b_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v_as_3086_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3100_, size_t v_sz_3101_, size_t v_i_3102_, lean_object* v_b_3103_){
_start:
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_usize_dec_lt(v_i_3102_, v_sz_3101_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_b_3103_);
return v___x_3106_;
}
else
{
lean_object* v_snd_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3125_; 
v_snd_3107_ = lean_ctor_get(v_b_3103_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_b_3103_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_b_3103_, 0);
lean_dec(v_unused_3126_);
v___x_3109_ = v_b_3103_;
v_isShared_3110_ = v_isSharedCheck_3125_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snd_3107_);
lean_dec(v_b_3103_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3125_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v_a_3113_; lean_object* v_a_3120_; 
v___x_3111_ = lean_box(0);
v_a_3120_ = lean_array_uget_borrowed(v_as_3100_, v_i_3102_);
if (lean_obj_tag(v_a_3120_) == 0)
{
v_a_3113_ = v_snd_3107_;
goto v___jp_3112_;
}
else
{
lean_object* v_val_3121_; uint8_t v___x_3122_; 
v_val_3121_ = lean_ctor_get(v_a_3120_, 0);
v___x_3122_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_inc(v_val_3121_);
v___x_3123_ = l_Lean_LocalDecl_toExpr(v_val_3121_);
v___x_3124_ = lean_array_push(v_snd_3107_, v___x_3123_);
v_a_3113_ = v___x_3124_;
goto v___jp_3112_;
}
else
{
v_a_3113_ = v_snd_3107_;
goto v___jp_3112_;
}
}
v___jp_3112_:
{
lean_object* v___x_3115_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v_a_3113_);
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3115_ = v___x_3109_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_a_3113_);
v___x_3115_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
size_t v___x_3116_; size_t v___x_3117_; 
v___x_3116_ = ((size_t)1ULL);
v___x_3117_ = lean_usize_add(v_i_3102_, v___x_3116_);
v_i_3102_ = v___x_3117_;
v_b_3103_ = v___x_3115_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3127_, lean_object* v_sz_3128_, lean_object* v_i_3129_, lean_object* v_b_3130_, lean_object* v___y_3131_){
_start:
{
size_t v_sz_boxed_3132_; size_t v_i_boxed_3133_; lean_object* v_res_3134_; 
v_sz_boxed_3132_ = lean_unbox_usize(v_sz_3128_);
lean_dec(v_sz_3128_);
v_i_boxed_3133_ = lean_unbox_usize(v_i_3129_);
lean_dec(v_i_3129_);
v_res_3134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3127_, v_sz_boxed_3132_, v_i_boxed_3133_, v_b_3130_);
lean_dec_ref(v_as_3127_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3135_, size_t v_sz_3136_, size_t v_i_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
uint8_t v___x_3146_; 
v___x_3146_ = lean_usize_dec_lt(v_i_3137_, v_sz_3136_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_b_3138_);
return v___x_3147_;
}
else
{
lean_object* v_snd_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3166_; 
v_snd_3148_ = lean_ctor_get(v_b_3138_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_b_3138_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v_b_3138_, 0);
lean_dec(v_unused_3167_);
v___x_3150_ = v_b_3138_;
v_isShared_3151_ = v_isSharedCheck_3166_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_snd_3148_);
lean_dec(v_b_3138_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3166_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v_a_3154_; lean_object* v_a_3161_; 
v___x_3152_ = lean_box(0);
v_a_3161_ = lean_array_uget_borrowed(v_as_3135_, v_i_3137_);
if (lean_obj_tag(v_a_3161_) == 0)
{
v_a_3154_ = v_snd_3148_;
goto v___jp_3153_;
}
else
{
lean_object* v_val_3162_; uint8_t v___x_3163_; 
v_val_3162_ = lean_ctor_get(v_a_3161_, 0);
v___x_3163_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_inc(v_val_3162_);
v___x_3164_ = l_Lean_LocalDecl_toExpr(v_val_3162_);
v___x_3165_ = lean_array_push(v_snd_3148_, v___x_3164_);
v_a_3154_ = v___x_3165_;
goto v___jp_3153_;
}
else
{
v_a_3154_ = v_snd_3148_;
goto v___jp_3153_;
}
}
v___jp_3153_:
{
lean_object* v___x_3156_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v_a_3154_);
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3156_ = v___x_3150_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_a_3154_);
v___x_3156_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = ((size_t)1ULL);
v___x_3158_ = lean_usize_add(v_i_3137_, v___x_3157_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3135_, v_sz_3136_, v___x_3158_, v___x_3156_);
return v___x_3159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3168_, lean_object* v_sz_3169_, lean_object* v_i_3170_, lean_object* v_b_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
size_t v_sz_boxed_3179_; size_t v_i_boxed_3180_; lean_object* v_res_3181_; 
v_sz_boxed_3179_ = lean_unbox_usize(v_sz_3169_);
lean_dec(v_sz_3169_);
v_i_boxed_3180_ = lean_unbox_usize(v_i_3170_);
lean_dec(v_i_3170_);
v_res_3181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3168_, v_sz_boxed_3179_, v_i_boxed_3180_, v_b_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v_as_3168_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3182_, lean_object* v_n_3183_, lean_object* v_b_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
if (lean_obj_tag(v_n_3183_) == 0)
{
lean_object* v_cs_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; size_t v_sz_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
v_cs_3192_ = lean_ctor_get(v_n_3183_, 0);
v___x_3193_ = lean_box(0);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v_b_3184_);
v_sz_3195_ = lean_array_size(v_cs_3192_);
v___x_3196_ = ((size_t)0ULL);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3182_, v_cs_3192_, v_sz_3195_, v___x_3196_, v___x_3194_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3212_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3212_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3212_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_fst_3202_; 
v_fst_3202_ = lean_ctor_get(v_a_3198_, 0);
if (lean_obj_tag(v_fst_3202_) == 0)
{
lean_object* v_snd_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v_snd_3203_ = lean_ctor_get(v_a_3198_, 1);
lean_inc(v_snd_3203_);
lean_dec(v_a_3198_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_snd_3203_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3204_);
v___x_3206_ = v___x_3200_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
else
{
lean_object* v_val_3208_; lean_object* v___x_3210_; 
lean_inc_ref(v_fst_3202_);
lean_dec(v_a_3198_);
v_val_3208_ = lean_ctor_get(v_fst_3202_, 0);
lean_inc(v_val_3208_);
lean_dec_ref_known(v_fst_3202_, 1);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v_val_3208_);
v___x_3210_ = v___x_3200_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_val_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
v_a_3213_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3197_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3197_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_vs_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; size_t v_sz_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v_vs_3221_ = lean_ctor_get(v_n_3183_, 0);
v___x_3222_ = lean_box(0);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v_b_3184_);
v_sz_3224_ = lean_array_size(v_vs_3221_);
v___x_3225_ = ((size_t)0ULL);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3221_, v_sz_3224_, v___x_3225_, v___x_3223_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3241_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3241_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3241_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_fst_3231_; 
v_fst_3231_ = lean_ctor_get(v_a_3227_, 0);
if (lean_obj_tag(v_fst_3231_) == 0)
{
lean_object* v_snd_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v_snd_3232_ = lean_ctor_get(v_a_3227_, 1);
lean_inc(v_snd_3232_);
lean_dec(v_a_3227_);
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v_snd_3232_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3233_);
v___x_3235_ = v___x_3229_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
else
{
lean_object* v_val_3237_; lean_object* v___x_3239_; 
lean_inc_ref(v_fst_3231_);
lean_dec(v_a_3227_);
v_val_3237_ = lean_ctor_get(v_fst_3231_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v_fst_3231_, 1);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v_val_3237_);
v___x_3239_ = v___x_3229_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_val_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3226_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3226_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3250_, lean_object* v_as_3251_, size_t v_sz_3252_, size_t v_i_3253_, lean_object* v_b_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v_b_3254_);
return v___x_3263_;
}
else
{
lean_object* v_snd_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3298_; 
v_snd_3264_ = lean_ctor_get(v_b_3254_, 1);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_b_3254_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; 
v_unused_3299_ = lean_ctor_get(v_b_3254_, 0);
lean_dec(v_unused_3299_);
v___x_3266_ = v_b_3254_;
v_isShared_3267_ = v_isSharedCheck_3298_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_snd_3264_);
lean_dec(v_b_3254_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3298_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_a_3268_; lean_object* v___x_3269_; 
v_a_3268_ = lean_array_uget_borrowed(v_as_3251_, v_i_3253_);
lean_inc(v_snd_3264_);
v___x_3269_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3250_, v_a_3268_, v_snd_3264_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3289_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3289_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3289_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
if (lean_obj_tag(v_a_3270_) == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_a_3270_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3274_);
v___x_3276_ = v___x_3266_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_snd_3264_);
v___x_3276_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3278_; 
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3276_);
v___x_3278_ = v___x_3272_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
lean_del_object(v___x_3272_);
lean_dec(v_snd_3264_);
v_a_3281_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v_a_3270_, 1);
v___x_3282_ = lean_box(0);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 1, v_a_3281_);
lean_ctor_set(v___x_3266_, 0, v___x_3282_);
v___x_3284_ = v___x_3266_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_a_3281_);
v___x_3284_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
size_t v___x_3285_; size_t v___x_3286_; 
v___x_3285_ = ((size_t)1ULL);
v___x_3286_ = lean_usize_add(v_i_3253_, v___x_3285_);
v_i_3253_ = v___x_3286_;
v_b_3254_ = v___x_3284_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_del_object(v___x_3266_);
lean_dec(v_snd_3264_);
v_a_3290_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3269_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3269_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3300_, lean_object* v_as_3301_, lean_object* v_sz_3302_, lean_object* v_i_3303_, lean_object* v_b_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
size_t v_sz_boxed_3312_; size_t v_i_boxed_3313_; lean_object* v_res_3314_; 
v_sz_boxed_3312_ = lean_unbox_usize(v_sz_3302_);
lean_dec(v_sz_3302_);
v_i_boxed_3313_ = lean_unbox_usize(v_i_3303_);
lean_dec(v_i_3303_);
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3300_, v_as_3301_, v_sz_boxed_3312_, v_i_boxed_3313_, v_b_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v_as_3301_);
lean_dec_ref(v_init_3300_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3315_, lean_object* v_n_3316_, lean_object* v_b_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3315_, v_n_3316_, v_b_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_n_3316_);
lean_dec_ref(v_init_3315_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3326_, lean_object* v_init_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_root_3335_; lean_object* v_tail_3336_; lean_object* v___x_3337_; 
v_root_3335_ = lean_ctor_get(v_t_3326_, 0);
v_tail_3336_ = lean_ctor_get(v_t_3326_, 1);
lean_inc_ref(v_init_3327_);
v___x_3337_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3327_, v_root_3335_, v_init_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec_ref(v_init_3327_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3374_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3374_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3374_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_a_3338_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; 
v_a_3342_ = lean_ctor_get(v_a_3338_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v_a_3338_, 1);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_a_3342_);
v___x_3344_ = v___x_3340_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; size_t v_sz_3349_; size_t v___x_3350_; lean_object* v___x_3351_; 
lean_del_object(v___x_3340_);
v_a_3346_ = lean_ctor_get(v_a_3338_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v_a_3338_, 1);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v_a_3346_);
v_sz_3349_ = lean_array_size(v_tail_3336_);
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3336_, v_sz_3349_, v___x_3350_, v___x_3348_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3365_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3365_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3365_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_fst_3356_; 
v_fst_3356_ = lean_ctor_get(v_a_3352_, 0);
if (lean_obj_tag(v_fst_3356_) == 0)
{
lean_object* v_snd_3357_; lean_object* v___x_3359_; 
v_snd_3357_ = lean_ctor_get(v_a_3352_, 1);
lean_inc(v_snd_3357_);
lean_dec(v_a_3352_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_snd_3357_);
v___x_3359_ = v___x_3354_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_snd_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
else
{
lean_object* v_val_3361_; lean_object* v___x_3363_; 
lean_inc_ref(v_fst_3356_);
lean_dec(v_a_3352_);
v_val_3361_ = lean_ctor_get(v_fst_3356_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v_fst_3356_, 1);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_val_3361_);
v___x_3363_ = v___x_3354_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_val_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_a_3366_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3351_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3351_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v_a_3375_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3337_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3337_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3383_, lean_object* v_init_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3383_, v_init_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec_ref(v_t_3383_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_lctx_3402_; lean_object* v_decls_3403_; lean_object* v_hs_3404_; lean_object* v___x_3405_; 
v_lctx_3402_ = lean_ctor_get(v___y_3397_, 2);
v_decls_3403_ = lean_ctor_get(v_lctx_3402_, 1);
v_hs_3404_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3405_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3403_, v_hs_3404_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3414_, lean_object* v_cfg_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
if (v_only_3414_ == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_toApplyRulesConfig_3424_; lean_object* v_a_3425_; uint8_t v_symm_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_toApplyRulesConfig_3424_ = lean_ctor_get(v_cfg_3415_, 0);
v_a_3425_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3423_, 1);
v_symm_3426_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3424_, sizeof(void*)*2 + 1);
v___x_3427_ = lean_array_to_list(v_a_3425_);
v___x_3428_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3426_, v___x_3427_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v___x_3428_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
v_a_3429_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3423_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3423_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3439_, lean_object* v_cfg_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
uint8_t v_only_boxed_3448_; lean_object* v_res_3449_; 
v_only_boxed_3448_ = lean_unbox(v_only_3439_);
v_res_3449_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3448_, v_cfg_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v_cfg_3440_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3450_, lean_object* v_lemmas_3451_, uint8_t v_only_3452_, lean_object* v_g_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_toApplyRulesConfig_3459_; uint8_t v_intro_3460_; uint8_t v_constructor_3461_; uint8_t v_suggestions_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3475_; 
v_toApplyRulesConfig_3459_ = lean_ctor_get(v_cfg_3450_, 0);
v_intro_3460_ = lean_ctor_get_uint8(v_cfg_3450_, sizeof(void*)*1 + 1);
v_constructor_3461_ = lean_ctor_get_uint8(v_cfg_3450_, sizeof(void*)*1 + 2);
v_suggestions_3462_ = lean_ctor_get_uint8(v_cfg_3450_, sizeof(void*)*1 + 3);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_cfg_3450_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3464_ = v_cfg_3450_;
v_isShared_3465_ = v_isSharedCheck_3475_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_toApplyRulesConfig_3459_);
lean_dec(v_cfg_3450_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3475_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v_ctx_3467_; uint8_t v___x_3468_; lean_object* v___x_3470_; 
v___x_3466_ = lean_box(v_only_3452_);
v_ctx_3467_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3467_, 0, v___x_3466_);
v___x_3468_ = 0;
if (v_isShared_3465_ == 0)
{
v___x_3470_ = v___x_3464_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_toApplyRulesConfig_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3474_, sizeof(void*)*1 + 1, v_intro_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3474_, sizeof(void*)*1 + 2, v_constructor_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3474_, sizeof(void*)*1 + 3, v_suggestions_3462_);
v___x_3470_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*1, v___x_3468_);
v___x_3471_ = lean_box(0);
v___x_3472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3472_, 0, v_g_3453_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3470_, v_lemmas_3451_, v_ctx_3467_, v___x_3472_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
return v___x_3473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3476_, lean_object* v_lemmas_3477_, lean_object* v_only_3478_, lean_object* v_g_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
uint8_t v_only_boxed_3485_; lean_object* v_res_3486_; 
v_only_boxed_3485_ = lean_unbox(v_only_3478_);
v_res_3486_ = l_Lean_MVarId_applyRules(v_cfg_3476_, v_lemmas_3477_, v_only_boxed_3485_, v_g_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3487_, size_t v_sz_3488_, size_t v_i_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3487_, v_sz_3488_, v_i_3489_, v_b_3490_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3499_, lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
size_t v_sz_boxed_3510_; size_t v_i_boxed_3511_; lean_object* v_res_3512_; 
v_sz_boxed_3510_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3511_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3499_, v_sz_boxed_3510_, v_i_boxed_3511_, v_b_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_as_3499_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3513_, size_t v_sz_3514_, size_t v_i_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3513_, v_sz_3514_, v_i_3515_, v_b_3516_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3525_, lean_object* v_sz_3526_, lean_object* v_i_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
size_t v_sz_boxed_3536_; size_t v_i_boxed_3537_; lean_object* v_res_3538_; 
v_sz_boxed_3536_ = lean_unbox_usize(v_sz_3526_);
lean_dec(v_sz_3526_);
v_i_boxed_3537_ = lean_unbox_usize(v_i_3527_);
lean_dec(v_i_3527_);
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3525_, v_sz_boxed_3536_, v_i_boxed_3537_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_as_3525_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_box(0);
v___x_3548_ = 1;
v___x_3549_ = l_Lean_Elab_Term_elabTerm(v_t_3539_, v___x_3547_, v___x_3548_, v___x_3548_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_ref_3564_; uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_ref_3564_ = lean_ctor_get(v___y_3561_, 4);
v___x_3565_ = 0;
v___x_3566_ = l_Lean_SourceInfo_fromRef(v_ref_3564_, v___x_3565_);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3573_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3574_, lean_object* v_x_3575_){
_start:
{
if (lean_obj_tag(v_x_3575_) == 0)
{
uint8_t v___x_3576_; 
v___x_3576_ = 0;
return v___x_3576_;
}
else
{
lean_object* v_head_3577_; lean_object* v_tail_3578_; uint8_t v___x_3579_; 
v_head_3577_ = lean_ctor_get(v_x_3575_, 0);
v_tail_3578_ = lean_ctor_get(v_x_3575_, 1);
v___x_3579_ = lean_expr_eqv(v_a_3574_, v_head_3577_);
if (v___x_3579_ == 0)
{
v_x_3575_ = v_tail_3578_;
goto _start;
}
else
{
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3581_, lean_object* v_x_3582_){
_start:
{
uint8_t v_res_3583_; lean_object* v_r_3584_; 
v_res_3583_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3581_, v_x_3582_);
lean_dec(v_x_3582_);
lean_dec_ref(v_a_3581_);
v_r_3584_ = lean_box(v_res_3583_);
return v_r_3584_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3585_, lean_object* v_x_3586_){
_start:
{
uint8_t v___x_3587_; 
v___x_3587_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3586_, v_ys_3585_);
if (v___x_3587_ == 0)
{
uint8_t v___x_3588_; 
v___x_3588_ = 1;
return v___x_3588_;
}
else
{
uint8_t v___x_3589_; 
v___x_3589_ = 0;
return v___x_3589_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3590_, lean_object* v_x_3591_){
_start:
{
uint8_t v_res_3592_; lean_object* v_r_3593_; 
v_res_3592_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3590_, v_x_3591_);
lean_dec_ref(v_x_3591_);
lean_dec(v_ys_3590_);
v_r_3593_ = lean_box(v_res_3592_);
return v_r_3593_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3594_, lean_object* v_ys_3595_){
_start:
{
lean_object* v___f_3596_; lean_object* v___x_3597_; 
v___f_3596_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3596_, 0, v_ys_3595_);
v___x_3597_ = l_List_filter___redArg(v___f_3596_, v_xs_3594_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3598_, lean_object* v_x_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
if (lean_obj_tag(v_x_3598_) == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = l_List_reverse___redArg(v_x_3599_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
else
{
lean_object* v_head_3609_; lean_object* v_tail_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3628_; 
v_head_3609_ = lean_ctor_get(v_x_3598_, 0);
v_tail_3610_ = lean_ctor_get(v_x_3598_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_x_3598_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3612_ = v_x_3598_;
v_isShared_3613_ = v_isSharedCheck_3628_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_tail_3610_);
lean_inc(v_head_3609_);
lean_dec(v_x_3598_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3628_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; 
v___x_3614_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3609_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3614_, 1);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v_x_3599_);
lean_ctor_set(v___x_3612_, 0, v_a_3615_);
v___x_3617_ = v___x_3612_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3615_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_x_3599_);
v___x_3617_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
v_x_3598_ = v_tail_3610_;
v_x_3599_ = v___x_3617_;
goto _start;
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_del_object(v___x_3612_);
lean_dec(v_tail_3610_);
lean_dec(v_x_3599_);
v_a_3620_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3614_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3614_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3629_, v_x_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3639_, uint8_t v_noDefaults_3640_, uint8_t v_star_3641_, lean_object* v_cfg_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
if (v_noDefaults_3640_ == 0)
{
goto v___jp_3650_;
}
else
{
if (v_star_3641_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_dec(v_remove_3639_);
v___x_3669_ = lean_box(0);
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
return v___x_3670_;
}
else
{
goto v___jp_3650_;
}
}
v___jp_3650_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = lean_box(0);
v___x_3654_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3639_, v___x_3653_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_toApplyRulesConfig_3655_; lean_object* v_a_3656_; uint8_t v_symm_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v_toApplyRulesConfig_3655_ = lean_ctor_get(v_cfg_3642_, 0);
v_a_3656_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3654_, 1);
v_symm_3657_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3655_, sizeof(void*)*2 + 1);
v___x_3658_ = lean_array_to_list(v_a_3652_);
v___x_3659_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3658_, v_a_3656_);
v___x_3660_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3657_, v___x_3659_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
return v___x_3660_;
}
else
{
lean_dec(v_a_3652_);
return v___x_3654_;
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v_remove_3639_);
v_a_3661_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3651_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3651_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3671_, lean_object* v_noDefaults_3672_, lean_object* v_star_3673_, lean_object* v_cfg_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v_noDefaults_boxed_3682_; uint8_t v_star_boxed_3683_; lean_object* v_res_3684_; 
v_noDefaults_boxed_3682_ = lean_unbox(v_noDefaults_3672_);
v_star_boxed_3683_ = lean_unbox(v_star_3673_);
v_res_3684_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3671_, v_noDefaults_boxed_3682_, v_star_boxed_3683_, v_cfg_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v_cfg_3674_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3685_, size_t v_i_3686_, size_t v_stop_3687_, lean_object* v_b_3688_){
_start:
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_usize_dec_eq(v_i_3686_, v_stop_3687_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; size_t v___x_3692_; size_t v___x_3693_; 
v___x_3690_ = lean_array_uget_borrowed(v_as_3685_, v_i_3686_);
v___x_3691_ = l_Array_append___redArg(v_b_3688_, v___x_3690_);
v___x_3692_ = ((size_t)1ULL);
v___x_3693_ = lean_usize_add(v_i_3686_, v___x_3692_);
v_i_3686_ = v___x_3693_;
v_b_3688_ = v___x_3691_;
goto _start;
}
else
{
return v_b_3688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3695_, lean_object* v_i_3696_, lean_object* v_stop_3697_, lean_object* v_b_3698_){
_start:
{
size_t v_i_boxed_3699_; size_t v_stop_boxed_3700_; lean_object* v_res_3701_; 
v_i_boxed_3699_ = lean_unbox_usize(v_i_3696_);
lean_dec(v_i_3696_);
v_stop_boxed_3700_ = lean_unbox_usize(v_stop_3697_);
lean_dec(v_stop_3697_);
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3695_, v_i_boxed_3699_, v_stop_boxed_3700_, v_b_3698_);
lean_dec_ref(v_as_3695_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
if (lean_obj_tag(v_a_3702_) == 0)
{
lean_object* v___x_3704_; 
v___x_3704_ = l_List_reverse___redArg(v_a_3703_);
return v___x_3704_;
}
else
{
lean_object* v_head_3705_; lean_object* v_tail_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3715_; 
v_head_3705_ = lean_ctor_get(v_a_3702_, 0);
v_tail_3706_ = lean_ctor_get(v_a_3702_, 1);
v_isSharedCheck_3715_ = !lean_is_exclusive(v_a_3702_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3708_ = v_a_3702_;
v_isShared_3709_ = v_isSharedCheck_3715_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_tail_3706_);
lean_inc(v_head_3705_);
lean_dec(v_a_3702_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3715_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; lean_object* v___x_3712_; 
v___x_3710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3710_, 0, v_head_3705_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 1, v_a_3703_);
lean_ctor_set(v___x_3708_, 0, v___x_3710_);
v___x_3712_ = v___x_3708_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_a_3703_);
v___x_3712_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
v_a_3702_ = v_tail_3706_;
v_a_3703_ = v___x_3712_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3716_, size_t v_i_3717_, lean_object* v_bs_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
uint8_t v___x_3722_; 
v___x_3722_ = lean_usize_dec_lt(v_i_3717_, v_sz_3716_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v_bs_3718_);
return v___x_3723_;
}
else
{
lean_object* v_v_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_v_3724_ = lean_array_uget_borrowed(v_bs_3718_, v_i_3717_);
v___x_3725_ = l_Lean_Syntax_getId(v_v_3724_);
v___x_3726_ = l_Lean_labelled(v___x_3725_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v_bs_x27_3729_; size_t v___x_3730_; size_t v___x_3731_; lean_object* v___x_3732_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v___x_3728_ = lean_unsigned_to_nat(0u);
v_bs_x27_3729_ = lean_array_uset(v_bs_3718_, v_i_3717_, v___x_3728_);
v___x_3730_ = ((size_t)1ULL);
v___x_3731_ = lean_usize_add(v_i_3717_, v___x_3730_);
v___x_3732_ = lean_array_uset(v_bs_x27_3729_, v_i_3717_, v_a_3727_);
v_i_3717_ = v___x_3731_;
v_bs_3718_ = v___x_3732_;
goto _start;
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v_bs_3718_);
v_a_3734_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3726_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3726_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3742_, lean_object* v_i_3743_, lean_object* v_bs_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
size_t v_sz_boxed_3748_; size_t v_i_boxed_3749_; lean_object* v_res_3750_; 
v_sz_boxed_3748_ = lean_unbox_usize(v_sz_3742_);
lean_dec(v_sz_3742_);
v_i_boxed_3749_ = lean_unbox_usize(v_i_3743_);
lean_dec(v_i_3743_);
v_res_3750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3748_, v_i_boxed_3749_, v_bs_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3751_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
if (lean_obj_tag(v_a_3769_) == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = l_List_reverse___redArg(v_a_3770_);
return v___x_3771_;
}
else
{
lean_object* v_head_3772_; lean_object* v_tail_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3782_; 
v_head_3772_ = lean_ctor_get(v_a_3769_, 0);
v_tail_3773_ = lean_ctor_get(v_a_3769_, 1);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_a_3769_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3775_ = v_a_3769_;
v_isShared_3776_ = v_isSharedCheck_3782_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_tail_3773_);
lean_inc(v_head_3772_);
lean_dec(v_a_3769_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3782_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___f_3777_; lean_object* v___x_3779_; 
v___f_3777_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3777_, 0, v_head_3772_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v_a_3770_);
lean_ctor_set(v___x_3775_, 0, v___f_3777_);
v___x_3779_ = v___x_3775_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___f_3777_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_a_3770_);
v___x_3779_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
v_a_3769_ = v_tail_3773_;
v_a_3770_ = v___x_3779_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3785_ = l_Lean_stringToMessageData(v___x_3784_);
return v___x_3785_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3788_ = l_String_toRawSubstring_x27(v___x_3787_);
return v___x_3788_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3793_ = l_String_toRawSubstring_x27(v___x_3792_);
return v___x_3793_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3798_ = l_String_toRawSubstring_x27(v___x_3797_);
return v___x_3798_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3803_ = l_String_toRawSubstring_x27(v___x_3802_);
return v___x_3803_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3835_, uint8_t v_star_3836_, lean_object* v_add_3837_, lean_object* v_remove_3838_, lean_object* v_use_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___f_3870_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; 
v___x_3868_ = lean_box(v_noDefaults_3835_);
v___x_3869_ = lean_box(v_star_3836_);
lean_inc(v_remove_3838_);
v___f_3870_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3870_, 0, v_remove_3838_);
lean_closure_set(v___f_3870_, 1, v___x_3868_);
lean_closure_set(v___f_3870_, 2, v___x_3869_);
if (v_star_3836_ == 0)
{
v___y_3887_ = v_a_3840_;
v___y_3888_ = v_a_3841_;
v___y_3889_ = v_a_3842_;
v___y_3890_ = v_a_3843_;
goto v___jp_3886_;
}
else
{
if (v_noDefaults_3835_ == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec_ref(v___f_3870_);
lean_dec_ref(v_use_3839_);
lean_dec(v_remove_3838_);
lean_dec(v_add_3837_);
v___x_3947_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3948_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3947_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3948_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3948_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
else
{
v___y_3887_ = v_a_3840_;
v___y_3888_ = v_a_3841_;
v___y_3889_ = v_a_3842_;
v___y_3890_ = v_a_3843_;
goto v___jp_3886_;
}
}
v___jp_3845_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___y_3846_);
lean_ctor_set(v___x_3848_, 1, v___y_3847_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
return v___x_3849_;
}
v___jp_3850_:
{
uint8_t v___x_3857_; 
v___x_3857_ = l_List_isEmpty___redArg(v_remove_3838_);
lean_dec(v_remove_3838_);
if (v___x_3857_ == 0)
{
if (v_noDefaults_3835_ == 0)
{
v___y_3846_ = v___y_3856_;
v___y_3847_ = v___y_3855_;
goto v___jp_3845_;
}
else
{
if (v_star_3836_ == 0)
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
v___x_3858_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3859_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3858_, v___y_3853_, v___y_3854_, v___y_3851_, v___y_3852_);
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
else
{
v___y_3846_ = v___y_3856_;
v___y_3847_ = v___y_3855_;
goto v___jp_3845_;
}
}
}
else
{
v___y_3846_ = v___y_3856_;
v___y_3847_ = v___y_3855_;
goto v___jp_3845_;
}
}
v___jp_3871_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_array_to_list(v___y_3878_);
lean_inc(v___y_3876_);
v___x_3880_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3879_, v___y_3876_);
if (v_noDefaults_3835_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3837_, v___y_3876_);
v___x_3882_ = l_List_appendTR___redArg(v___x_3881_, v___x_3880_);
v___x_3883_ = l_List_appendTR___redArg(v___x_3882_, v___y_3873_);
v___y_3851_ = v___y_3872_;
v___y_3852_ = v___y_3875_;
v___y_3853_ = v___y_3874_;
v___y_3854_ = v___y_3877_;
v___y_3855_ = v___f_3870_;
v___y_3856_ = v___x_3883_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_dec(v___y_3873_);
v___x_3884_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3837_, v___y_3876_);
v___x_3885_ = l_List_appendTR___redArg(v___x_3884_, v___x_3880_);
v___y_3851_ = v___y_3872_;
v___y_3852_ = v___y_3875_;
v___y_3853_ = v___y_3874_;
v___y_3854_ = v___y_3877_;
v___y_3855_ = v___f_3870_;
v___y_3856_ = v___x_3885_;
goto v___jp_3850_;
}
}
v___jp_3886_:
{
lean_object* v_toCold_3891_; lean_object* v_ref_3892_; lean_object* v_currMacroScope_3893_; lean_object* v_quotContext_3894_; lean_object* v___x_3895_; lean_object* v_a_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; size_t v_sz_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
v_toCold_3891_ = lean_ctor_get(v___y_3889_, 0);
v_ref_3892_ = lean_ctor_get(v___y_3889_, 4);
v_currMacroScope_3893_ = lean_ctor_get(v___y_3889_, 9);
v_quotContext_3894_ = lean_ctor_get(v_toCold_3891_, 2);
v___x_3895_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v___x_3897_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3898_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3893_, 2);
lean_inc_n(v_quotContext_3894_, 2);
v___x_3901_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3900_, v_currMacroScope_3893_);
v___x_3902_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_3903_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3906_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3905_, v_currMacroScope_3893_);
v___x_3907_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_3908_ = lean_array_size(v_use_3839_);
v___x_3909_ = ((size_t)0ULL);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3908_, v___x_3909_, v_use_3839_, v___y_3889_, v___y_3890_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3893_, 2);
lean_inc_n(v_quotContext_3894_, 2);
v___x_3913_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3912_, v_currMacroScope_3893_);
v___x_3914_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_3915_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_3916_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3915_, v_currMacroScope_3893_);
v___x_3917_ = 0;
v___x_3918_ = l_Lean_SourceInfo_fromRef(v_ref_3892_, v___x_3917_);
v___x_3919_ = lean_box(0);
v___x_3920_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_3921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3918_);
lean_ctor_set(v___x_3921_, 1, v___x_3897_);
lean_ctor_set(v___x_3921_, 2, v___x_3901_);
lean_ctor_set(v___x_3921_, 3, v___x_3920_);
v___x_3922_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3923_, 0, v_a_3896_);
lean_ctor_set(v___x_3923_, 1, v___x_3902_);
lean_ctor_set(v___x_3923_, 2, v___x_3906_);
lean_ctor_set(v___x_3923_, 3, v___x_3922_);
v___x_3924_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3925_, 0, v_a_3899_);
lean_ctor_set(v___x_3925_, 1, v___x_3907_);
lean_ctor_set(v___x_3925_, 2, v___x_3913_);
lean_ctor_set(v___x_3925_, 3, v___x_3924_);
v___x_3926_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3927_, 0, v_a_3904_);
lean_ctor_set(v___x_3927_, 1, v___x_3914_);
lean_ctor_set(v___x_3927_, 2, v___x_3916_);
lean_ctor_set(v___x_3927_, 3, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
lean_ctor_set(v___x_3928_, 1, v___x_3919_);
v___x_3929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3925_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3923_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3921_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_3931_, v___x_3919_);
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3935_ = lean_array_get_size(v_a_3911_);
v___x_3936_ = lean_nat_dec_lt(v___x_3933_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_dec(v_a_3911_);
v___y_3872_ = v___y_3889_;
v___y_3873_ = v___x_3932_;
v___y_3874_ = v___y_3887_;
v___y_3875_ = v___y_3890_;
v___y_3876_ = v___x_3919_;
v___y_3877_ = v___y_3888_;
v___y_3878_ = v___x_3934_;
goto v___jp_3871_;
}
else
{
size_t v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_usize_of_nat(v___x_3935_);
v___x_3938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3911_, v___x_3909_, v___x_3937_, v___x_3934_);
lean_dec(v_a_3911_);
v___y_3872_ = v___y_3889_;
v___y_3873_ = v___x_3932_;
v___y_3874_ = v___y_3887_;
v___y_3875_ = v___y_3890_;
v___y_3876_ = v___x_3919_;
v___y_3877_ = v___y_3888_;
v___y_3878_ = v___x_3938_;
goto v___jp_3871_;
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec(v___x_3906_);
lean_dec(v_a_3904_);
lean_dec(v___x_3901_);
lean_dec(v_a_3899_);
lean_dec(v_a_3896_);
lean_dec_ref(v___f_3870_);
lean_dec(v_remove_3838_);
lean_dec(v_add_3837_);
v_a_3939_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3910_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3910_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3957_, lean_object* v_star_3958_, lean_object* v_add_3959_, lean_object* v_remove_3960_, lean_object* v_use_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
uint8_t v_noDefaults_boxed_3967_; uint8_t v_star_boxed_3968_; lean_object* v_res_3969_; 
v_noDefaults_boxed_3967_ = lean_unbox(v_noDefaults_3957_);
v_star_boxed_3968_ = lean_unbox(v_star_3958_);
v_res_3969_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3967_, v_star_boxed_3968_, v_add_3959_, v_remove_3960_, v_use_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_3970_, size_t v_i_3971_, lean_object* v_bs_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3970_, v_i_3971_, v_bs_3972_, v___y_3975_, v___y_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_3979_, lean_object* v_i_3980_, lean_object* v_bs_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
size_t v_sz_boxed_3987_; size_t v_i_boxed_3988_; lean_object* v_res_3989_; 
v_sz_boxed_3987_ = lean_unbox_usize(v_sz_3979_);
lean_dec(v_sz_3979_);
v_i_boxed_3988_ = lean_unbox_usize(v_i_3980_);
lean_dec(v_i_3980_);
v_res_3989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_3987_, v_i_boxed_3988_, v_bs_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
return v_res_3989_;
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

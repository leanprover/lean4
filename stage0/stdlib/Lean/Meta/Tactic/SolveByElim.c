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
uint8_t v___x_13832__boxed_297_; uint8_t v___x_13833__boxed_298_; lean_object* v_res_299_; 
v___x_13832__boxed_297_ = lean_unbox(v___x_288_);
v___x_13833__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13832__boxed_297_, v___x_13833__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
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
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_toCold_309_; lean_object* v_mctx_310_; lean_object* v_lctx_311_; lean_object* v_options_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_302_);
v_toCold_309_ = lean_ctor_get(v___y_303_, 0);
v_mctx_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_310_);
lean_dec(v___x_308_);
v_lctx_311_ = lean_ctor_get(v___y_301_, 2);
v_options_312_ = lean_ctor_get(v_toCold_309_, 2);
lean_inc_ref(v_options_312_);
lean_inc_ref(v_lctx_311_);
v___x_313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_313_, 0, v_env_307_);
lean_ctor_set(v___x_313_, 1, v_mctx_310_);
lean_ctor_set(v___x_313_, 2, v_lctx_311_);
lean_ctor_set(v___x_313_, 3, v_options_312_);
v___x_314_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_msgData_300_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_323_, size_t v_i_324_, lean_object* v_bs_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_326_ == 0)
{
return v_bs_325_;
}
else
{
lean_object* v_v_327_; lean_object* v_msg_328_; lean_object* v___x_329_; lean_object* v_bs_x27_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v_v_327_ = lean_array_uget_borrowed(v_bs_325_, v_i_324_);
v_msg_328_ = lean_ctor_get(v_v_327_, 1);
lean_inc_ref(v_msg_328_);
v___x_329_ = lean_unsigned_to_nat(0u);
v_bs_x27_330_ = lean_array_uset(v_bs_325_, v_i_324_, v___x_329_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_324_, v___x_331_);
v___x_333_ = lean_array_uset(v_bs_x27_330_, v_i_324_, v_msg_328_);
v_i_324_ = v___x_332_;
v_bs_325_ = v___x_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_bs_337_){
_start:
{
size_t v_sz_boxed_338_; size_t v_i_boxed_339_; lean_object* v_res_340_; 
v_sz_boxed_338_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_339_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_338_, v_i_boxed_339_, v_bs_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_341_, lean_object* v_data_342_, lean_object* v_ref_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_toCold_350_; lean_object* v_currRecDepth_351_; lean_object* v_ref_352_; uint8_t v_diag_353_; uint8_t v_suppressElabErrors_354_; lean_object* v___x_355_; lean_object* v_traceState_356_; lean_object* v_traces_357_; lean_object* v_ref_358_; lean_object* v___x_359_; lean_object* v___x_360_; size_t v_sz_361_; size_t v___x_362_; lean_object* v___x_363_; lean_object* v_msg_364_; lean_object* v___x_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_403_; 
v_toCold_350_ = lean_ctor_get(v___y_347_, 0);
v_currRecDepth_351_ = lean_ctor_get(v___y_347_, 1);
v_ref_352_ = lean_ctor_get(v___y_347_, 2);
v_diag_353_ = lean_ctor_get_uint8(v___y_347_, sizeof(void*)*3);
v_suppressElabErrors_354_ = lean_ctor_get_uint8(v___y_347_, sizeof(void*)*3 + 1);
v___x_355_ = lean_st_ref_get(v___y_348_);
v_traceState_356_ = lean_ctor_get(v___x_355_, 4);
lean_inc_ref(v_traceState_356_);
lean_dec(v___x_355_);
v_traces_357_ = lean_ctor_get(v_traceState_356_, 0);
lean_inc_ref(v_traces_357_);
lean_dec_ref(v_traceState_356_);
v_ref_358_ = l_Lean_replaceRef(v_ref_343_, v_ref_352_);
lean_inc(v_currRecDepth_351_);
lean_inc_ref(v_toCold_350_);
v___x_359_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_359_, 0, v_toCold_350_);
lean_ctor_set(v___x_359_, 1, v_currRecDepth_351_);
lean_ctor_set(v___x_359_, 2, v_ref_358_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*3, v_diag_353_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*3 + 1, v_suppressElabErrors_354_);
v___x_360_ = l_Lean_PersistentArray_toArray___redArg(v_traces_357_);
lean_dec_ref(v_traces_357_);
v_sz_361_ = lean_array_size(v___x_360_);
v___x_362_ = ((size_t)0ULL);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_361_, v___x_362_, v___x_360_);
v_msg_364_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_364_, 0, v_data_342_);
lean_ctor_set(v_msg_364_, 1, v_msg_344_);
lean_ctor_set(v_msg_364_, 2, v___x_363_);
v___x_365_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_364_, v___y_345_, v___y_346_, v___x_359_, v___y_348_);
lean_dec_ref_known(v___x_359_, 3);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_403_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_403_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_403_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v_traceState_371_; lean_object* v_env_372_; lean_object* v_nextMacroScope_373_; lean_object* v_ngen_374_; lean_object* v_auxDeclNGen_375_; lean_object* v_cache_376_; lean_object* v_messages_377_; lean_object* v_infoState_378_; lean_object* v_snapshotTasks_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_402_; 
v___x_370_ = lean_st_ref_take(v___y_348_);
v_traceState_371_ = lean_ctor_get(v___x_370_, 4);
v_env_372_ = lean_ctor_get(v___x_370_, 0);
v_nextMacroScope_373_ = lean_ctor_get(v___x_370_, 1);
v_ngen_374_ = lean_ctor_get(v___x_370_, 2);
v_auxDeclNGen_375_ = lean_ctor_get(v___x_370_, 3);
v_cache_376_ = lean_ctor_get(v___x_370_, 5);
v_messages_377_ = lean_ctor_get(v___x_370_, 6);
v_infoState_378_ = lean_ctor_get(v___x_370_, 7);
v_snapshotTasks_379_ = lean_ctor_get(v___x_370_, 8);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_402_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snapshotTasks_379_);
lean_inc(v_infoState_378_);
lean_inc(v_messages_377_);
lean_inc(v_cache_376_);
lean_inc(v_traceState_371_);
lean_inc(v_auxDeclNGen_375_);
lean_inc(v_ngen_374_);
lean_inc(v_nextMacroScope_373_);
lean_inc(v_env_372_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint64_t v_tid_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_400_; 
v_tid_383_ = lean_ctor_get_uint64(v_traceState_371_, sizeof(void*)*1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_traceState_371_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_traceState_371_, 0);
lean_dec(v_unused_401_);
v___x_385_ = v_traceState_371_;
v_isShared_386_ = v_isSharedCheck_400_;
goto v_resetjp_384_;
}
else
{
lean_dec(v_traceState_371_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_400_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_ref_343_);
lean_ctor_set(v___x_387_, 1, v_a_366_);
v___x_388_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_341_, v___x_387_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_388_);
lean_ctor_set_uint64(v_reuseFailAlloc_399_, sizeof(void*)*1, v_tid_383_);
v___x_390_ = v_reuseFailAlloc_399_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v___x_390_);
v___x_392_ = v___x_381_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_env_372_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_nextMacroScope_373_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_ngen_374_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_auxDeclNGen_375_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_398_, 5, v_cache_376_);
lean_ctor_set(v_reuseFailAlloc_398_, 6, v_messages_377_);
lean_ctor_set(v_reuseFailAlloc_398_, 7, v_infoState_378_);
lean_ctor_set(v_reuseFailAlloc_398_, 8, v_snapshotTasks_379_);
v___x_392_ = v_reuseFailAlloc_398_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_st_ref_put(v___y_348_, v___x_392_);
v___x_394_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_394_);
v___x_396_ = v___x_368_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_404_, lean_object* v_data_405_, lean_object* v_ref_406_, lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_404_, v_data_405_, v_ref_406_, v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_414_){
_start:
{
if (lean_obj_tag(v_e_414_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 2;
return v___x_415_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_417_);
lean_dec_ref(v_e_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_420_, lean_object* v_opt_421_){
_start:
{
lean_object* v_name_422_; lean_object* v_defValue_423_; lean_object* v_map_424_; lean_object* v___x_425_; 
v_name_422_ = lean_ctor_get(v_opt_421_, 0);
v_defValue_423_ = lean_ctor_get(v_opt_421_, 1);
v_map_424_ = lean_ctor_get(v_opts_420_, 0);
v___x_425_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_424_, v_name_422_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_inc(v_defValue_423_);
return v_defValue_423_;
}
else
{
lean_object* v_val_426_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v___x_425_, 1);
if (lean_obj_tag(v_val_426_) == 3)
{
lean_object* v_v_427_; 
v_v_427_ = lean_ctor_get(v_val_426_, 0);
lean_inc(v_v_427_);
lean_dec_ref_known(v_val_426_, 1);
return v_v_427_;
}
else
{
lean_dec(v_val_426_);
lean_inc(v_defValue_423_);
return v_defValue_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_428_, lean_object* v_opt_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_428_, v_opt_429_);
lean_dec_ref(v_opt_429_);
lean_dec_ref(v_opts_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v_x_431_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v_x_431_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v_x_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set_tag(v___x_435_, 1);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v_x_431_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v_x_431_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v_x_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 0);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_449_);
return v_res_451_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_452_; double v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_float_of_nat(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_457_; double v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(1000u);
v___x_458_ = lean_float_of_nat(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_459_, uint8_t v_collapsed_460_, lean_object* v_tag_461_, lean_object* v_opts_462_, uint8_t v_clsEnabled_463_, lean_object* v_oldTraces_464_, lean_object* v_msg_465_, lean_object* v_resStartStop_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v_data_477_; lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___y_493_; lean_object* v_a_494_; uint8_t v___y_509_; double v___y_540_; 
v_fst_472_ = lean_ctor_get(v_resStartStop_466_, 0);
lean_inc(v_fst_472_);
v_snd_473_ = lean_ctor_get(v_resStartStop_466_, 1);
lean_inc(v_snd_473_);
lean_dec_ref(v_resStartStop_466_);
v_fst_488_ = lean_ctor_get(v_snd_473_, 0);
lean_inc(v_fst_488_);
v_snd_489_ = lean_ctor_get(v_snd_473_, 1);
lean_inc(v_snd_489_);
lean_dec(v_snd_473_);
v___x_490_ = l_Lean_trace_profiler;
v___x_491_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_462_, v___x_490_);
if (v___x_491_ == 0)
{
v___y_509_ = v___x_491_;
goto v___jp_508_;
}
else
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = l_Lean_trace_profiler_useHeartbeats;
v___x_546_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_462_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; double v___x_549_; double v___x_550_; double v___x_551_; 
v___x_547_ = l_Lean_trace_profiler_threshold;
v___x_548_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_462_, v___x_547_);
v___x_549_ = lean_float_of_nat(v___x_548_);
v___x_550_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_551_ = lean_float_div(v___x_549_, v___x_550_);
v___y_540_ = v___x_551_;
goto v___jp_539_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; double v___x_554_; 
v___x_552_ = l_Lean_trace_profiler_threshold;
v___x_553_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_462_, v___x_552_);
v___x_554_ = lean_float_of_nat(v___x_553_);
v___y_540_ = v___x_554_;
goto v___jp_539_;
}
}
v___jp_474_:
{
lean_object* v___x_478_; 
lean_inc(v___y_475_);
v___x_478_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_464_, v_data_477_, v___y_475_, v___y_476_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; 
lean_dec_ref_known(v___x_478_, 1);
v___x_479_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_472_);
return v___x_479_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_fst_472_);
v_a_480_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_478_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
v___jp_492_:
{
uint8_t v_result_495_; lean_object* v___x_496_; lean_object* v___x_497_; double v___x_498_; lean_object* v_data_499_; 
v_result_495_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_472_);
v___x_496_ = lean_box(v_result_495_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
v___x_498_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_461_);
lean_inc_ref(v___x_497_);
lean_inc(v_cls_459_);
v_data_499_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_499_, 0, v_cls_459_);
lean_ctor_set(v_data_499_, 1, v___x_497_);
lean_ctor_set(v_data_499_, 2, v_tag_461_);
lean_ctor_set_float(v_data_499_, sizeof(void*)*3, v___x_498_);
lean_ctor_set_float(v_data_499_, sizeof(void*)*3 + 8, v___x_498_);
lean_ctor_set_uint8(v_data_499_, sizeof(void*)*3 + 16, v_collapsed_460_);
if (v___x_491_ == 0)
{
lean_dec_ref_known(v___x_497_, 1);
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
lean_dec_ref(v_tag_461_);
lean_dec(v_cls_459_);
v___y_475_ = v___y_493_;
v___y_476_ = v_a_494_;
v_data_477_ = v_data_499_;
goto v___jp_474_;
}
else
{
lean_object* v_data_500_; double v___x_501_; double v___x_502_; 
lean_dec_ref_known(v_data_499_, 3);
v_data_500_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_500_, 0, v_cls_459_);
lean_ctor_set(v_data_500_, 1, v___x_497_);
lean_ctor_set(v_data_500_, 2, v_tag_461_);
v___x_501_ = lean_unbox_float(v_fst_488_);
lean_dec(v_fst_488_);
lean_ctor_set_float(v_data_500_, sizeof(void*)*3, v___x_501_);
v___x_502_ = lean_unbox_float(v_snd_489_);
lean_dec(v_snd_489_);
lean_ctor_set_float(v_data_500_, sizeof(void*)*3 + 8, v___x_502_);
lean_ctor_set_uint8(v_data_500_, sizeof(void*)*3 + 16, v_collapsed_460_);
v___y_475_ = v___y_493_;
v___y_476_ = v_a_494_;
v_data_477_ = v_data_500_;
goto v___jp_474_;
}
}
v___jp_503_:
{
lean_object* v_ref_504_; lean_object* v___x_505_; 
v_ref_504_ = lean_ctor_get(v___y_469_, 2);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v_fst_472_);
v___x_505_ = lean_apply_6(v_msg_465_, v_fst_472_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, lean_box(0));
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___y_493_ = v_ref_504_;
v_a_494_ = v_a_506_;
goto v___jp_492_;
}
else
{
lean_object* v___x_507_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_493_ = v_ref_504_;
v_a_494_ = v___x_507_;
goto v___jp_492_;
}
}
v___jp_508_:
{
if (v_clsEnabled_463_ == 0)
{
if (v___y_509_ == 0)
{
lean_object* v___x_510_; lean_object* v_traceState_511_; lean_object* v_env_512_; lean_object* v_nextMacroScope_513_; lean_object* v_ngen_514_; lean_object* v_auxDeclNGen_515_; lean_object* v_cache_516_; lean_object* v_messages_517_; lean_object* v_infoState_518_; lean_object* v_snapshotTasks_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
lean_dec_ref(v_msg_465_);
lean_dec_ref(v_tag_461_);
lean_dec(v_cls_459_);
v___x_510_ = lean_st_ref_take(v___y_470_);
v_traceState_511_ = lean_ctor_get(v___x_510_, 4);
v_env_512_ = lean_ctor_get(v___x_510_, 0);
v_nextMacroScope_513_ = lean_ctor_get(v___x_510_, 1);
v_ngen_514_ = lean_ctor_get(v___x_510_, 2);
v_auxDeclNGen_515_ = lean_ctor_get(v___x_510_, 3);
v_cache_516_ = lean_ctor_get(v___x_510_, 5);
v_messages_517_ = lean_ctor_get(v___x_510_, 6);
v_infoState_518_ = lean_ctor_get(v___x_510_, 7);
v_snapshotTasks_519_ = lean_ctor_get(v___x_510_, 8);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_538_ == 0)
{
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snapshotTasks_519_);
lean_inc(v_infoState_518_);
lean_inc(v_messages_517_);
lean_inc(v_cache_516_);
lean_inc(v_traceState_511_);
lean_inc(v_auxDeclNGen_515_);
lean_inc(v_ngen_514_);
lean_inc(v_nextMacroScope_513_);
lean_inc(v_env_512_);
lean_dec(v___x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint64_t v_tid_523_; lean_object* v_traces_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_537_; 
v_tid_523_ = lean_ctor_get_uint64(v_traceState_511_, sizeof(void*)*1);
v_traces_524_ = lean_ctor_get(v_traceState_511_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_traceState_511_);
if (v_isSharedCheck_537_ == 0)
{
v___x_526_ = v_traceState_511_;
v_isShared_527_ = v_isSharedCheck_537_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_traces_524_);
lean_dec(v_traceState_511_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_537_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_464_, v_traces_524_);
lean_dec_ref(v_traces_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_528_);
lean_ctor_set_uint64(v_reuseFailAlloc_536_, sizeof(void*)*1, v_tid_523_);
v___x_530_ = v_reuseFailAlloc_536_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_env_512_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_nextMacroScope_513_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_ngen_514_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_auxDeclNGen_515_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_535_, 5, v_cache_516_);
lean_ctor_set(v_reuseFailAlloc_535_, 6, v_messages_517_);
lean_ctor_set(v_reuseFailAlloc_535_, 7, v_infoState_518_);
lean_ctor_set(v_reuseFailAlloc_535_, 8, v_snapshotTasks_519_);
v___x_532_ = v_reuseFailAlloc_535_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_st_ref_put(v___y_470_, v___x_532_);
v___x_534_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_472_);
return v___x_534_;
}
}
}
}
}
else
{
goto v___jp_503_;
}
}
else
{
goto v___jp_503_;
}
}
v___jp_539_:
{
double v___x_541_; double v___x_542_; double v___x_543_; uint8_t v___x_544_; 
v___x_541_ = lean_unbox_float(v_snd_489_);
v___x_542_ = lean_unbox_float(v_fst_488_);
v___x_543_ = lean_float_sub(v___x_541_, v___x_542_);
v___x_544_ = lean_float_decLt(v___y_540_, v___x_543_);
v___y_509_ = v___x_544_;
goto v___jp_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_555_, lean_object* v_collapsed_556_, lean_object* v_tag_557_, lean_object* v_opts_558_, lean_object* v_clsEnabled_559_, lean_object* v_oldTraces_560_, lean_object* v_msg_561_, lean_object* v_resStartStop_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v_collapsed_boxed_568_; uint8_t v_clsEnabled_boxed_569_; lean_object* v_res_570_; 
v_collapsed_boxed_568_ = lean_unbox(v_collapsed_556_);
v_clsEnabled_boxed_569_ = lean_unbox(v_clsEnabled_559_);
v_res_570_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_555_, v_collapsed_boxed_568_, v_tag_557_, v_opts_558_, v_clsEnabled_boxed_569_, v_oldTraces_560_, v_msg_561_, v_resStartStop_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_opts_558_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v_x_573_);
return v___x_579_;
}
else
{
lean_object* v_head_580_; lean_object* v_tail_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_604_; 
v_head_580_ = lean_ctor_get(v_x_572_, 0);
v_tail_581_ = lean_ctor_get(v_x_572_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_604_ == 0)
{
v___x_583_ = v_x_572_;
v_isShared_584_ = v_isSharedCheck_604_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_tail_581_);
lean_inc(v_head_580_);
lean_dec(v_x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_604_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; 
lean_inc(v_head_580_);
v___x_585_ = l_Lean_MVarId_inferInstance(v_head_580_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_dec_ref_known(v___x_585_, 1);
lean_del_object(v___x_583_);
lean_dec(v_head_580_);
v_x_572_ = v_tail_581_;
goto _start;
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_603_; 
v_a_587_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_603_ == 0)
{
v___x_589_ = v___x_585_;
v_isShared_590_ = v_isSharedCheck_603_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_603_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
uint8_t v___y_592_; uint8_t v___x_601_; 
v___x_601_ = l_Lean_Exception_isInterrupt(v_a_587_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; 
lean_inc(v_a_587_);
v___x_602_ = l_Lean_Exception_isRuntime(v_a_587_);
v___y_592_ = v___x_602_;
goto v___jp_591_;
}
else
{
v___y_592_ = v___x_601_;
goto v___jp_591_;
}
v___jp_591_:
{
if (v___y_592_ == 0)
{
lean_del_object(v___x_589_);
lean_dec(v_a_587_);
if (v___x_571_ == 0)
{
lean_del_object(v___x_583_);
lean_dec(v_head_580_);
v_x_572_ = v_tail_581_;
goto _start;
}
else
{
lean_object* v___x_595_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_x_573_);
v___x_595_ = v___x_583_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_head_580_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_x_573_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v_x_572_ = v_tail_581_;
v_x_573_ = v___x_595_;
goto _start;
}
}
}
else
{
lean_object* v___x_599_; 
lean_del_object(v___x_583_);
lean_dec(v_tail_581_);
lean_dec(v_head_580_);
lean_dec(v_x_573_);
if (v_isShared_590_ == 0)
{
v___x_599_ = v___x_589_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_587_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_605_, lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
uint8_t v___x_14257__boxed_613_; lean_object* v_res_614_; 
v___x_14257__boxed_613_ = lean_unbox(v___x_605_);
v_res_614_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14257__boxed_613_, v_x_606_, v_x_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_x_617_);
return v___x_623_;
}
else
{
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_648_; 
v_head_624_ = lean_ctor_get(v_x_616_, 0);
v_tail_625_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_648_ == 0)
{
v___x_627_ = v_x_616_;
v_isShared_628_ = v_isSharedCheck_648_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_tail_625_);
lean_inc(v_head_624_);
lean_dec(v_x_616_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_648_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_634_; 
lean_inc(v_head_624_);
v___x_634_ = l_Lean_MVarId_inferInstance(v_head_624_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref_known(v___x_634_, 1);
if (v___x_615_ == 0)
{
lean_del_object(v___x_627_);
lean_dec(v_head_624_);
v_x_616_ = v_tail_625_;
goto _start;
}
else
{
goto v___jp_629_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_647_; 
v_a_636_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_647_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_647_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_647_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint8_t v___y_641_; uint8_t v___x_645_; 
v___x_645_ = l_Lean_Exception_isInterrupt(v_a_636_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
lean_inc(v_a_636_);
v___x_646_ = l_Lean_Exception_isRuntime(v_a_636_);
v___y_641_ = v___x_646_;
goto v___jp_640_;
}
else
{
v___y_641_ = v___x_645_;
goto v___jp_640_;
}
v___jp_640_:
{
if (v___y_641_ == 0)
{
lean_del_object(v___x_638_);
lean_dec(v_a_636_);
goto v___jp_629_;
}
else
{
lean_object* v___x_643_; 
lean_del_object(v___x_627_);
lean_dec(v_tail_625_);
lean_dec(v_head_624_);
lean_dec(v_x_617_);
if (v_isShared_639_ == 0)
{
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_636_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
v___jp_629_:
{
lean_object* v___x_631_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_x_617_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_head_624_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_x_617_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v_x_616_ = v_tail_625_;
v_x_617_ = v___x_631_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_14334__boxed_657_; lean_object* v_res_658_; 
v___x_14334__boxed_657_ = lean_unbox(v___x_649_);
v_res_658_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14334__boxed_657_, v_x_650_, v_x_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_658_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_662_; double v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(1000000000u);
v___x_663_ = lean_float_of_nat(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_664_, lean_object* v_g_665_, lean_object* v_e_666_, lean_object* v_cfg_667_, lean_object* v___x_668_, lean_object* v___x_669_, uint8_t v___x_670_, lean_object* v___x_671_, lean_object* v___f_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_toCold_678_; lean_object* v_options_679_; lean_object* v_inheritedTraceOptions_680_; uint8_t v_hasTrace_681_; lean_object* v___y_683_; 
v_toCold_678_ = lean_ctor_get(v___y_675_, 0);
v_options_679_ = lean_ctor_get(v_toCold_678_, 2);
v_inheritedTraceOptions_680_ = lean_ctor_get(v_toCold_678_, 11);
v_hasTrace_681_ = lean_ctor_get_uint8(v_options_679_, sizeof(void*)*1);
if (v_hasTrace_681_ == 0)
{
lean_object* v___x_704_; uint8_t v_transparency_705_; uint8_t v___x_706_; 
lean_dec_ref(v___f_672_);
lean_dec_ref(v___x_671_);
lean_dec(v___x_669_);
v___x_704_ = l_Lean_Meta_Context_config(v___y_673_);
v_transparency_705_ = lean_ctor_get_uint8(v___x_704_, 9);
lean_dec_ref(v___x_704_);
v___x_706_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_705_, v_transparency_664_);
if (v___x_706_ == 0)
{
lean_object* v_keyedConfig_707_; uint8_t v_trackZetaDelta_708_; lean_object* v_zetaDeltaSet_709_; lean_object* v_lctx_710_; lean_object* v_localInstances_711_; lean_object* v_defEqCtx_x3f_712_; lean_object* v_synthPendingDepth_713_; lean_object* v_customCanUnfoldPredicate_x3f_714_; uint8_t v_univApprox_715_; uint8_t v_inTypeClassResolution_716_; uint8_t v_cacheInferType_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_keyedConfig_707_ = lean_ctor_get(v___y_673_, 0);
v_trackZetaDelta_708_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7);
v_zetaDeltaSet_709_ = lean_ctor_get(v___y_673_, 1);
v_lctx_710_ = lean_ctor_get(v___y_673_, 2);
v_localInstances_711_ = lean_ctor_get(v___y_673_, 3);
v_defEqCtx_x3f_712_ = lean_ctor_get(v___y_673_, 4);
v_synthPendingDepth_713_ = lean_ctor_get(v___y_673_, 5);
v_customCanUnfoldPredicate_x3f_714_ = lean_ctor_get(v___y_673_, 6);
v_univApprox_715_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_716_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 2);
v_cacheInferType_717_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_707_);
v___x_718_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_664_, v_keyedConfig_707_);
lean_inc(v_customCanUnfoldPredicate_x3f_714_);
lean_inc(v_synthPendingDepth_713_);
lean_inc(v_defEqCtx_x3f_712_);
lean_inc_ref(v_localInstances_711_);
lean_inc_ref(v_lctx_710_);
lean_inc(v_zetaDeltaSet_709_);
v___x_719_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_zetaDeltaSet_709_);
lean_ctor_set(v___x_719_, 2, v_lctx_710_);
lean_ctor_set(v___x_719_, 3, v_localInstances_711_);
lean_ctor_set(v___x_719_, 4, v_defEqCtx_x3f_712_);
lean_ctor_set(v___x_719_, 5, v_synthPendingDepth_713_);
lean_ctor_set(v___x_719_, 6, v_customCanUnfoldPredicate_x3f_714_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*7, v_trackZetaDelta_708_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*7 + 1, v_univApprox_715_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*7 + 2, v_inTypeClassResolution_716_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*7 + 3, v_cacheInferType_717_);
v___x_720_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___x_719_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref_known(v___x_719_, 7);
v___y_683_ = v___x_720_;
goto v___jp_682_;
}
else
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
v___y_683_ = v___x_721_;
goto v___jp_682_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v_a_728_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v_a_743_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v_a_748_; lean_object* v___y_751_; uint8_t v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v_a_766_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v_a_778_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v_a_783_; lean_object* v___y_786_; uint8_t v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; 
v___x_722_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_669_);
v___x_723_ = l_Lean_Name_append(v___x_722_, v___x_669_);
v___x_724_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_680_, v_options_679_, v___x_723_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___y_844_; 
v___x_841_ = l_Lean_trace_profiler;
v___x_842_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_679_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_865_; uint8_t v_transparency_866_; uint8_t v___x_867_; 
lean_dec_ref(v___f_672_);
lean_dec_ref(v___x_671_);
lean_dec(v___x_669_);
v___x_865_ = l_Lean_Meta_Context_config(v___y_673_);
v_transparency_866_ = lean_ctor_get_uint8(v___x_865_, 9);
lean_dec_ref(v___x_865_);
v___x_867_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_866_, v_transparency_664_);
if (v___x_867_ == 0)
{
lean_object* v_keyedConfig_868_; uint8_t v_trackZetaDelta_869_; lean_object* v_zetaDeltaSet_870_; lean_object* v_lctx_871_; lean_object* v_localInstances_872_; lean_object* v_defEqCtx_x3f_873_; lean_object* v_synthPendingDepth_874_; lean_object* v_customCanUnfoldPredicate_x3f_875_; uint8_t v_univApprox_876_; uint8_t v_inTypeClassResolution_877_; uint8_t v_cacheInferType_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_keyedConfig_868_ = lean_ctor_get(v___y_673_, 0);
v_trackZetaDelta_869_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7);
v_zetaDeltaSet_870_ = lean_ctor_get(v___y_673_, 1);
v_lctx_871_ = lean_ctor_get(v___y_673_, 2);
v_localInstances_872_ = lean_ctor_get(v___y_673_, 3);
v_defEqCtx_x3f_873_ = lean_ctor_get(v___y_673_, 4);
v_synthPendingDepth_874_ = lean_ctor_get(v___y_673_, 5);
v_customCanUnfoldPredicate_x3f_875_ = lean_ctor_get(v___y_673_, 6);
v_univApprox_876_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_877_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 2);
v_cacheInferType_878_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_868_);
v___x_879_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_664_, v_keyedConfig_868_);
lean_inc(v_customCanUnfoldPredicate_x3f_875_);
lean_inc(v_synthPendingDepth_874_);
lean_inc(v_defEqCtx_x3f_873_);
lean_inc_ref(v_localInstances_872_);
lean_inc_ref(v_lctx_871_);
lean_inc(v_zetaDeltaSet_870_);
v___x_880_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_zetaDeltaSet_870_);
lean_ctor_set(v___x_880_, 2, v_lctx_871_);
lean_ctor_set(v___x_880_, 3, v_localInstances_872_);
lean_ctor_set(v___x_880_, 4, v_defEqCtx_x3f_873_);
lean_ctor_set(v___x_880_, 5, v_synthPendingDepth_874_);
lean_ctor_set(v___x_880_, 6, v_customCanUnfoldPredicate_x3f_875_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*7, v_trackZetaDelta_869_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*7 + 1, v_univApprox_876_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*7 + 2, v_inTypeClassResolution_877_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*7 + 3, v_cacheInferType_878_);
v___x_881_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___x_880_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref_known(v___x_880_, 7);
v___y_844_ = v___x_881_;
goto v___jp_843_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
v___y_844_ = v___x_882_;
goto v___jp_843_;
}
}
else
{
goto v___jp_798_;
}
v___jp_843_:
{
if (lean_obj_tag(v___y_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_a_845_ = lean_ctor_get(v___y_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___y_844_, 1);
v___x_846_ = lean_box(0);
v___x_847_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_842_, v_hasTrace_681_, v_a_845_, v___x_846_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___y_673_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_852_ = l_List_reverse___redArg(v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_852_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
return v___x_847_;
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___y_673_);
v_a_857_ = lean_ctor_get(v___y_844_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___y_844_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___y_844_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___y_844_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
else
{
goto v___jp_798_;
}
v___jp_725_:
{
lean_object* v___x_729_; double v___x_730_; double v___x_731_; double v___x_732_; double v___x_733_; double v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_729_ = lean_io_mono_nanos_now();
v___x_730_ = lean_float_of_nat(v___y_726_);
v___x_731_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_732_ = lean_float_div(v___x_730_, v___x_731_);
v___x_733_ = lean_float_of_nat(v___x_729_);
v___x_734_ = lean_float_div(v___x_733_, v___x_731_);
v___x_735_ = lean_box_float(v___x_732_);
v___x_736_ = lean_box_float(v___x_734_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_a_728_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_669_, v___x_670_, v___x_671_, v_options_679_, v___x_724_, v___y_727_, v___f_672_, v___x_738_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___y_673_);
return v___x_739_;
}
v___jp_740_:
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_a_743_);
v___y_726_ = v___y_741_;
v___y_727_ = v___y_742_;
v_a_728_ = v___x_744_;
goto v___jp_725_;
}
v___jp_745_:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_a_748_);
v___y_726_ = v___y_746_;
v___y_727_ = v___y_747_;
v_a_728_ = v___x_749_;
goto v___jp_725_;
}
v___jp_750_:
{
if (lean_obj_tag(v___y_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_755_ = lean_ctor_get(v___y_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___y_754_, 1);
v___x_756_ = lean_box(0);
v___x_757_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_752_, v_hasTrace_681_, v_a_755_, v___x_756_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_List_reverse___redArg(v_a_758_);
v___y_746_ = v___y_751_;
v___y_747_ = v___y_753_;
v_a_748_ = v___x_759_;
goto v___jp_745_;
}
else
{
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_757_, 1);
v___y_746_ = v___y_751_;
v___y_747_ = v___y_753_;
v_a_748_ = v_a_760_;
goto v___jp_745_;
}
else
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_757_, 1);
v___y_741_ = v___y_751_;
v___y_742_ = v___y_753_;
v_a_743_ = v_a_761_;
goto v___jp_740_;
}
}
}
else
{
lean_object* v_a_762_; 
v_a_762_ = lean_ctor_get(v___y_754_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___y_754_, 1);
v___y_741_ = v___y_751_;
v___y_742_ = v___y_753_;
v_a_743_ = v_a_762_;
goto v___jp_740_;
}
}
v___jp_763_:
{
lean_object* v___x_767_; double v___x_768_; double v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_767_ = lean_io_get_num_heartbeats();
v___x_768_ = lean_float_of_nat(v___y_764_);
v___x_769_ = lean_float_of_nat(v___x_767_);
v___x_770_ = lean_box_float(v___x_768_);
v___x_771_ = lean_box_float(v___x_769_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_a_766_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_669_, v___x_670_, v___x_671_, v_options_679_, v___x_724_, v___y_765_, v___f_672_, v___x_773_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___y_673_);
return v___x_774_;
}
v___jp_775_:
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_a_778_);
v___y_764_ = v___y_776_;
v___y_765_ = v___y_777_;
v_a_766_ = v___x_779_;
goto v___jp_763_;
}
v___jp_780_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_a_783_);
v___y_764_ = v___y_781_;
v___y_765_ = v___y_782_;
v_a_766_ = v___x_784_;
goto v___jp_763_;
}
v___jp_785_:
{
if (lean_obj_tag(v___y_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___y_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___y_789_, 1);
v___x_791_ = lean_box(0);
v___x_792_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_787_, v_a_790_, v___x_791_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_List_reverse___redArg(v_a_793_);
v___y_781_ = v___y_786_;
v___y_782_ = v___y_788_;
v_a_783_ = v___x_794_;
goto v___jp_780_;
}
else
{
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_792_, 1);
v___y_781_ = v___y_786_;
v___y_782_ = v___y_788_;
v_a_783_ = v_a_795_;
goto v___jp_780_;
}
else
{
lean_object* v_a_796_; 
v_a_796_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_792_, 1);
v___y_776_ = v___y_786_;
v___y_777_ = v___y_788_;
v_a_778_ = v_a_796_;
goto v___jp_775_;
}
}
}
else
{
lean_object* v_a_797_; 
v_a_797_ = lean_ctor_get(v___y_789_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___y_789_, 1);
v___y_776_ = v___y_786_;
v___y_777_ = v___y_788_;
v_a_778_ = v_a_797_;
goto v___jp_775_;
}
}
v___jp_798_:
{
lean_object* v___x_799_; lean_object* v_a_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_799_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_676_);
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = l_Lean_trace_profiler_useHeartbeats;
v___x_802_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_679_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v_transparency_805_; uint8_t v___x_806_; 
v___x_803_ = lean_io_mono_nanos_now();
v___x_804_ = l_Lean_Meta_Context_config(v___y_673_);
v_transparency_805_ = lean_ctor_get_uint8(v___x_804_, 9);
lean_dec_ref(v___x_804_);
v___x_806_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_805_, v_transparency_664_);
if (v___x_806_ == 0)
{
lean_object* v_keyedConfig_807_; uint8_t v_trackZetaDelta_808_; lean_object* v_zetaDeltaSet_809_; lean_object* v_lctx_810_; lean_object* v_localInstances_811_; lean_object* v_defEqCtx_x3f_812_; lean_object* v_synthPendingDepth_813_; lean_object* v_customCanUnfoldPredicate_x3f_814_; uint8_t v_univApprox_815_; uint8_t v_inTypeClassResolution_816_; uint8_t v_cacheInferType_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_keyedConfig_807_ = lean_ctor_get(v___y_673_, 0);
v_trackZetaDelta_808_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7);
v_zetaDeltaSet_809_ = lean_ctor_get(v___y_673_, 1);
v_lctx_810_ = lean_ctor_get(v___y_673_, 2);
v_localInstances_811_ = lean_ctor_get(v___y_673_, 3);
v_defEqCtx_x3f_812_ = lean_ctor_get(v___y_673_, 4);
v_synthPendingDepth_813_ = lean_ctor_get(v___y_673_, 5);
v_customCanUnfoldPredicate_x3f_814_ = lean_ctor_get(v___y_673_, 6);
v_univApprox_815_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_816_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 2);
v_cacheInferType_817_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_807_);
v___x_818_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_664_, v_keyedConfig_807_);
lean_inc(v_customCanUnfoldPredicate_x3f_814_);
lean_inc(v_synthPendingDepth_813_);
lean_inc(v_defEqCtx_x3f_812_);
lean_inc_ref(v_localInstances_811_);
lean_inc_ref(v_lctx_810_);
lean_inc(v_zetaDeltaSet_809_);
v___x_819_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_zetaDeltaSet_809_);
lean_ctor_set(v___x_819_, 2, v_lctx_810_);
lean_ctor_set(v___x_819_, 3, v_localInstances_811_);
lean_ctor_set(v___x_819_, 4, v_defEqCtx_x3f_812_);
lean_ctor_set(v___x_819_, 5, v_synthPendingDepth_813_);
lean_ctor_set(v___x_819_, 6, v_customCanUnfoldPredicate_x3f_814_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*7, v_trackZetaDelta_808_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*7 + 1, v_univApprox_815_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*7 + 2, v_inTypeClassResolution_816_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*7 + 3, v_cacheInferType_817_);
v___x_820_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___x_819_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref_known(v___x_819_, 7);
v___y_751_ = v___x_803_;
v___y_752_ = v___x_802_;
v___y_753_ = v_a_800_;
v___y_754_ = v___x_820_;
goto v___jp_750_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
v___y_751_ = v___x_803_;
v___y_752_ = v___x_802_;
v___y_753_ = v_a_800_;
v___y_754_ = v___x_821_;
goto v___jp_750_;
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v_transparency_824_; uint8_t v___x_825_; 
v___x_822_ = lean_io_get_num_heartbeats();
v___x_823_ = l_Lean_Meta_Context_config(v___y_673_);
v_transparency_824_ = lean_ctor_get_uint8(v___x_823_, 9);
lean_dec_ref(v___x_823_);
v___x_825_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_824_, v_transparency_664_);
if (v___x_825_ == 0)
{
lean_object* v_keyedConfig_826_; uint8_t v_trackZetaDelta_827_; lean_object* v_zetaDeltaSet_828_; lean_object* v_lctx_829_; lean_object* v_localInstances_830_; lean_object* v_defEqCtx_x3f_831_; lean_object* v_synthPendingDepth_832_; lean_object* v_customCanUnfoldPredicate_x3f_833_; uint8_t v_univApprox_834_; uint8_t v_inTypeClassResolution_835_; uint8_t v_cacheInferType_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_keyedConfig_826_ = lean_ctor_get(v___y_673_, 0);
v_trackZetaDelta_827_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7);
v_zetaDeltaSet_828_ = lean_ctor_get(v___y_673_, 1);
v_lctx_829_ = lean_ctor_get(v___y_673_, 2);
v_localInstances_830_ = lean_ctor_get(v___y_673_, 3);
v_defEqCtx_x3f_831_ = lean_ctor_get(v___y_673_, 4);
v_synthPendingDepth_832_ = lean_ctor_get(v___y_673_, 5);
v_customCanUnfoldPredicate_x3f_833_ = lean_ctor_get(v___y_673_, 6);
v_univApprox_834_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_835_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 2);
v_cacheInferType_836_ = lean_ctor_get_uint8(v___y_673_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_826_);
v___x_837_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_664_, v_keyedConfig_826_);
lean_inc(v_customCanUnfoldPredicate_x3f_833_);
lean_inc(v_synthPendingDepth_832_);
lean_inc(v_defEqCtx_x3f_831_);
lean_inc_ref(v_localInstances_830_);
lean_inc_ref(v_lctx_829_);
lean_inc(v_zetaDeltaSet_828_);
v___x_838_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_zetaDeltaSet_828_);
lean_ctor_set(v___x_838_, 2, v_lctx_829_);
lean_ctor_set(v___x_838_, 3, v_localInstances_830_);
lean_ctor_set(v___x_838_, 4, v_defEqCtx_x3f_831_);
lean_ctor_set(v___x_838_, 5, v_synthPendingDepth_832_);
lean_ctor_set(v___x_838_, 6, v_customCanUnfoldPredicate_x3f_833_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*7, v_trackZetaDelta_827_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*7 + 1, v_univApprox_834_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*7 + 2, v_inTypeClassResolution_835_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*7 + 3, v_cacheInferType_836_);
v___x_839_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___x_838_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref_known(v___x_838_, 7);
v___y_786_ = v___x_822_;
v___y_787_ = v___x_802_;
v___y_788_ = v_a_800_;
v___y_789_ = v___x_839_;
goto v___jp_785_;
}
else
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_MVarId_apply(v_g_665_, v_e_666_, v_cfg_667_, v___x_668_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
v___y_786_ = v___x_822_;
v___y_787_ = v___x_802_;
v___y_788_ = v_a_800_;
v___y_789_ = v___x_840_;
goto v___jp_785_;
}
}
}
}
v___jp_682_:
{
if (lean_obj_tag(v___y_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_a_684_ = lean_ctor_get(v___y_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___y_683_, 1);
v___x_685_ = lean_box(0);
v___x_686_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_681_, v_a_684_, v___x_685_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___y_673_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_List_reverse___redArg(v_a_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
return v___x_686_;
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___y_673_);
v_a_696_ = lean_ctor_get(v___y_683_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___y_683_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___y_683_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___y_683_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_883_, lean_object* v_g_884_, lean_object* v_e_885_, lean_object* v_cfg_886_, lean_object* v___x_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v___f_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v_transparency_boxed_897_; uint8_t v___x_14422__boxed_898_; lean_object* v_res_899_; 
v_transparency_boxed_897_ = lean_unbox(v_transparency_883_);
v___x_14422__boxed_898_ = lean_unbox(v___x_889_);
v_res_899_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_897_, v_g_884_, v_e_885_, v_cfg_886_, v___x_887_, v___x_888_, v___x_14422__boxed_898_, v___x_890_, v___f_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_901_, lean_object* v_g_902_, lean_object* v_cfg_903_, lean_object* v_e_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___f_917_; lean_object* v___x_918_; 
lean_inc_ref(v_e_904_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_910_, 0, v_e_904_);
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_912_ = lean_box(0);
v___x_913_ = 1;
v___x_914_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_915_ = lean_box(v_transparency_901_);
v___x_916_ = lean_box(v___x_913_);
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_917_, 0, v___x_915_);
lean_closure_set(v___f_917_, 1, v_g_902_);
lean_closure_set(v___f_917_, 2, v_e_904_);
lean_closure_set(v___f_917_, 3, v_cfg_903_);
lean_closure_set(v___f_917_, 4, v___x_912_);
lean_closure_set(v___f_917_, 5, v___x_911_);
lean_closure_set(v___f_917_, 6, v___x_916_);
lean_closure_set(v___f_917_, 7, v___x_914_);
lean_closure_set(v___f_917_, 8, v___f_910_);
v___x_918_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_917_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_919_, lean_object* v_g_920_, lean_object* v_cfg_921_, lean_object* v_e_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_transparency_boxed_928_; lean_object* v_res_929_; 
v_transparency_boxed_928_ = lean_unbox(v_transparency_919_);
v_res_929_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_928_, v_g_920_, v_cfg_921_, v_e_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_930_, uint8_t v_transparency_931_, lean_object* v_lemmas_932_, lean_object* v_g_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_932_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_948_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_948_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_942_ = lean_box(v_transparency_931_);
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_943_, 0, v___x_942_);
lean_closure_set(v___f_943_, 1, v_g_933_);
lean_closure_set(v___f_943_, 2, v_cfg_930_);
v___x_944_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_944_, 0, lean_box(0));
lean_closure_set(v___x_944_, 1, lean_box(0));
lean_closure_set(v___x_944_, 2, v___f_943_);
lean_closure_set(v___x_944_, 3, v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_944_);
v___x_946_ = v___x_940_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_g_933_);
lean_dec_ref(v_cfg_930_);
v_a_949_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_937_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_937_);
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
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_957_, lean_object* v_transparency_958_, lean_object* v_lemmas_959_, lean_object* v_g_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
uint8_t v_transparency_boxed_964_; lean_object* v_res_965_; 
v_transparency_boxed_964_ = lean_unbox(v_transparency_958_);
v_res_965_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_957_, v_transparency_boxed_964_, v_lemmas_959_, v_g_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec(v_a_961_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_966_, uint8_t v_transparency_967_, lean_object* v_lemmas_968_, lean_object* v_g_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_966_, v_transparency_967_, v_lemmas_968_, v_g_969_, v_a_971_, v_a_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_976_, lean_object* v_transparency_977_, lean_object* v_lemmas_978_, lean_object* v_g_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
uint8_t v_transparency_boxed_985_; lean_object* v_res_986_; 
v_transparency_boxed_985_ = lean_unbox(v_transparency_977_);
v_res_986_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_976_, v_transparency_boxed_985_, v_lemmas_978_, v_g_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_987_, lean_object* v_x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_988_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_995_, v_x_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1003_, uint8_t v_transparency_1004_, lean_object* v_lemmas_1005_, lean_object* v_g_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1003_, v_transparency_1004_, v_lemmas_1005_, v_g_1006_, v_a_1008_, v_a_1010_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = l_Lean_Meta_Iterator_head___redArg(v_a_1013_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1012_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1012_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1023_, lean_object* v_transparency_1024_, lean_object* v_lemmas_1025_, lean_object* v_g_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
uint8_t v_transparency_boxed_1032_; lean_object* v_res_1033_; 
v_transparency_boxed_1032_ = lean_unbox(v_transparency_1024_);
v_res_1033_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1023_, v_transparency_boxed_1032_, v_lemmas_1025_, v_g_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1034_){
_start:
{
lean_object* v_toApplyRulesConfig_1035_; lean_object* v_toBacktrackConfig_1036_; 
v_toApplyRulesConfig_1035_ = lean_ctor_get(v_x_1034_, 0);
v_toBacktrackConfig_1036_ = lean_ctor_get(v_toApplyRulesConfig_1035_, 0);
lean_inc_ref(v_toBacktrackConfig_1036_);
return v_toBacktrackConfig_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1037_);
lean_dec_ref(v_x_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1041_, lean_object* v_discharge_1042_, lean_object* v_g_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v_g_1043_);
v___x_1049_ = lean_apply_6(v_test_1041_, v_g_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, lean_box(0));
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1060_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_unbox(v_a_1050_);
lean_dec(v_a_1050_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_del_object(v___x_1052_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
v___x_1055_ = lean_apply_6(v_discharge_1042_, v_g_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, lean_box(0));
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_dec(v_g_1043_);
lean_dec_ref(v_discharge_1042_);
v___x_1056_ = lean_box(0);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1056_);
v___x_1058_ = v___x_1052_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
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
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_g_1043_);
lean_dec_ref(v_discharge_1042_);
v_a_1061_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1049_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1049_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1069_, lean_object* v_discharge_1070_, lean_object* v_g_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1069_, v_discharge_1070_, v_g_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1078_, lean_object* v_test_1079_){
_start:
{
lean_object* v_toApplyRulesConfig_1080_; lean_object* v_toBacktrackConfig_1081_; uint8_t v_backtracking_1082_; uint8_t v_intro_1083_; uint8_t v_constructor_1084_; uint8_t v_suggestions_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1117_; 
v_toApplyRulesConfig_1080_ = lean_ctor_get(v_cfg_1078_, 0);
lean_inc_ref(v_toApplyRulesConfig_1080_);
v_toBacktrackConfig_1081_ = lean_ctor_get(v_toApplyRulesConfig_1080_, 0);
lean_inc_ref(v_toBacktrackConfig_1081_);
v_backtracking_1082_ = lean_ctor_get_uint8(v_cfg_1078_, sizeof(void*)*1);
v_intro_1083_ = lean_ctor_get_uint8(v_cfg_1078_, sizeof(void*)*1 + 1);
v_constructor_1084_ = lean_ctor_get_uint8(v_cfg_1078_, sizeof(void*)*1 + 2);
v_suggestions_1085_ = lean_ctor_get_uint8(v_cfg_1078_, sizeof(void*)*1 + 3);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_cfg_1078_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_cfg_1078_, 0);
lean_dec(v_unused_1118_);
v___x_1087_ = v_cfg_1078_;
v_isShared_1088_ = v_isSharedCheck_1117_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_cfg_1078_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1117_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_toApplyConfig_1089_; uint8_t v_transparency_1090_; uint8_t v_symm_1091_; uint8_t v_exfalso_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1115_; 
v_toApplyConfig_1089_ = lean_ctor_get(v_toApplyRulesConfig_1080_, 1);
v_transparency_1090_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1080_, sizeof(void*)*2);
v_symm_1091_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1080_, sizeof(void*)*2 + 1);
v_exfalso_1092_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1080_, sizeof(void*)*2 + 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_toApplyRulesConfig_1080_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v_toApplyRulesConfig_1080_, 0);
lean_dec(v_unused_1116_);
v___x_1094_ = v_toApplyRulesConfig_1080_;
v_isShared_1095_ = v_isSharedCheck_1115_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_toApplyConfig_1089_);
lean_dec(v_toApplyRulesConfig_1080_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1115_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_maxDepth_1096_; lean_object* v_proc_1097_; lean_object* v_suspend_1098_; lean_object* v_discharge_1099_; uint8_t v_commitIndependentGoals_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1114_; 
v_maxDepth_1096_ = lean_ctor_get(v_toBacktrackConfig_1081_, 0);
v_proc_1097_ = lean_ctor_get(v_toBacktrackConfig_1081_, 1);
v_suspend_1098_ = lean_ctor_get(v_toBacktrackConfig_1081_, 2);
v_discharge_1099_ = lean_ctor_get(v_toBacktrackConfig_1081_, 3);
v_commitIndependentGoals_1100_ = lean_ctor_get_uint8(v_toBacktrackConfig_1081_, sizeof(void*)*4);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_toBacktrackConfig_1081_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1102_ = v_toBacktrackConfig_1081_;
v_isShared_1103_ = v_isSharedCheck_1114_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_discharge_1099_);
lean_inc(v_suspend_1098_);
lean_inc(v_proc_1097_);
lean_inc(v_maxDepth_1096_);
lean_dec(v_toBacktrackConfig_1081_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1114_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___x_1106_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1104_, 0, v_test_1079_);
lean_closure_set(v___f_1104_, 1, v_discharge_1099_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v___f_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_maxDepth_1096_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_proc_1097_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_suspend_1098_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___f_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*4, v_commitIndependentGoals_1100_);
v___x_1106_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1106_);
v___x_1108_ = v___x_1094_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_toApplyConfig_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*2, v_transparency_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*2 + 1, v_symm_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*2 + 2, v_exfalso_1092_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1108_);
v___x_1110_ = v___x_1087_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*1, v_backtracking_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*1 + 1, v_intro_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*1 + 2, v_constructor_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*1 + 3, v_suggestions_1085_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1119_, lean_object* v_proc_1120_, lean_object* v_orig_1121_, lean_object* v_goals_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
if (lean_obj_tag(v_goals_1122_) == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_proc_1120_);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc_ref(v___y_1123_);
v___x_1128_ = lean_apply_7(v_proc_1119_, v_orig_1121_, v_goals_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, lean_box(0));
return v___x_1128_;
}
else
{
lean_object* v_head_1129_; lean_object* v_tail_1130_; lean_object* v___x_1131_; 
v_head_1129_ = lean_ctor_get(v_goals_1122_, 0);
v_tail_1130_ = lean_ctor_get(v_goals_1122_, 1);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc_ref(v___y_1123_);
lean_inc(v_head_1129_);
v___x_1131_ = lean_apply_6(v_proc_1120_, v_head_1129_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, lean_box(0));
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1141_; 
lean_inc(v_tail_1130_);
lean_dec_ref_known(v_goals_1122_, 2);
lean_dec(v_orig_1121_);
lean_dec_ref(v_proc_1119_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = l_List_appendTR___redArg(v_a_1132_, v_tail_1130_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1154_; 
v_a_1142_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1144_ = v___x_1131_;
v_isShared_1145_ = v_isSharedCheck_1154_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1131_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1154_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
uint8_t v___y_1147_; uint8_t v___x_1152_; 
v___x_1152_ = l_Lean_Exception_isInterrupt(v_a_1142_);
if (v___x_1152_ == 0)
{
uint8_t v___x_1153_; 
lean_inc(v_a_1142_);
v___x_1153_ = l_Lean_Exception_isRuntime(v_a_1142_);
v___y_1147_ = v___x_1153_;
goto v___jp_1146_;
}
else
{
v___y_1147_ = v___x_1152_;
goto v___jp_1146_;
}
v___jp_1146_:
{
if (v___y_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_del_object(v___x_1144_);
lean_dec(v_a_1142_);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc_ref(v___y_1123_);
v___x_1148_ = lean_apply_7(v_proc_1119_, v_orig_1121_, v_goals_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, lean_box(0));
return v___x_1148_;
}
else
{
lean_object* v___x_1150_; 
lean_dec_ref_known(v_goals_1122_, 2);
lean_dec(v_orig_1121_);
lean_dec_ref(v_proc_1119_);
if (v_isShared_1145_ == 0)
{
v___x_1150_ = v___x_1144_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1142_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1155_, lean_object* v_proc_1156_, lean_object* v_orig_1157_, lean_object* v_goals_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1155_, v_proc_1156_, v_orig_1157_, v_goals_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1165_, lean_object* v_proc_1166_){
_start:
{
lean_object* v_toApplyRulesConfig_1167_; lean_object* v_toBacktrackConfig_1168_; uint8_t v_backtracking_1169_; uint8_t v_intro_1170_; uint8_t v_constructor_1171_; uint8_t v_suggestions_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1204_; 
v_toApplyRulesConfig_1167_ = lean_ctor_get(v_cfg_1165_, 0);
lean_inc_ref(v_toApplyRulesConfig_1167_);
v_toBacktrackConfig_1168_ = lean_ctor_get(v_toApplyRulesConfig_1167_, 0);
lean_inc_ref(v_toBacktrackConfig_1168_);
v_backtracking_1169_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*1);
v_intro_1170_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*1 + 1);
v_constructor_1171_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*1 + 2);
v_suggestions_1172_ = lean_ctor_get_uint8(v_cfg_1165_, sizeof(void*)*1 + 3);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_cfg_1165_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v_cfg_1165_, 0);
lean_dec(v_unused_1205_);
v___x_1174_ = v_cfg_1165_;
v_isShared_1175_ = v_isSharedCheck_1204_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_cfg_1165_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1204_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_toApplyConfig_1176_; uint8_t v_transparency_1177_; uint8_t v_symm_1178_; uint8_t v_exfalso_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1202_; 
v_toApplyConfig_1176_ = lean_ctor_get(v_toApplyRulesConfig_1167_, 1);
v_transparency_1177_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1167_, sizeof(void*)*2);
v_symm_1178_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1167_, sizeof(void*)*2 + 1);
v_exfalso_1179_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1167_, sizeof(void*)*2 + 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_toApplyRulesConfig_1167_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_toApplyRulesConfig_1167_, 0);
lean_dec(v_unused_1203_);
v___x_1181_ = v_toApplyRulesConfig_1167_;
v_isShared_1182_ = v_isSharedCheck_1202_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_toApplyConfig_1176_);
lean_dec(v_toApplyRulesConfig_1167_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1202_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_maxDepth_1183_; lean_object* v_proc_1184_; lean_object* v_suspend_1185_; lean_object* v_discharge_1186_; uint8_t v_commitIndependentGoals_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1201_; 
v_maxDepth_1183_ = lean_ctor_get(v_toBacktrackConfig_1168_, 0);
v_proc_1184_ = lean_ctor_get(v_toBacktrackConfig_1168_, 1);
v_suspend_1185_ = lean_ctor_get(v_toBacktrackConfig_1168_, 2);
v_discharge_1186_ = lean_ctor_get(v_toBacktrackConfig_1168_, 3);
v_commitIndependentGoals_1187_ = lean_ctor_get_uint8(v_toBacktrackConfig_1168_, sizeof(void*)*4);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_toBacktrackConfig_1168_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1189_ = v_toBacktrackConfig_1168_;
v_isShared_1190_ = v_isSharedCheck_1201_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_discharge_1186_);
lean_inc(v_suspend_1185_);
lean_inc(v_proc_1184_);
lean_inc(v_maxDepth_1183_);
lean_dec(v_toBacktrackConfig_1168_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1201_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___f_1191_; lean_object* v___x_1193_; 
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1191_, 0, v_proc_1184_);
lean_closure_set(v___f_1191_, 1, v_proc_1166_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___f_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_maxDepth_1183_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___f_1191_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_suspend_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_discharge_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*4, v_commitIndependentGoals_1187_);
v___x_1193_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1193_);
v___x_1195_ = v___x_1181_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_toApplyConfig_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1199_, sizeof(void*)*2, v_transparency_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1199_, sizeof(void*)*2 + 1, v_symm_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1199_, sizeof(void*)*2 + 2, v_exfalso_1179_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1195_);
v___x_1197_ = v___x_1174_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*1, v_backtracking_1169_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*1 + 1, v_intro_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*1 + 2, v_constructor_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*1 + 3, v_suggestions_1172_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = 1;
v___x_1213_ = l_Lean_Meta_intro1Core(v_g_1206_, v___x_1212_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1231_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
v_snd_1218_ = lean_ctor_get(v_a_1214_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_a_1214_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_a_1214_, 0);
lean_dec(v_unused_1230_);
v___x_1220_ = v_a_1214_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_dec(v_a_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_box(0);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 1, v___x_1222_);
lean_ctor_set(v___x_1220_, 0, v_snd_1218_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_snd_1218_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1224_);
v___x_1226_ = v___x_1216_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
v_a_1232_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1213_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1213_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1248_){
_start:
{
lean_object* v___f_1249_; lean_object* v___x_1250_; 
v___f_1249_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1250_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1248_, v___f_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v_ks_1255_; lean_object* v_vs_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1280_; 
v_ks_1255_ = lean_ctor_get(v_x_1251_, 0);
v_vs_1256_ = lean_ctor_get(v_x_1251_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1258_ = v_x_1251_;
v_isShared_1259_ = v_isSharedCheck_1280_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_vs_1256_);
lean_inc(v_ks_1255_);
lean_dec(v_x_1251_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1280_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = lean_array_get_size(v_ks_1255_);
v___x_1261_ = lean_nat_dec_lt(v_x_1252_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec(v_x_1252_);
v___x_1262_ = lean_array_push(v_ks_1255_, v_x_1253_);
v___x_1263_ = lean_array_push(v_vs_1256_, v_x_1254_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1263_);
lean_ctor_set(v___x_1258_, 0, v___x_1262_);
v___x_1265_ = v___x_1258_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_object* v_k_x27_1267_; uint8_t v___x_1268_; 
v_k_x27_1267_ = lean_array_fget_borrowed(v_ks_1255_, v_x_1252_);
v___x_1268_ = l_Lean_instBEqMVarId_beq(v_x_1253_, v_k_x27_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1270_; 
if (v_isShared_1259_ == 0)
{
v___x_1270_ = v___x_1258_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_ks_1255_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_vs_1256_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_x_1252_, v___x_1271_);
lean_dec(v_x_1252_);
v_x_1251_ = v___x_1270_;
v_x_1252_ = v___x_1272_;
goto _start;
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_array_fset(v_ks_1255_, v_x_1252_, v_x_1253_);
v___x_1276_ = lean_array_fset(v_vs_1256_, v_x_1252_, v_x_1254_);
lean_dec(v_x_1252_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1276_);
lean_ctor_set(v___x_1258_, 0, v___x_1275_);
v___x_1278_ = v___x_1258_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1281_, lean_object* v_k_1282_, lean_object* v_v_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1281_, v___x_1284_, v_k_1282_, v_v_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1287_, size_t v_x_1288_, size_t v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
lean_object* v_es_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v_j_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_es_1292_ = lean_ctor_get(v_x_1287_, 0);
v___x_1293_ = ((size_t)31ULL);
v___x_1294_ = lean_usize_land(v_x_1288_, v___x_1293_);
v_j_1295_ = lean_usize_to_nat(v___x_1294_);
v___x_1296_ = lean_array_get_size(v_es_1292_);
v___x_1297_ = lean_nat_dec_lt(v_j_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_dec(v_j_1295_);
lean_dec(v_x_1291_);
lean_dec(v_x_1290_);
return v_x_1287_;
}
else
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1336_; 
lean_inc_ref(v_es_1292_);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_x_1287_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_x_1287_, 0);
lean_dec(v_unused_1337_);
v___x_1299_ = v_x_1287_;
v_isShared_1300_ = v_isSharedCheck_1336_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_x_1287_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1336_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_v_1301_; lean_object* v___x_1302_; lean_object* v_xs_x27_1303_; lean_object* v___y_1305_; 
v_v_1301_ = lean_array_fget(v_es_1292_, v_j_1295_);
v___x_1302_ = lean_box(0);
v_xs_x27_1303_ = lean_array_fset(v_es_1292_, v_j_1295_, v___x_1302_);
switch(lean_obj_tag(v_v_1301_))
{
case 0:
{
lean_object* v_key_1310_; lean_object* v_val_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1321_; 
v_key_1310_ = lean_ctor_get(v_v_1301_, 0);
v_val_1311_ = lean_ctor_get(v_v_1301_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1313_ = v_v_1301_;
v_isShared_1314_ = v_isSharedCheck_1321_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_val_1311_);
lean_inc(v_key_1310_);
lean_dec(v_v_1301_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1321_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_instBEqMVarId_beq(v_x_1290_, v_key_1310_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_del_object(v___x_1313_);
v___x_1316_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1310_, v_val_1311_, v_x_1290_, v_x_1291_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___y_1305_ = v___x_1317_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1319_; 
lean_dec(v_val_1311_);
lean_dec(v_key_1310_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v_x_1291_);
lean_ctor_set(v___x_1313_, 0, v_x_1290_);
v___x_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_x_1290_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_x_1291_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
v___y_1305_ = v___x_1319_;
goto v___jp_1304_;
}
}
}
}
case 1:
{
lean_object* v_node_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1334_; 
v_node_1322_ = lean_ctor_get(v_v_1301_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1324_ = v_v_1301_;
v_isShared_1325_ = v_isSharedCheck_1334_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_node_1322_);
lean_dec(v_v_1301_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1334_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1326_ = ((size_t)5ULL);
v___x_1327_ = lean_usize_shift_right(v_x_1288_, v___x_1326_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_x_1289_, v___x_1328_);
v___x_1330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1322_, v___x_1327_, v___x_1329_, v_x_1290_, v_x_1291_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1330_);
v___x_1332_ = v___x_1324_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
v___y_1305_ = v___x_1332_;
goto v___jp_1304_;
}
}
}
default: 
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_x_1290_);
lean_ctor_set(v___x_1335_, 1, v_x_1291_);
v___y_1305_ = v___x_1335_;
goto v___jp_1304_;
}
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_array_fset(v_xs_x27_1303_, v_j_1295_, v___y_1305_);
lean_dec(v_j_1295_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1306_);
v___x_1308_ = v___x_1299_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
lean_object* v_ks_1338_; lean_object* v_vs_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1357_; 
v_ks_1338_ = lean_ctor_get(v_x_1287_, 0);
v_vs_1339_ = lean_ctor_get(v_x_1287_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_x_1287_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1341_ = v_x_1287_;
v_isShared_1342_ = v_isSharedCheck_1357_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_vs_1339_);
lean_inc(v_ks_1338_);
lean_dec(v_x_1287_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1357_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_ks_1338_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_vs_1339_);
v___x_1344_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v_newNode_1345_; size_t v___x_1346_; uint8_t v___x_1347_; 
v_newNode_1345_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1344_, v_x_1290_, v_x_1291_);
v___x_1346_ = ((size_t)7ULL);
v___x_1347_ = lean_usize_dec_le(v___x_1346_, v_x_1289_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1345_);
v___x_1349_ = lean_unsigned_to_nat(4u);
v___x_1350_ = lean_nat_dec_lt(v___x_1348_, v___x_1349_);
lean_dec(v___x_1348_);
if (v___x_1350_ == 0)
{
lean_object* v_ks_1351_; lean_object* v_vs_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_ks_1351_ = lean_ctor_get(v_newNode_1345_, 0);
lean_inc_ref(v_ks_1351_);
v_vs_1352_ = lean_ctor_get(v_newNode_1345_, 1);
lean_inc_ref(v_vs_1352_);
lean_dec_ref(v_newNode_1345_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1289_, v_ks_1351_, v_vs_1352_, v___x_1353_, v___x_1354_);
lean_dec_ref(v_vs_1352_);
lean_dec_ref(v_ks_1351_);
return v___x_1355_;
}
else
{
return v_newNode_1345_;
}
}
else
{
return v_newNode_1345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1358_, lean_object* v_keys_1359_, lean_object* v_vals_1360_, lean_object* v_i_1361_, lean_object* v_entries_1362_){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_array_get_size(v_keys_1359_);
v___x_1364_ = lean_nat_dec_lt(v_i_1361_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_dec(v_i_1361_);
return v_entries_1362_;
}
else
{
lean_object* v_k_1365_; lean_object* v_v_1366_; uint64_t v___x_1367_; size_t v_h_1368_; size_t v___x_1369_; lean_object* v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v_h_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_k_1365_ = lean_array_fget_borrowed(v_keys_1359_, v_i_1361_);
v_v_1366_ = lean_array_fget_borrowed(v_vals_1360_, v_i_1361_);
v___x_1367_ = l_Lean_instHashableMVarId_hash(v_k_1365_);
v_h_1368_ = lean_uint64_to_usize(v___x_1367_);
v___x_1369_ = ((size_t)5ULL);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_sub(v_depth_1358_, v___x_1371_);
v___x_1373_ = lean_usize_mul(v___x_1369_, v___x_1372_);
v_h_1374_ = lean_usize_shift_right(v_h_1368_, v___x_1373_);
v___x_1375_ = lean_nat_add(v_i_1361_, v___x_1370_);
lean_dec(v_i_1361_);
lean_inc(v_v_1366_);
lean_inc(v_k_1365_);
v___x_1376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1362_, v_h_1374_, v_depth_1358_, v_k_1365_, v_v_1366_);
v_i_1361_ = v___x_1375_;
v_entries_1362_ = v___x_1376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_i_1381_, lean_object* v_entries_1382_){
_start:
{
size_t v_depth_boxed_1383_; lean_object* v_res_1384_; 
v_depth_boxed_1383_ = lean_unbox_usize(v_depth_1378_);
lean_dec(v_depth_1378_);
v_res_1384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1383_, v_keys_1379_, v_vals_1380_, v_i_1381_, v_entries_1382_);
lean_dec_ref(v_vals_1380_);
lean_dec_ref(v_keys_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
size_t v_x_832__boxed_1390_; size_t v_x_833__boxed_1391_; lean_object* v_res_1392_; 
v_x_832__boxed_1390_ = lean_unbox_usize(v_x_1386_);
lean_dec(v_x_1386_);
v_x_833__boxed_1391_ = lean_unbox_usize(v_x_1387_);
lean_dec(v_x_1387_);
v_res_1392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1385_, v_x_832__boxed_1390_, v_x_833__boxed_1391_, v_x_1388_, v_x_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
uint64_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = l_Lean_instHashableMVarId_hash(v_x_1394_);
v___x_1397_ = lean_uint64_to_usize(v___x_1396_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1393_, v___x_1397_, v___x_1398_, v_x_1394_, v_x_1395_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1400_, lean_object* v_val_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v_cache_1406_; lean_object* v_zetaDeltaFVarIds_1407_; lean_object* v_postponed_1408_; lean_object* v_diag_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1438_; 
v___x_1404_ = lean_st_ref_take(v___y_1402_);
v_mctx_1405_ = lean_ctor_get(v___x_1404_, 0);
v_cache_1406_ = lean_ctor_get(v___x_1404_, 1);
v_zetaDeltaFVarIds_1407_ = lean_ctor_get(v___x_1404_, 2);
v_postponed_1408_ = lean_ctor_get(v___x_1404_, 3);
v_diag_1409_ = lean_ctor_get(v___x_1404_, 4);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1411_ = v___x_1404_;
v_isShared_1412_ = v_isSharedCheck_1438_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_diag_1409_);
lean_inc(v_postponed_1408_);
lean_inc(v_zetaDeltaFVarIds_1407_);
lean_inc(v_cache_1406_);
lean_inc(v_mctx_1405_);
lean_dec(v___x_1404_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1438_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_depth_1413_; lean_object* v_levelAssignDepth_1414_; lean_object* v_lmvarCounter_1415_; lean_object* v_mvarCounter_1416_; lean_object* v_lDecls_1417_; lean_object* v_decls_1418_; lean_object* v_userNames_1419_; lean_object* v_lAssignment_1420_; lean_object* v_eAssignment_1421_; lean_object* v_dAssignment_1422_; lean_object* v_instanceTypedMVars_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1437_; 
v_depth_1413_ = lean_ctor_get(v_mctx_1405_, 0);
v_levelAssignDepth_1414_ = lean_ctor_get(v_mctx_1405_, 1);
v_lmvarCounter_1415_ = lean_ctor_get(v_mctx_1405_, 2);
v_mvarCounter_1416_ = lean_ctor_get(v_mctx_1405_, 3);
v_lDecls_1417_ = lean_ctor_get(v_mctx_1405_, 4);
v_decls_1418_ = lean_ctor_get(v_mctx_1405_, 5);
v_userNames_1419_ = lean_ctor_get(v_mctx_1405_, 6);
v_lAssignment_1420_ = lean_ctor_get(v_mctx_1405_, 7);
v_eAssignment_1421_ = lean_ctor_get(v_mctx_1405_, 8);
v_dAssignment_1422_ = lean_ctor_get(v_mctx_1405_, 9);
v_instanceTypedMVars_1423_ = lean_ctor_get(v_mctx_1405_, 10);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_mctx_1405_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1425_ = v_mctx_1405_;
v_isShared_1426_ = v_isSharedCheck_1437_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_instanceTypedMVars_1423_);
lean_inc(v_dAssignment_1422_);
lean_inc(v_eAssignment_1421_);
lean_inc(v_lAssignment_1420_);
lean_inc(v_userNames_1419_);
lean_inc(v_decls_1418_);
lean_inc(v_lDecls_1417_);
lean_inc(v_mvarCounter_1416_);
lean_inc(v_lmvarCounter_1415_);
lean_inc(v_levelAssignDepth_1414_);
lean_inc(v_depth_1413_);
lean_dec(v_mctx_1405_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1437_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1421_, v_mvarId_1400_, v_val_1401_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 8, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_depth_1413_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_levelAssignDepth_1414_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_lmvarCounter_1415_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_mvarCounter_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_lDecls_1417_);
lean_ctor_set(v_reuseFailAlloc_1436_, 5, v_decls_1418_);
lean_ctor_set(v_reuseFailAlloc_1436_, 6, v_userNames_1419_);
lean_ctor_set(v_reuseFailAlloc_1436_, 7, v_lAssignment_1420_);
lean_ctor_set(v_reuseFailAlloc_1436_, 8, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1436_, 9, v_dAssignment_1422_);
lean_ctor_set(v_reuseFailAlloc_1436_, 10, v_instanceTypedMVars_1423_);
v___x_1429_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1429_);
v___x_1431_ = v___x_1411_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_cache_1406_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_zetaDeltaFVarIds_1407_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_postponed_1408_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v_diag_1409_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_st_ref_put(v___y_1402_, v___x_1431_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1439_, lean_object* v_val_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1439_, v_val_1440_, v___y_1441_);
lean_dec(v___y_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
lean_inc(v_g_1444_);
v___x_1450_ = l_Lean_MVarId_getType(v_g_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = lean_box(0);
v___x_1453_ = l_Lean_Meta_synthInstance(v_a_1451_, v___x_1452_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1444_, v_a_1454_, v___y_1446_);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1455_, 0);
lean_dec(v_unused_1464_);
v___x_1457_ = v___x_1455_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v___x_1455_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_g_1444_);
v_a_1465_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1453_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1453_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_g_1444_);
v_a_1473_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1450_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1450_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1489_){
_start:
{
lean_object* v___f_1490_; lean_object* v___x_1491_; 
v___f_1490_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1491_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1489_, v___f_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1492_, lean_object* v_val_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1492_, v_val_1493_, v___y_1495_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1500_, lean_object* v_val_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1500_, v_val_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1509_, v_x_1510_, v_x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1513_, lean_object* v_x_1514_, size_t v_x_1515_, size_t v_x_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1514_, v_x_1515_, v_x_1516_, v_x_1517_, v_x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
size_t v_x_1153__boxed_1526_; size_t v_x_1154__boxed_1527_; lean_object* v_res_1528_; 
v_x_1153__boxed_1526_ = lean_unbox_usize(v_x_1522_);
lean_dec(v_x_1522_);
v_x_1154__boxed_1527_ = lean_unbox_usize(v_x_1523_);
lean_dec(v_x_1523_);
v_res_1528_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1520_, v_x_1521_, v_x_1153__boxed_1526_, v_x_1154__boxed_1527_, v_x_1524_, v_x_1525_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1529_, lean_object* v_n_1530_, lean_object* v_k_1531_, lean_object* v_v_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1530_, v_k_1531_, v_v_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1534_, size_t v_depth_1535_, lean_object* v_keys_1536_, lean_object* v_vals_1537_, lean_object* v_heq_1538_, lean_object* v_i_1539_, lean_object* v_entries_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1535_, v_keys_1536_, v_vals_1537_, v_i_1539_, v_entries_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1542_, lean_object* v_depth_1543_, lean_object* v_keys_1544_, lean_object* v_vals_1545_, lean_object* v_heq_1546_, lean_object* v_i_1547_, lean_object* v_entries_1548_){
_start:
{
size_t v_depth_boxed_1549_; lean_object* v_res_1550_; 
v_depth_boxed_1549_ = lean_unbox_usize(v_depth_1543_);
lean_dec(v_depth_1543_);
v_res_1550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1542_, v_depth_boxed_1549_, v_keys_1544_, v_vals_1545_, v_heq_1546_, v_i_1547_, v_entries_1548_);
lean_dec_ref(v_vals_1545_);
lean_dec_ref(v_keys_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1552_, v_x_1553_, v_x_1554_, v_x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1557_, lean_object* v_discharge_1558_, lean_object* v_g_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
lean_inc(v_g_1559_);
v___x_1565_ = lean_apply_6(v_discharge_1557_, v_g_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, lean_box(0));
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec(v_g_1559_);
lean_dec_ref(v_discharge_1558_);
return v___x_1565_;
}
else
{
lean_object* v_a_1566_; uint8_t v___y_1568_; uint8_t v___x_1570_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
v___x_1570_ = l_Lean_Exception_isInterrupt(v_a_1566_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_Exception_isRuntime(v_a_1566_);
v___y_1568_ = v___x_1571_;
goto v___jp_1567_;
}
else
{
lean_dec(v_a_1566_);
v___y_1568_ = v___x_1570_;
goto v___jp_1567_;
}
v___jp_1567_:
{
if (v___y_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
v___x_1569_ = lean_apply_6(v_discharge_1558_, v_g_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, lean_box(0));
return v___x_1569_;
}
else
{
lean_dec(v_g_1559_);
lean_dec_ref(v_discharge_1558_);
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1572_, lean_object* v_discharge_1573_, lean_object* v_g_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1572_, v_discharge_1573_, v_g_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1581_, lean_object* v_discharge_1582_){
_start:
{
lean_object* v_toApplyRulesConfig_1583_; lean_object* v_toBacktrackConfig_1584_; uint8_t v_backtracking_1585_; uint8_t v_intro_1586_; uint8_t v_constructor_1587_; uint8_t v_suggestions_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1620_; 
v_toApplyRulesConfig_1583_ = lean_ctor_get(v_cfg_1581_, 0);
lean_inc_ref(v_toApplyRulesConfig_1583_);
v_toBacktrackConfig_1584_ = lean_ctor_get(v_toApplyRulesConfig_1583_, 0);
lean_inc_ref(v_toBacktrackConfig_1584_);
v_backtracking_1585_ = lean_ctor_get_uint8(v_cfg_1581_, sizeof(void*)*1);
v_intro_1586_ = lean_ctor_get_uint8(v_cfg_1581_, sizeof(void*)*1 + 1);
v_constructor_1587_ = lean_ctor_get_uint8(v_cfg_1581_, sizeof(void*)*1 + 2);
v_suggestions_1588_ = lean_ctor_get_uint8(v_cfg_1581_, sizeof(void*)*1 + 3);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_cfg_1581_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v_cfg_1581_, 0);
lean_dec(v_unused_1621_);
v___x_1590_ = v_cfg_1581_;
v_isShared_1591_ = v_isSharedCheck_1620_;
goto v_resetjp_1589_;
}
else
{
lean_dec(v_cfg_1581_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1620_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v_toApplyConfig_1592_; uint8_t v_transparency_1593_; uint8_t v_symm_1594_; uint8_t v_exfalso_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1618_; 
v_toApplyConfig_1592_ = lean_ctor_get(v_toApplyRulesConfig_1583_, 1);
v_transparency_1593_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1583_, sizeof(void*)*2);
v_symm_1594_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1583_, sizeof(void*)*2 + 1);
v_exfalso_1595_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1583_, sizeof(void*)*2 + 2);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_toApplyRulesConfig_1583_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_toApplyRulesConfig_1583_, 0);
lean_dec(v_unused_1619_);
v___x_1597_ = v_toApplyRulesConfig_1583_;
v_isShared_1598_ = v_isSharedCheck_1618_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_toApplyConfig_1592_);
lean_dec(v_toApplyRulesConfig_1583_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1618_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_maxDepth_1599_; lean_object* v_proc_1600_; lean_object* v_suspend_1601_; lean_object* v_discharge_1602_; uint8_t v_commitIndependentGoals_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1617_; 
v_maxDepth_1599_ = lean_ctor_get(v_toBacktrackConfig_1584_, 0);
v_proc_1600_ = lean_ctor_get(v_toBacktrackConfig_1584_, 1);
v_suspend_1601_ = lean_ctor_get(v_toBacktrackConfig_1584_, 2);
v_discharge_1602_ = lean_ctor_get(v_toBacktrackConfig_1584_, 3);
v_commitIndependentGoals_1603_ = lean_ctor_get_uint8(v_toBacktrackConfig_1584_, sizeof(void*)*4);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_toBacktrackConfig_1584_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1605_ = v_toBacktrackConfig_1584_;
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_discharge_1602_);
lean_inc(v_suspend_1601_);
lean_inc(v_proc_1600_);
lean_inc(v_maxDepth_1599_);
lean_dec(v_toBacktrackConfig_1584_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___f_1607_; lean_object* v___x_1609_; 
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1607_, 0, v_discharge_1582_);
lean_closure_set(v___f_1607_, 1, v_discharge_1602_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v___f_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_maxDepth_1599_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_proc_1600_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_suspend_1601_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v___f_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1616_, sizeof(void*)*4, v_commitIndependentGoals_1603_);
v___x_1609_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1609_);
v___x_1611_ = v___x_1597_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_toApplyConfig_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*2, v_transparency_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*2 + 1, v_symm_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*2 + 2, v_exfalso_1595_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1611_);
v___x_1613_ = v___x_1590_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*1, v_backtracking_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*1 + 1, v_intro_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*1 + 2, v_constructor_1587_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*1 + 3, v_suggestions_1588_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = 1;
v___x_1629_ = l_Lean_Meta_intro1Core(v_g_1622_, v___x_1628_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1648_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1648_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1648_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_snd_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1646_; 
v_snd_1634_ = lean_ctor_get(v_a_1630_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_a_1630_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_a_1630_, 0);
lean_dec(v_unused_1647_);
v___x_1636_ = v_a_1630_;
v_isShared_1637_ = v_isSharedCheck_1646_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_snd_1634_);
lean_dec(v_a_1630_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1646_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_box(0);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 1);
lean_ctor_set(v___x_1636_, 1, v___x_1638_);
lean_ctor_set(v___x_1636_, 0, v_snd_1634_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_snd_1634_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1641_);
v___x_1643_ = v___x_1632_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1629_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1629_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1665_){
_start:
{
lean_object* v___f_1666_; lean_object* v___x_1667_; 
v___f_1666_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1667_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1665_, v___f_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1679_ = l_Lean_MVarId_constructor(v_g_1672_, v___x_1678_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_a_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1679_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1679_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1705_){
_start:
{
lean_object* v___f_1706_; lean_object* v___x_1707_; 
v___f_1706_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1707_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1705_, v___f_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
lean_inc(v_g_1710_);
v___x_1716_ = l_Lean_MVarId_getType(v_g_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = lean_box(0);
v___x_1719_ = l_Lean_Meta_synthInstance(v_a_1717_, v___x_1718_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1729_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1710_, v_a_1720_, v___y_1712_);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1730_);
v___x_1723_ = v___x_1721_;
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v___x_1721_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_g_1710_);
v_a_1731_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1719_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1719_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_g_1710_);
v_a_1739_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1716_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1716_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1755_){
_start:
{
lean_object* v___f_1756_; lean_object* v___x_1757_; 
v___f_1756_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1757_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1755_, v___f_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = l_Lean_Expr_hasMVar(v_e_1758_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_e_1758_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; lean_object* v_mctx_1764_; lean_object* v___x_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; lean_object* v___x_1768_; lean_object* v_cache_1769_; lean_object* v_zetaDeltaFVarIds_1770_; lean_object* v_postponed_1771_; lean_object* v_diag_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1781_; 
v___x_1763_ = lean_st_ref_get(v___y_1759_);
v_mctx_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc_ref(v_mctx_1764_);
lean_dec(v___x_1763_);
v___x_1765_ = l_Lean_instantiateMVarsCore(v_mctx_1764_, v_e_1758_);
v_fst_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_fst_1766_);
v_snd_1767_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_snd_1767_);
lean_dec_ref(v___x_1765_);
v___x_1768_ = lean_st_ref_take(v___y_1759_);
v_cache_1769_ = lean_ctor_get(v___x_1768_, 1);
v_zetaDeltaFVarIds_1770_ = lean_ctor_get(v___x_1768_, 2);
v_postponed_1771_ = lean_ctor_get(v___x_1768_, 3);
v_diag_1772_ = lean_ctor_get(v___x_1768_, 4);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1768_, 0);
lean_dec(v_unused_1782_);
v___x_1774_ = v___x_1768_;
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_diag_1772_);
lean_inc(v_postponed_1771_);
lean_inc(v_zetaDeltaFVarIds_1770_);
lean_inc(v_cache_1769_);
lean_dec(v___x_1768_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v_snd_1767_);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_snd_1767_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_cache_1769_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_zetaDeltaFVarIds_1770_);
lean_ctor_set(v_reuseFailAlloc_1780_, 3, v_postponed_1771_);
lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_diag_1772_);
v___x_1777_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_st_ref_put(v___y_1759_, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_fst_1766_);
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1783_, v___y_1784_);
lean_dec(v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1787_, v___y_1789_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1801_, v_x_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1808_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1808_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1825_, lean_object* v_x_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1825_, v_x_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1833_, lean_object* v_mvarId_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1834_, v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1842_, lean_object* v_mvarId_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1842_, v_mvarId_1843_, v_x_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_ref_1857_; lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_ref_1857_ = lean_ctor_get(v___y_1854_, 2);
v___x_1858_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_inc(v_ref_1857_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_ref_1857_);
lean_ctor_set(v___x_1863_, 1, v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 1);
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = l_List_reverse___redArg(v_x_1876_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v_head_1884_; lean_object* v_tail_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1905_; 
v_head_1884_ = lean_ctor_get(v_x_1875_, 0);
v_tail_1885_ = lean_ctor_get(v_x_1875_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1887_ = v_x_1875_;
v_isShared_1888_ = v_isSharedCheck_1905_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_tail_1885_);
lean_inc(v_head_1884_);
lean_dec(v_x_1875_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1905_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_inc(v_head_1884_);
v___x_1889_ = l_Lean_Expr_mvar___override(v_head_1884_);
v___x_1890_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1890_, 0, v___x_1889_);
v___x_1891_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1884_, v___x_1890_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v_x_1876_);
lean_ctor_set(v___x_1887_, 0, v_a_1892_);
v___x_1894_ = v___x_1887_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1892_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_x_1876_);
v___x_1894_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
v_x_1875_ = v_tail_1885_;
v_x_1876_ = v___x_1894_;
goto _start;
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_del_object(v___x_1887_);
lean_dec(v_tail_1885_);
lean_dec(v_x_1876_);
v_a_1897_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1891_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1891_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1906_, v_x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1916_ = l_Lean_stringToMessageData(v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1917_, lean_object* v_proc_1918_, lean_object* v_orig_1919_, lean_object* v_goals_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_box(0);
lean_inc(v_orig_1919_);
v___x_1927_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1919_, v___x_1926_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
v___x_1929_ = lean_apply_6(v_test_1917_, v_a_1928_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, lean_box(0));
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; uint8_t v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = lean_unbox(v_a_1930_);
lean_dec(v_a_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_goals_1920_);
lean_dec(v_orig_1919_);
lean_dec_ref(v_proc_1918_);
v___x_1932_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1933_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1932_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v___x_1942_; 
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
v___x_1942_ = lean_apply_7(v_proc_1918_, v_orig_1919_, v_goals_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, lean_box(0));
return v___x_1942_;
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_goals_1920_);
lean_dec(v_orig_1919_);
lean_dec_ref(v_proc_1918_);
v_a_1943_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1929_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1929_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_goals_1920_);
lean_dec(v_orig_1919_);
lean_dec_ref(v_proc_1918_);
lean_dec_ref(v_test_1917_);
v_a_1951_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1927_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1927_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1959_, lean_object* v_proc_1960_, lean_object* v_orig_1961_, lean_object* v_goals_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1959_, v_proc_1960_, v_orig_1961_, v_goals_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1969_, lean_object* v_test_1970_){
_start:
{
lean_object* v_toApplyRulesConfig_1971_; lean_object* v_toBacktrackConfig_1972_; uint8_t v_backtracking_1973_; uint8_t v_intro_1974_; uint8_t v_constructor_1975_; uint8_t v_suggestions_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2008_; 
v_toApplyRulesConfig_1971_ = lean_ctor_get(v_cfg_1969_, 0);
lean_inc_ref(v_toApplyRulesConfig_1971_);
v_toBacktrackConfig_1972_ = lean_ctor_get(v_toApplyRulesConfig_1971_, 0);
lean_inc_ref(v_toBacktrackConfig_1972_);
v_backtracking_1973_ = lean_ctor_get_uint8(v_cfg_1969_, sizeof(void*)*1);
v_intro_1974_ = lean_ctor_get_uint8(v_cfg_1969_, sizeof(void*)*1 + 1);
v_constructor_1975_ = lean_ctor_get_uint8(v_cfg_1969_, sizeof(void*)*1 + 2);
v_suggestions_1976_ = lean_ctor_get_uint8(v_cfg_1969_, sizeof(void*)*1 + 3);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_cfg_1969_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v_cfg_1969_, 0);
lean_dec(v_unused_2009_);
v___x_1978_ = v_cfg_1969_;
v_isShared_1979_ = v_isSharedCheck_2008_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_cfg_1969_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2008_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_toApplyConfig_1980_; uint8_t v_transparency_1981_; uint8_t v_symm_1982_; uint8_t v_exfalso_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2006_; 
v_toApplyConfig_1980_ = lean_ctor_get(v_toApplyRulesConfig_1971_, 1);
v_transparency_1981_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1971_, sizeof(void*)*2);
v_symm_1982_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1971_, sizeof(void*)*2 + 1);
v_exfalso_1983_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1971_, sizeof(void*)*2 + 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_toApplyRulesConfig_1971_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v_toApplyRulesConfig_1971_, 0);
lean_dec(v_unused_2007_);
v___x_1985_ = v_toApplyRulesConfig_1971_;
v_isShared_1986_ = v_isSharedCheck_2006_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_toApplyConfig_1980_);
lean_dec(v_toApplyRulesConfig_1971_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2006_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_maxDepth_1987_; lean_object* v_proc_1988_; lean_object* v_suspend_1989_; lean_object* v_discharge_1990_; uint8_t v_commitIndependentGoals_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2005_; 
v_maxDepth_1987_ = lean_ctor_get(v_toBacktrackConfig_1972_, 0);
v_proc_1988_ = lean_ctor_get(v_toBacktrackConfig_1972_, 1);
v_suspend_1989_ = lean_ctor_get(v_toBacktrackConfig_1972_, 2);
v_discharge_1990_ = lean_ctor_get(v_toBacktrackConfig_1972_, 3);
v_commitIndependentGoals_1991_ = lean_ctor_get_uint8(v_toBacktrackConfig_1972_, sizeof(void*)*4);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_toBacktrackConfig_1972_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1993_ = v_toBacktrackConfig_1972_;
v_isShared_1994_ = v_isSharedCheck_2005_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_discharge_1990_);
lean_inc(v_suspend_1989_);
lean_inc(v_proc_1988_);
lean_inc(v_maxDepth_1987_);
lean_dec(v_toBacktrackConfig_1972_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2005_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___f_1995_; lean_object* v___x_1997_; 
v___f_1995_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1995_, 0, v_test_1970_);
lean_closure_set(v___f_1995_, 1, v_proc_1988_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___f_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_maxDepth_1987_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___f_1995_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_suspend_1989_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_discharge_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*4, v_commitIndependentGoals_1991_);
v___x_1997_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1997_);
v___x_1999_ = v___x_1985_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_toApplyConfig_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*2, v_transparency_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*2 + 1, v_symm_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*2 + 2, v_exfalso_1983_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2001_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1999_);
v___x_2001_ = v___x_1978_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*1, v_backtracking_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*1 + 1, v_intro_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*1 + 2, v_constructor_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*1 + 3, v_suggestions_1976_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2010_, lean_object* v_msg_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2018_, lean_object* v_msg_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2018_, v_msg_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2025_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
uint8_t v___x_2027_; 
v___x_2027_ = 0;
return v___x_2027_;
}
else
{
lean_object* v_head_2028_; lean_object* v_tail_2029_; uint8_t v___x_2030_; 
v_head_2028_ = lean_ctor_get(v_x_2026_, 0);
v_tail_2029_ = lean_ctor_get(v_x_2026_, 1);
v___x_2030_ = l_Lean_Expr_hasMVar(v_head_2028_);
if (v___x_2030_ == 0)
{
v_x_2026_ = v_tail_2029_;
goto _start;
}
else
{
return v___x_2030_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2032_){
_start:
{
uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_res_2033_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2032_);
lean_dec(v_x_2032_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2035_, lean_object* v_sols_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2036_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
v___x_2043_ = lean_apply_6(v_test_2035_, v_sols_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, lean_box(0));
return v___x_2043_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_sols_2036_);
lean_dec_ref(v_test_2035_);
v___x_2044_ = lean_box(v___x_2042_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2046_, lean_object* v_sols_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2046_, v_sols_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2054_, lean_object* v_test_2055_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2056_, 0, v_test_2055_);
v___x_2057_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2054_, v___f_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2058_, lean_object* v_x_2059_){
_start:
{
if (lean_obj_tag(v_x_2059_) == 0)
{
uint8_t v___x_2060_; 
lean_dec_ref(v_e_2058_);
v___x_2060_ = 0;
return v___x_2060_;
}
else
{
lean_object* v_head_2061_; lean_object* v_tail_2062_; uint8_t v___x_2063_; 
v_head_2061_ = lean_ctor_get(v_x_2059_, 0);
v_tail_2062_ = lean_ctor_get(v_x_2059_, 1);
lean_inc_ref(v_e_2058_);
v___x_2063_ = l_Lean_Expr_occurs(v_e_2058_, v_head_2061_);
if (v___x_2063_ == 0)
{
v_x_2059_ = v_tail_2062_;
goto _start;
}
else
{
lean_dec_ref(v_e_2058_);
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2065_, lean_object* v_x_2066_){
_start:
{
uint8_t v_res_2067_; lean_object* v_r_2068_; 
v_res_2067_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2065_, v_x_2066_);
lean_dec(v_x_2066_);
v_r_2068_ = lean_box(v_res_2067_);
return v_r_2068_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
uint8_t v___x_2071_; 
v___x_2071_ = 1;
return v___x_2071_;
}
else
{
lean_object* v_head_2072_; lean_object* v_tail_2073_; uint8_t v___x_2074_; 
v_head_2072_ = lean_ctor_get(v_x_2070_, 0);
lean_inc(v_head_2072_);
v_tail_2073_ = lean_ctor_get(v_x_2070_, 1);
lean_inc(v_tail_2073_);
lean_dec_ref_known(v_x_2070_, 2);
v___x_2074_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2072_, v_sols_2069_);
if (v___x_2074_ == 0)
{
lean_dec(v_tail_2073_);
return v___x_2074_;
}
else
{
v_x_2070_ = v_tail_2073_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2076_, lean_object* v_x_2077_){
_start:
{
uint8_t v_res_2078_; lean_object* v_r_2079_; 
v_res_2078_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2076_, v_x_2077_);
lean_dec(v_sols_2076_);
v_r_2079_ = lean_box(v_res_2078_);
return v_r_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2080_, lean_object* v_sols_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2081_, v_use_2080_);
v___x_2088_ = lean_box(v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2090_, lean_object* v_sols_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2090_, v_sols_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v_sols_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2098_, lean_object* v_use_2099_){
_start:
{
lean_object* v___f_2100_; lean_object* v___x_2101_; 
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2100_, 0, v_use_2099_);
v___x_2101_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2098_, v___f_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2102_){
_start:
{
lean_object* v___y_2104_; lean_object* v_toApplyRulesConfig_2105_; uint8_t v_backtracking_2106_; uint8_t v_intro_2107_; uint8_t v_constructor_2108_; uint8_t v_suggestions_2109_; uint8_t v_intro_2113_; 
v_intro_2113_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1 + 1);
if (v_intro_2113_ == 0)
{
lean_object* v_toApplyRulesConfig_2114_; uint8_t v_backtracking_2115_; uint8_t v_constructor_2116_; uint8_t v_suggestions_2117_; 
v_toApplyRulesConfig_2114_ = lean_ctor_get(v_cfg_2102_, 0);
lean_inc_ref(v_toApplyRulesConfig_2114_);
v_backtracking_2115_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1);
v_constructor_2116_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1 + 2);
v_suggestions_2117_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1 + 3);
v___y_2104_ = v_cfg_2102_;
v_toApplyRulesConfig_2105_ = v_toApplyRulesConfig_2114_;
v_backtracking_2106_ = v_backtracking_2115_;
v_intro_2107_ = v_intro_2113_;
v_constructor_2108_ = v_constructor_2116_;
v_suggestions_2109_ = v_suggestions_2117_;
goto v___jp_2103_;
}
else
{
lean_object* v_toApplyRulesConfig_2118_; uint8_t v_backtracking_2119_; uint8_t v_constructor_2120_; uint8_t v_suggestions_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2135_; 
v_toApplyRulesConfig_2118_ = lean_ctor_get(v_cfg_2102_, 0);
v_backtracking_2119_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1);
v_constructor_2120_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1 + 2);
v_suggestions_2121_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*1 + 3);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_cfg_2102_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2123_ = v_cfg_2102_;
v_isShared_2124_ = v_isSharedCheck_2135_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_toApplyRulesConfig_2118_);
lean_dec(v_cfg_2102_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2135_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
uint8_t v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = 0;
if (v_isShared_2124_ == 0)
{
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_toApplyRulesConfig_2118_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*1, v_backtracking_2119_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*1 + 2, v_constructor_2120_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*1 + 3, v_suggestions_2121_);
v___x_2127_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; lean_object* v_toApplyRulesConfig_2129_; uint8_t v_backtracking_2130_; uint8_t v_intro_2131_; uint8_t v_constructor_2132_; uint8_t v_suggestions_2133_; 
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*1 + 1, v___x_2125_);
v___x_2128_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2127_);
v_toApplyRulesConfig_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_ref(v_toApplyRulesConfig_2129_);
v_backtracking_2130_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*1);
v_intro_2131_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*1 + 1);
v_constructor_2132_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*1 + 2);
v_suggestions_2133_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*1 + 3);
v___y_2104_ = v___x_2128_;
v_toApplyRulesConfig_2105_ = v_toApplyRulesConfig_2129_;
v_backtracking_2106_ = v_backtracking_2130_;
v_intro_2107_ = v_intro_2131_;
v_constructor_2108_ = v_constructor_2132_;
v_suggestions_2109_ = v_suggestions_2133_;
goto v___jp_2103_;
}
}
}
v___jp_2103_:
{
if (v_constructor_2108_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2105_);
return v___y_2104_;
}
else
{
uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec_ref(v___y_2104_);
v___x_2110_ = 0;
v___x_2111_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2111_, 0, v_toApplyRulesConfig_2105_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*1, v_backtracking_2106_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*1 + 1, v_intro_2107_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*1 + 2, v___x_2110_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*1 + 3, v_suggestions_2109_);
v___x_2112_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2111_);
return v___x_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2136_, lean_object* v_x_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = l_List_reverse___redArg(v_x_2137_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
else
{
lean_object* v_head_2147_; lean_object* v_tail_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2166_; 
v_head_2147_ = lean_ctor_get(v_x_2136_, 0);
v_tail_2148_ = lean_ctor_get(v_x_2136_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2150_ = v_x_2136_;
v_isShared_2151_ = v_isSharedCheck_2166_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_tail_2148_);
lean_inc(v_head_2147_);
lean_dec(v_x_2136_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2166_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; 
lean_inc(v___y_2143_);
lean_inc_ref(v___y_2142_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
v___x_2152_ = lean_apply_7(v_head_2147_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, lean_box(0));
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_x_2137_);
lean_ctor_set(v___x_2150_, 0, v_a_2153_);
v___x_2155_ = v___x_2150_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2153_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_x_2137_);
v___x_2155_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
v_x_2136_ = v_tail_2148_;
v_x_2137_ = v___x_2155_;
goto _start;
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_del_object(v___x_2150_);
lean_dec(v_tail_2148_);
lean_dec(v_x_2137_);
v_a_2158_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2152_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2152_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2167_, v_x_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2177_, lean_object* v_cfg_2178_, lean_object* v_lemmas_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
lean_inc(v___y_2185_);
lean_inc_ref(v___y_2184_);
lean_inc(v___y_2183_);
lean_inc_ref(v___y_2182_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
v___x_2187_ = lean_apply_8(v_ctx_2177_, v_cfg_2178_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, lean_box(0));
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = lean_box(0);
v___x_2190_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2179_, v___x_2189_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = l_List_appendTR___redArg(v_a_2188_, v_a_2191_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
else
{
lean_dec(v_a_2188_);
return v___x_2190_;
}
}
else
{
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v_lemmas_2179_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2200_, lean_object* v_cfg_2201_, lean_object* v_lemmas_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2200_, v_cfg_2201_, v_lemmas_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2211_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = 0;
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2213_){
_start:
{
uint8_t v_res_2214_; lean_object* v_r_2215_; 
v_res_2214_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2213_);
lean_dec(v_x_2213_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2216_, lean_object* v___x_2217_, lean_object* v___x_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2216_, v___x_2217_, v___x_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_fst_2229_; lean_object* v___x_2231_; 
v_fst_2229_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_fst_2229_);
lean_dec(v_a_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_fst_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_fst_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2224_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2224_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2242_, lean_object* v___x_2243_, lean_object* v___x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2242_, v___x_2243_, v___x_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2265_, lean_object* v_g_2266_, lean_object* v_lemmas_2267_, lean_object* v_ctx_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___f_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; 
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2274_, 0, v_ctx_2268_);
lean_closure_set(v___f_2274_, 1, v_cfg_2265_);
lean_closure_set(v___f_2274_, 2, v_lemmas_2267_);
v___x_2275_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2276_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2277_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2277_, 0, v___f_2274_);
lean_closure_set(v___f_2277_, 1, v___x_2275_);
lean_closure_set(v___f_2277_, 2, v___x_2276_);
v___x_2278_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2266_, v___f_2277_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2279_, lean_object* v_g_2280_, lean_object* v_lemmas_2281_, lean_object* v_ctx_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2279_, v_g_2280_, v_lemmas_2281_, v_ctx_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2289_, lean_object* v_lemmas_2290_, lean_object* v_ctx_2291_, lean_object* v_g_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; 
lean_inc(v_g_2292_);
lean_inc_ref(v_cfg_2289_);
v___x_2298_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2289_, v_g_2292_, v_lemmas_2290_, v_ctx_2291_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_toApplyRulesConfig_2299_; lean_object* v_a_2300_; lean_object* v_toApplyConfig_2301_; uint8_t v_transparency_2302_; lean_object* v___x_2303_; 
v_toApplyRulesConfig_2299_ = lean_ctor_get(v_cfg_2289_, 0);
lean_inc_ref(v_toApplyRulesConfig_2299_);
lean_dec_ref(v_cfg_2289_);
v_a_2300_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2298_, 1);
v_toApplyConfig_2301_ = lean_ctor_get(v_toApplyRulesConfig_2299_, 1);
lean_inc_ref(v_toApplyConfig_2301_);
v_transparency_2302_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2299_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2299_);
v___x_2303_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2301_, v_transparency_2302_, v_a_2300_, v_g_2292_, v_a_2294_, v_a_2296_);
return v___x_2303_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_g_2292_);
lean_dec_ref(v_cfg_2289_);
v_a_2304_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2298_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2298_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2312_, lean_object* v_lemmas_2313_, lean_object* v_ctx_2314_, lean_object* v_g_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2312_, v_lemmas_2313_, v_ctx_2314_, v_g_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2322_, lean_object* v_lemmas_2323_, lean_object* v_ctx_2324_, lean_object* v_g_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2331_; 
lean_inc(v_g_2325_);
lean_inc_ref(v_cfg_2322_);
v___x_2331_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2322_, v_g_2325_, v_lemmas_2323_, v_ctx_2324_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_toApplyRulesConfig_2332_; lean_object* v_a_2333_; lean_object* v_toApplyConfig_2334_; uint8_t v_transparency_2335_; lean_object* v___x_2336_; 
v_toApplyRulesConfig_2332_ = lean_ctor_get(v_cfg_2322_, 0);
lean_inc_ref(v_toApplyRulesConfig_2332_);
lean_dec_ref(v_cfg_2322_);
v_a_2333_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2331_, 1);
v_toApplyConfig_2334_ = lean_ctor_get(v_toApplyRulesConfig_2332_, 1);
lean_inc_ref(v_toApplyConfig_2334_);
v_transparency_2335_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2332_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2332_);
v___x_2336_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2334_, v_transparency_2335_, v_a_2333_, v_g_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
return v___x_2336_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_g_2325_);
lean_dec_ref(v_cfg_2322_);
v_a_2337_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2331_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2331_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2345_, lean_object* v_lemmas_2346_, lean_object* v_ctx_2347_, lean_object* v_g_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2345_, v_lemmas_2346_, v_ctx_2347_, v_g_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2355_, lean_object* v_i_2356_, lean_object* v_k_2357_){
_start:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = lean_array_get_size(v_keys_2355_);
v___x_2359_ = lean_nat_dec_lt(v_i_2356_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec(v_i_2356_);
return v___x_2359_;
}
else
{
lean_object* v_k_x27_2360_; uint8_t v___x_2361_; 
v_k_x27_2360_ = lean_array_fget_borrowed(v_keys_2355_, v_i_2356_);
v___x_2361_ = l_Lean_instBEqMVarId_beq(v_k_2357_, v_k_x27_2360_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = lean_nat_add(v_i_2356_, v___x_2362_);
lean_dec(v_i_2356_);
v_i_2356_ = v___x_2363_;
goto _start;
}
else
{
lean_dec(v_i_2356_);
return v___x_2359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2365_, lean_object* v_i_2366_, lean_object* v_k_2367_){
_start:
{
uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_res_2368_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2365_, v_i_2366_, v_k_2367_);
lean_dec(v_k_2367_);
lean_dec_ref(v_keys_2365_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2370_, size_t v_x_2371_, lean_object* v_x_2372_){
_start:
{
if (lean_obj_tag(v_x_2370_) == 0)
{
lean_object* v_es_2373_; lean_object* v___x_2374_; size_t v___x_2375_; size_t v___x_2376_; lean_object* v_j_2377_; lean_object* v___x_2378_; 
v_es_2373_ = lean_ctor_get(v_x_2370_, 0);
v___x_2374_ = lean_box(2);
v___x_2375_ = ((size_t)31ULL);
v___x_2376_ = lean_usize_land(v_x_2371_, v___x_2375_);
v_j_2377_ = lean_usize_to_nat(v___x_2376_);
v___x_2378_ = lean_array_get_borrowed(v___x_2374_, v_es_2373_, v_j_2377_);
lean_dec(v_j_2377_);
switch(lean_obj_tag(v___x_2378_))
{
case 0:
{
lean_object* v_key_2379_; uint8_t v___x_2380_; 
v_key_2379_ = lean_ctor_get(v___x_2378_, 0);
v___x_2380_ = l_Lean_instBEqMVarId_beq(v_x_2372_, v_key_2379_);
return v___x_2380_;
}
case 1:
{
lean_object* v_node_2381_; size_t v___x_2382_; size_t v___x_2383_; 
v_node_2381_ = lean_ctor_get(v___x_2378_, 0);
v___x_2382_ = ((size_t)5ULL);
v___x_2383_ = lean_usize_shift_right(v_x_2371_, v___x_2382_);
v_x_2370_ = v_node_2381_;
v_x_2371_ = v___x_2383_;
goto _start;
}
default: 
{
uint8_t v___x_2385_; 
v___x_2385_ = 0;
return v___x_2385_;
}
}
}
else
{
lean_object* v_ks_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v_ks_2386_ = lean_ctor_get(v_x_2370_, 0);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2386_, v___x_2387_, v_x_2372_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
size_t v_x_1986__boxed_2392_; uint8_t v_res_2393_; lean_object* v_r_2394_; 
v_x_1986__boxed_2392_ = lean_unbox_usize(v_x_2390_);
lean_dec(v_x_2390_);
v_res_2393_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2389_, v_x_1986__boxed_2392_, v_x_2391_);
lean_dec(v_x_2391_);
lean_dec_ref(v_x_2389_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint64_t v___x_2397_; size_t v___x_2398_; uint8_t v___x_2399_; 
v___x_2397_ = l_Lean_instHashableMVarId_hash(v_x_2396_);
v___x_2398_ = lean_uint64_to_usize(v___x_2397_);
v___x_2399_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2395_, v___x_2398_, v_x_2396_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2400_, lean_object* v_x_2401_){
_start:
{
uint8_t v_res_2402_; lean_object* v_r_2403_; 
v_res_2402_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2400_, v_x_2401_);
lean_dec(v_x_2401_);
lean_dec_ref(v_x_2400_);
v_r_2403_ = lean_box(v_res_2402_);
return v_r_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v_mctx_2408_; lean_object* v_eAssignment_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2407_ = lean_st_ref_get(v___y_2405_);
v_mctx_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc_ref(v_mctx_2408_);
lean_dec(v___x_2407_);
v_eAssignment_2409_ = lean_ctor_get(v_mctx_2408_, 8);
lean_inc_ref(v_eAssignment_2409_);
lean_dec_ref(v_mctx_2408_);
v___x_2410_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2409_, v_mvarId_2404_);
lean_dec_ref(v_eAssignment_2409_);
v___x_2411_ = lean_box(v___x_2410_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec(v_mvarId_2413_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
if (lean_obj_tag(v_x_2418_) == 0)
{
return v_x_2417_;
}
else
{
lean_object* v_head_2419_; lean_object* v_tail_2420_; lean_object* v___x_2421_; 
v_head_2419_ = lean_ctor_get(v_x_2418_, 0);
lean_inc(v_head_2419_);
v_tail_2420_ = lean_ctor_get(v_x_2418_, 1);
lean_inc(v_tail_2420_);
lean_dec_ref_known(v_x_2418_, 2);
v___x_2421_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2417_, v_head_2419_);
v_x_2417_ = v___x_2421_;
v_x_2418_ = v_tail_2420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2423_, lean_object* v_a_2424_, uint8_t v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
if (lean_obj_tag(v_a_2426_) == 0)
{
if (lean_obj_tag(v_a_2427_) == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_a_2424_);
lean_dec_ref(v_f_2423_);
v___x_2434_ = lean_box(v_a_2425_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v_a_2428_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
else
{
lean_object* v_head_2437_; lean_object* v_tail_2438_; 
v_head_2437_ = lean_ctor_get(v_a_2427_, 0);
lean_inc(v_head_2437_);
v_tail_2438_ = lean_ctor_get(v_a_2427_, 1);
lean_inc(v_tail_2438_);
lean_dec_ref_known(v_a_2427_, 2);
v_a_2426_ = v_head_2437_;
v_a_2427_ = v_tail_2438_;
goto _start;
}
}
else
{
lean_object* v_head_2440_; lean_object* v_tail_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2484_; 
v_head_2440_ = lean_ctor_get(v_a_2426_, 0);
v_tail_2441_ = lean_ctor_get(v_a_2426_, 1);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_a_2426_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2443_ = v_a_2426_;
v_isShared_2444_ = v_isSharedCheck_2484_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_tail_2441_);
lean_inc(v_head_2440_);
lean_dec(v_a_2426_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2484_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2483_; 
v___x_2445_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2440_, v___y_2430_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2483_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2483_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
if (v___x_2450_ == 0)
{
lean_object* v_zero_2451_; uint8_t v_isZero_2452_; 
v_zero_2451_ = lean_unsigned_to_nat(0u);
v_isZero_2452_ = lean_nat_dec_eq(v_a_2424_, v_zero_2451_);
if (v_isZero_2452_ == 1)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_del_object(v___x_2443_);
lean_dec(v_a_2424_);
lean_dec_ref(v_f_2423_);
v___x_2453_ = lean_array_push(v_a_2428_, v_head_2440_);
v___x_2454_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2453_, v_tail_2441_);
v___x_2455_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2454_, v_a_2427_);
v___x_2456_ = lean_box(v_a_2425_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2457_);
v___x_2459_ = v___x_2448_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_del_object(v___x_2448_);
lean_inc_ref(v_f_2423_);
lean_inc(v_head_2440_);
v___x_2461_ = lean_apply_1(v_f_2423_, v_head_2440_);
v___x_2462_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2461_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v_one_2464_; lean_object* v_n_2465_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v_one_2464_ = lean_unsigned_to_nat(1u);
v_n_2465_ = lean_nat_sub(v_a_2424_, v_one_2464_);
lean_dec(v_a_2424_);
if (lean_obj_tag(v_a_2463_) == 0)
{
lean_object* v___x_2466_; 
lean_del_object(v___x_2443_);
v___x_2466_ = lean_array_push(v_a_2428_, v_head_2440_);
v_a_2424_ = v_n_2465_;
v_a_2426_ = v_tail_2441_;
v_a_2428_ = v___x_2466_;
goto _start;
}
else
{
lean_object* v_val_2468_; uint8_t v___x_2469_; lean_object* v___x_2471_; 
lean_dec(v_head_2440_);
v_val_2468_ = lean_ctor_get(v_a_2463_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v_a_2463_, 1);
v___x_2469_ = 1;
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v_a_2427_);
lean_ctor_set(v___x_2443_, 0, v_tail_2441_);
v___x_2471_ = v___x_2443_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_tail_2441_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_a_2427_);
v___x_2471_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v_a_2424_ = v_n_2465_;
v_a_2425_ = v___x_2469_;
v_a_2426_ = v_val_2468_;
v_a_2427_ = v___x_2471_;
goto _start;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_del_object(v___x_2443_);
lean_dec(v_tail_2441_);
lean_dec(v_head_2440_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec(v_a_2424_);
lean_dec_ref(v_f_2423_);
v_a_2474_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2462_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2462_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
else
{
lean_del_object(v___x_2448_);
lean_del_object(v___x_2443_);
lean_dec(v_head_2440_);
v_a_2426_ = v_tail_2441_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v_a_2065__boxed_2496_; lean_object* v_res_2497_; 
v_a_2065__boxed_2496_ = lean_unbox(v_a_2487_);
v_res_2497_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2485_, v_a_2486_, v_a_2065__boxed_2496_, v_a_2488_, v_a_2489_, v_a_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2498_, size_t v_i_2499_, size_t v_stop_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_a_2508_; uint8_t v___x_2512_; 
v___x_2512_ = lean_usize_dec_eq(v_i_2499_, v_stop_2500_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2516_; 
v___x_2513_ = lean_array_uget_borrowed(v_as_2498_, v_i_2499_);
v___x_2516_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2513_, v___y_2503_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; uint8_t v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = lean_unbox(v_a_2517_);
lean_dec(v_a_2517_);
if (v___x_2518_ == 0)
{
goto v___jp_2514_;
}
else
{
v_a_2508_ = v_b_2501_;
goto v___jp_2507_;
}
}
else
{
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2519_; uint8_t v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2520_ = lean_unbox(v_a_2519_);
lean_dec(v_a_2519_);
if (v___x_2520_ == 0)
{
v_a_2508_ = v_b_2501_;
goto v___jp_2507_;
}
else
{
goto v___jp_2514_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_b_2501_);
v_a_2521_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2516_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2516_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
v___jp_2514_:
{
lean_object* v___x_2515_; 
lean_inc(v___x_2513_);
v___x_2515_ = lean_array_push(v_b_2501_, v___x_2513_);
v_a_2508_ = v___x_2515_;
goto v___jp_2507_;
}
}
else
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_b_2501_);
return v___x_2529_;
}
v___jp_2507_:
{
size_t v___x_2509_; size_t v___x_2510_; 
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2499_, v___x_2509_);
v_i_2499_ = v___x_2510_;
v_b_2501_ = v_a_2508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2530_, lean_object* v_i_2531_, lean_object* v_stop_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
size_t v_i_boxed_2539_; size_t v_stop_boxed_2540_; lean_object* v_res_2541_; 
v_i_boxed_2539_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_stop_boxed_2540_ = lean_unbox_usize(v_stop_2532_);
lean_dec(v_stop_2532_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2530_, v_i_boxed_2539_, v_stop_boxed_2540_, v_b_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v_as_2530_);
return v_res_2541_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2545_ = lean_array_to_list(v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2546_, lean_object* v_goals_2547_, lean_object* v_maxIters_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2554_ = 0;
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2558_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2546_, v_maxIters_2548_, v___x_2554_, v_goals_2547_, v___x_2555_, v___x_2557_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2601_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2601_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2601_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_fst_2563_; lean_object* v_snd_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2600_; 
v_fst_2563_ = lean_ctor_get(v_a_2559_, 0);
v_snd_2564_ = lean_ctor_get(v_a_2559_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_a_2559_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2566_ = v_a_2559_;
v_isShared_2567_ = v_isSharedCheck_2600_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_snd_2564_);
lean_inc(v_fst_2563_);
lean_dec(v_a_2559_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2600_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = lean_array_get_size(v_snd_2564_);
v___x_2569_ = lean_nat_dec_lt(v___x_2556_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_dec(v_snd_2564_);
v___x_2570_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 1, v___x_2570_);
v___x_2572_ = v___x_2566_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_fst_2563_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2574_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2572_);
v___x_2574_ = v___x_2561_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
lean_del_object(v___x_2561_);
v___x_2577_ = ((size_t)0ULL);
v___x_2578_ = lean_usize_of_nat(v___x_2568_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2564_, v___x_2577_, v___x_2578_, v___x_2557_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v_snd_2564_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2591_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2591_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2591_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_array_to_list(v_a_2580_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 1, v___x_2584_);
v___x_2586_ = v___x_2566_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_fst_2563_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2586_);
v___x_2588_ = v___x_2582_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_del_object(v___x_2566_);
lean_dec(v_fst_2563_);
v_a_2592_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2579_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2579_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_a_2602_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2558_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2558_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2610_, lean_object* v_goals_2611_, lean_object* v_maxIters_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2610_, v_goals_2611_, v_maxIters_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2618_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2622_, lean_object* v_goals_2623_, lean_object* v_maxIters_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2622_, v_goals_2623_, v_maxIters_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2643_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_fst_2635_; uint8_t v___x_2636_; 
v_fst_2635_ = lean_ctor_get(v_a_2631_, 0);
v___x_2636_ = lean_unbox(v_fst_2635_);
if (v___x_2636_ == 1)
{
lean_object* v_snd_2637_; lean_object* v___x_2639_; 
v_snd_2637_ = lean_ctor_get(v_a_2631_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_a_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_snd_2637_);
v___x_2639_ = v___x_2633_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_snd_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_del_object(v___x_2633_);
lean_dec(v_a_2631_);
v___x_2641_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2642_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2641_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2642_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_a_2644_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2630_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2630_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2652_, lean_object* v_goals_2653_, lean_object* v_maxIters_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2652_, v_goals_2653_, v_maxIters_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2661_, lean_object* v_ctx_2662_, lean_object* v_cfg_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
uint8_t v_backtracking_2670_; 
v_backtracking_2670_ = lean_ctor_get_uint8(v_cfg_2663_, sizeof(void*)*1);
if (v_backtracking_2670_ == 0)
{
lean_object* v_toApplyRulesConfig_2671_; lean_object* v_toBacktrackConfig_2672_; lean_object* v_maxDepth_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_toApplyRulesConfig_2671_ = lean_ctor_get(v_cfg_2663_, 0);
v_toBacktrackConfig_2672_ = lean_ctor_get(v_toApplyRulesConfig_2671_, 0);
v_maxDepth_2673_ = lean_ctor_get(v_toBacktrackConfig_2672_, 0);
lean_inc(v_maxDepth_2673_);
v___x_2674_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2674_, 0, v_cfg_2663_);
lean_closure_set(v___x_2674_, 1, v_lemmas_2661_);
lean_closure_set(v___x_2674_, 2, v_ctx_2662_);
v___x_2675_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2674_, v_a_2664_, v_maxDepth_2673_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2675_;
}
else
{
lean_object* v_toApplyRulesConfig_2676_; lean_object* v_toBacktrackConfig_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_toApplyRulesConfig_2676_ = lean_ctor_get(v_cfg_2663_, 0);
v_toBacktrackConfig_2677_ = lean_ctor_get(v_toApplyRulesConfig_2676_, 0);
lean_inc_ref(v_toBacktrackConfig_2677_);
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2679_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2679_, 0, v_cfg_2663_);
lean_closure_set(v___x_2679_, 1, v_lemmas_2661_);
lean_closure_set(v___x_2679_, 2, v_ctx_2662_);
v___x_2680_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2677_, v___x_2678_, v___x_2679_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2681_, lean_object* v_ctx_2682_, lean_object* v_cfg_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2681_, v_ctx_2682_, v_cfg_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2691_, v___y_2693_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v_mvarId_2698_);
return v_res_2704_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_){
_start:
{
uint8_t v___x_2708_; 
v___x_2708_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2706_, v_x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
uint8_t v_res_2712_; lean_object* v_r_2713_; 
v_res_2712_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2709_, v_x_2710_, v_x_2711_);
lean_dec(v_x_2711_);
lean_dec_ref(v_x_2710_);
v_r_2713_ = lean_box(v_res_2712_);
return v_r_2713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2714_, lean_object* v_x_2715_, size_t v_x_2716_, lean_object* v_x_2717_){
_start:
{
uint8_t v___x_2718_; 
v___x_2718_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2715_, v_x_2716_, v_x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_){
_start:
{
size_t v_x_2511__boxed_2723_; uint8_t v_res_2724_; lean_object* v_r_2725_; 
v_x_2511__boxed_2723_ = lean_unbox_usize(v_x_2721_);
lean_dec(v_x_2721_);
v_res_2724_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2719_, v_x_2720_, v_x_2511__boxed_2723_, v_x_2722_);
lean_dec(v_x_2722_);
lean_dec_ref(v_x_2720_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2726_, lean_object* v_keys_2727_, lean_object* v_vals_2728_, lean_object* v_heq_2729_, lean_object* v_i_2730_, lean_object* v_k_2731_){
_start:
{
uint8_t v___x_2732_; 
v___x_2732_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2727_, v_i_2730_, v_k_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2733_, lean_object* v_keys_2734_, lean_object* v_vals_2735_, lean_object* v_heq_2736_, lean_object* v_i_2737_, lean_object* v_k_2738_){
_start:
{
uint8_t v_res_2739_; lean_object* v_r_2740_; 
v_res_2739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2733_, v_keys_2734_, v_vals_2735_, v_heq_2736_, v_i_2737_, v_k_2738_);
lean_dec(v_k_2738_);
lean_dec_ref(v_vals_2735_);
lean_dec_ref(v_keys_2734_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v_x_2752_);
return v_res_2758_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2761_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2762_ = l_Lean_Name_append(v___x_2761_, v___x_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2763_, lean_object* v_lemmas_2764_, lean_object* v_ctx_2765_, lean_object* v_goals_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_cfg_2772_; lean_object* v___x_2773_; 
v_cfg_2772_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2763_);
lean_inc(v_goals_2766_);
lean_inc_ref(v_cfg_2772_);
lean_inc_ref(v_ctx_2765_);
lean_inc(v_lemmas_2764_);
v___x_2773_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2764_, v_ctx_2765_, v_cfg_2772_, v_goals_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_dec_ref(v_cfg_2772_);
lean_dec(v_goals_2766_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
return v___x_2773_;
}
else
{
lean_object* v_a_2774_; lean_object* v___f_2775_; lean_object* v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v_a_2784_; lean_object* v___y_2797_; uint8_t v___y_2798_; lean_object* v___y_2799_; uint8_t v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v_a_2804_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; lean_object* v___y_2810_; uint8_t v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v_a_2814_; lean_object* v___y_2824_; lean_object* v___y_2825_; uint8_t v___y_2826_; lean_object* v___y_2827_; uint8_t v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v_a_2831_; lean_object* v___y_2834_; uint8_t v___y_2835_; uint8_t v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; uint8_t v___y_2876_; uint8_t v___x_2930_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
v___f_2775_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_2930_ = l_Lean_Exception_isInterrupt(v_a_2774_);
if (v___x_2930_ == 0)
{
uint8_t v___x_2931_; 
v___x_2931_ = l_Lean_Exception_isRuntime(v_a_2774_);
v___y_2876_ = v___x_2931_;
goto v___jp_2875_;
}
else
{
lean_dec(v_a_2774_);
v___y_2876_ = v___x_2930_;
goto v___jp_2875_;
}
v___jp_2776_:
{
lean_object* v___x_2785_; double v___x_2786_; double v___x_2787_; double v___x_2788_; double v___x_2789_; double v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2785_ = lean_io_mono_nanos_now();
v___x_2786_ = lean_float_of_nat(v___y_2782_);
v___x_2787_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2788_ = lean_float_div(v___x_2786_, v___x_2787_);
v___x_2789_ = lean_float_of_nat(v___x_2785_);
v___x_2790_ = lean_float_div(v___x_2789_, v___x_2787_);
v___x_2791_ = lean_box_float(v___x_2788_);
v___x_2792_ = lean_box_float(v___x_2790_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2784_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2777_);
v___x_2795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2777_, v___y_2780_, v___y_2783_, v___y_2781_, v___y_2778_, v___y_2779_, v___f_2775_, v___x_2794_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2795_;
}
v___jp_2796_:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2804_);
v___y_2777_ = v___y_2797_;
v___y_2778_ = v___y_2798_;
v___y_2779_ = v___y_2799_;
v___y_2780_ = v___y_2800_;
v___y_2781_ = v___y_2801_;
v___y_2782_ = v___y_2802_;
v___y_2783_ = v___y_2803_;
v_a_2784_ = v___x_2805_;
goto v___jp_2776_;
}
v___jp_2806_:
{
lean_object* v___x_2815_; double v___x_2816_; double v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2815_ = lean_io_get_num_heartbeats();
v___x_2816_ = lean_float_of_nat(v___y_2807_);
v___x_2817_ = lean_float_of_nat(v___x_2815_);
v___x_2818_ = lean_box_float(v___x_2816_);
v___x_2819_ = lean_box_float(v___x_2817_);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2814_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
lean_inc_ref(v___y_2813_);
lean_inc(v___y_2808_);
v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2808_, v___y_2811_, v___y_2813_, v___y_2812_, v___y_2809_, v___y_2810_, v___f_2775_, v___x_2821_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2822_;
}
v___jp_2823_:
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_a_2831_);
v___y_2807_ = v___y_2824_;
v___y_2808_ = v___y_2825_;
v___y_2809_ = v___y_2826_;
v___y_2810_ = v___y_2827_;
v___y_2811_ = v___y_2828_;
v___y_2812_ = v___y_2829_;
v___y_2813_ = v___y_2830_;
v_a_2814_ = v___x_2832_;
goto v___jp_2806_;
}
v___jp_2833_:
{
lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2770_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2844_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2837_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_io_mono_nanos_now();
v___x_2846_ = l_Lean_MVarId_exfalso(v___y_2838_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2848_, 0, v_a_2847_);
lean_ctor_set(v___x_2848_, 1, v___y_2839_);
v___x_2849_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2764_, v_ctx_2765_, v_cfg_2772_, v___x_2848_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set_tag(v___x_2852_, 1);
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
v___y_2777_ = v___y_2834_;
v___y_2778_ = v___y_2835_;
v___y_2779_ = v_a_2842_;
v___y_2780_ = v___y_2836_;
v___y_2781_ = v___y_2837_;
v___y_2782_ = v___x_2845_;
v___y_2783_ = v___y_2840_;
v_a_2784_ = v___x_2855_;
goto v___jp_2776_;
}
}
}
else
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2849_, 1);
v___y_2797_ = v___y_2834_;
v___y_2798_ = v___y_2835_;
v___y_2799_ = v_a_2842_;
v___y_2800_ = v___y_2836_;
v___y_2801_ = v___y_2837_;
v___y_2802_ = v___x_2845_;
v___y_2803_ = v___y_2840_;
v_a_2804_ = v_a_2858_;
goto v___jp_2796_;
}
}
else
{
lean_object* v_a_2859_; 
lean_dec(v___y_2839_);
lean_dec_ref(v_cfg_2772_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
v_a_2859_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2846_, 1);
v___y_2797_ = v___y_2834_;
v___y_2798_ = v___y_2835_;
v___y_2799_ = v_a_2842_;
v___y_2800_ = v___y_2836_;
v___y_2801_ = v___y_2837_;
v___y_2802_ = v___x_2845_;
v___y_2803_ = v___y_2840_;
v_a_2804_ = v_a_2859_;
goto v___jp_2796_;
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_io_get_num_heartbeats();
v___x_2861_ = l_Lean_MVarId_exfalso(v___y_2838_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2863_, 0, v_a_2862_);
lean_ctor_set(v___x_2863_, 1, v___y_2839_);
v___x_2864_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2764_, v_ctx_2765_, v_cfg_2772_, v___x_2863_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 1);
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
v___y_2807_ = v___x_2860_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2835_;
v___y_2810_ = v_a_2842_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___y_2837_;
v___y_2813_ = v___y_2840_;
v_a_2814_ = v___x_2870_;
goto v___jp_2806_;
}
}
}
else
{
lean_object* v_a_2873_; 
v_a_2873_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2864_, 1);
v___y_2824_ = v___x_2860_;
v___y_2825_ = v___y_2834_;
v___y_2826_ = v___y_2835_;
v___y_2827_ = v_a_2842_;
v___y_2828_ = v___y_2836_;
v___y_2829_ = v___y_2837_;
v___y_2830_ = v___y_2840_;
v_a_2831_ = v_a_2873_;
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2874_; 
lean_dec(v___y_2839_);
lean_dec_ref(v_cfg_2772_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
v_a_2874_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2861_, 1);
v___y_2824_ = v___x_2860_;
v___y_2825_ = v___y_2834_;
v___y_2826_ = v___y_2835_;
v___y_2827_ = v_a_2842_;
v___y_2828_ = v___y_2836_;
v___y_2829_ = v___y_2837_;
v___y_2830_ = v___y_2840_;
v_a_2831_ = v_a_2874_;
goto v___jp_2823_;
}
}
}
v___jp_2875_:
{
if (v___y_2876_ == 0)
{
if (lean_obj_tag(v_goals_2766_) == 1)
{
lean_object* v_tail_2877_; 
v_tail_2877_ = lean_ctor_get(v_goals_2766_, 1);
lean_inc(v_tail_2877_);
if (lean_obj_tag(v_tail_2877_) == 0)
{
lean_object* v_toApplyRulesConfig_2878_; uint8_t v_exfalso_2879_; 
v_toApplyRulesConfig_2878_ = lean_ctor_get(v_cfg_2772_, 0);
lean_inc_ref(v_toApplyRulesConfig_2878_);
v_exfalso_2879_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2878_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2878_);
if (v_exfalso_2879_ == 1)
{
lean_object* v_toCold_2880_; lean_object* v_options_2881_; uint8_t v_hasTrace_2882_; 
lean_dec_ref_known(v___x_2773_, 1);
v_toCold_2880_ = lean_ctor_get(v_a_2769_, 0);
v_options_2881_ = lean_ctor_get(v_toCold_2880_, 2);
v_hasTrace_2882_ = lean_ctor_get_uint8(v_options_2881_, sizeof(void*)*1);
if (v_hasTrace_2882_ == 0)
{
lean_object* v_head_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2901_; 
v_head_2883_ = lean_ctor_get(v_goals_2766_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_goals_2766_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v_goals_2766_, 1);
lean_dec(v_unused_2902_);
v___x_2885_ = v_goals_2766_;
v_isShared_2886_ = v_isSharedCheck_2901_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_head_2883_);
lean_dec(v_goals_2766_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2901_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_MVarId_exfalso(v_head_2883_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v_a_2888_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2888_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_tail_2877_);
v___x_2890_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2764_, v_ctx_2765_, v_cfg_2772_, v___x_2890_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2891_;
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_del_object(v___x_2885_);
lean_dec_ref(v_cfg_2772_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
v_a_2893_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2887_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2887_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
else
{
lean_object* v_head_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2928_; 
v_head_2903_ = lean_ctor_get(v_goals_2766_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_goals_2766_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v_goals_2766_, 1);
lean_dec(v_unused_2929_);
v___x_2905_ = v_goals_2766_;
v_isShared_2906_ = v_isSharedCheck_2928_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_head_2903_);
lean_dec(v_goals_2766_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2928_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_inheritedTraceOptions_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_inheritedTraceOptions_2907_ = lean_ctor_get(v_toCold_2880_, 11);
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2909_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2910_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2911_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2907_, v_options_2881_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = l_Lean_trace_profiler;
v___x_2913_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2881_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_MVarId_exfalso(v_head_2903_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v_a_2915_);
v___x_2917_ = v___x_2905_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2915_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_tail_2877_);
v___x_2917_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; 
v___x_2918_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2764_, v_ctx_2765_, v_cfg_2772_, v___x_2917_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2918_;
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_del_object(v___x_2905_);
lean_dec_ref(v_cfg_2772_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
v_a_2920_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2914_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2914_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_del_object(v___x_2905_);
v___y_2834_ = v___x_2908_;
v___y_2835_ = v___x_2911_;
v___y_2836_ = v_exfalso_2879_;
v___y_2837_ = v_options_2881_;
v___y_2838_ = v_head_2903_;
v___y_2839_ = v_tail_2877_;
v___y_2840_ = v___x_2909_;
goto v___jp_2833_;
}
}
else
{
lean_del_object(v___x_2905_);
v___y_2834_ = v___x_2908_;
v___y_2835_ = v___x_2911_;
v___y_2836_ = v_exfalso_2879_;
v___y_2837_ = v_options_2881_;
v___y_2838_ = v_head_2903_;
v___y_2839_ = v_tail_2877_;
v___y_2840_ = v___x_2909_;
goto v___jp_2833_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2766_, 2);
lean_dec_ref(v_cfg_2772_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
return v___x_2773_;
}
}
else
{
lean_dec_ref_known(v_goals_2766_, 2);
lean_dec(v_tail_2877_);
lean_dec_ref(v_cfg_2772_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
return v___x_2773_;
}
}
else
{
lean_dec_ref(v_cfg_2772_);
lean_dec(v_goals_2766_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
return v___x_2773_;
}
}
else
{
lean_dec_ref(v_cfg_2772_);
lean_dec(v_goals_2766_);
lean_dec_ref(v_ctx_2765_);
lean_dec(v_lemmas_2764_);
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2932_, lean_object* v_lemmas_2933_, lean_object* v_ctx_2934_, lean_object* v_goals_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2932_, v_lemmas_2933_, v_ctx_2934_, v_goals_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2942_, lean_object* v_x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
if (lean_obj_tag(v_x_2942_) == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = l_List_reverse___redArg(v_x_2943_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
else
{
lean_object* v_head_2951_; lean_object* v_tail_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2975_; 
v_head_2951_ = lean_ctor_get(v_x_2942_, 0);
v_tail_2952_ = lean_ctor_get(v_x_2942_, 1);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_x_2942_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2954_ = v_x_2942_;
v_isShared_2955_ = v_isSharedCheck_2975_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_tail_2952_);
lean_inc(v_head_2951_);
lean_dec(v_x_2942_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2975_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Expr_applySymm(v_head_2951_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v_x_2943_);
lean_ctor_set(v___x_2954_, 0, v_a_2957_);
v___x_2959_ = v___x_2954_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_x_2943_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
v_x_2942_ = v_tail_2952_;
v_x_2943_ = v___x_2959_;
goto _start;
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2974_; 
lean_del_object(v___x_2954_);
v_a_2962_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2964_ = v___x_2956_;
v_isShared_2965_ = v_isSharedCheck_2974_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2956_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2974_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
uint8_t v___y_2967_; uint8_t v___x_2972_; 
v___x_2972_ = l_Lean_Exception_isInterrupt(v_a_2962_);
if (v___x_2972_ == 0)
{
uint8_t v___x_2973_; 
lean_inc(v_a_2962_);
v___x_2973_ = l_Lean_Exception_isRuntime(v_a_2962_);
v___y_2967_ = v___x_2973_;
goto v___jp_2966_;
}
else
{
v___y_2967_ = v___x_2972_;
goto v___jp_2966_;
}
v___jp_2966_:
{
if (v___y_2967_ == 0)
{
lean_del_object(v___x_2964_);
lean_dec(v_a_2962_);
v_x_2942_ = v_tail_2952_;
goto _start;
}
else
{
lean_object* v___x_2970_; 
lean_dec(v_tail_2952_);
lean_dec(v_x_2943_);
if (v_isShared_2965_ == 0)
{
v___x_2970_ = v___x_2964_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2962_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2976_, lean_object* v_x_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2976_, v_x_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2984_, lean_object* v_hyps_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
if (v_symm_2984_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_hyps_2985_);
return v___x_2991_;
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_box(0);
lean_inc(v_hyps_2985_);
v___x_2993_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2985_, v___x_2992_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3002_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = l_List_appendTR___redArg(v_hyps_2985_, v_a_2994_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_2998_);
v___x_3000_ = v___x_2996_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_dec(v_hyps_2985_);
return v___x_2993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3003_, lean_object* v_hyps_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
uint8_t v_symm_boxed_3010_; lean_object* v_res_3011_; 
v_symm_boxed_3010_ = lean_unbox(v_symm_3003_);
v_res_3011_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3010_, v_hyps_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3012_, size_t v_sz_3013_, size_t v_i_3014_, lean_object* v_b_3015_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_usize_dec_lt(v_i_3014_, v_sz_3013_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_b_3015_);
return v___x_3018_;
}
else
{
lean_object* v_snd_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3037_; 
v_snd_3019_ = lean_ctor_get(v_b_3015_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_b_3015_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v_b_3015_, 0);
lean_dec(v_unused_3038_);
v___x_3021_ = v_b_3015_;
v_isShared_3022_ = v_isSharedCheck_3037_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_snd_3019_);
lean_dec(v_b_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3037_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v_a_3025_; lean_object* v_a_3032_; 
v___x_3023_ = lean_box(0);
v_a_3032_ = lean_array_uget_borrowed(v_as_3012_, v_i_3014_);
if (lean_obj_tag(v_a_3032_) == 0)
{
v_a_3025_ = v_snd_3019_;
goto v___jp_3024_;
}
else
{
lean_object* v_val_3033_; uint8_t v___x_3034_; 
v_val_3033_ = lean_ctor_get(v_a_3032_, 0);
v___x_3034_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_inc(v_val_3033_);
v___x_3035_ = l_Lean_LocalDecl_toExpr(v_val_3033_);
v___x_3036_ = lean_array_push(v_snd_3019_, v___x_3035_);
v_a_3025_ = v___x_3036_;
goto v___jp_3024_;
}
else
{
v_a_3025_ = v_snd_3019_;
goto v___jp_3024_;
}
}
v___jp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v_a_3025_);
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3027_ = v___x_3021_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_a_3025_);
v___x_3027_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
size_t v___x_3028_; size_t v___x_3029_; 
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_add(v_i_3014_, v___x_3028_);
v_i_3014_ = v___x_3029_;
v_b_3015_ = v___x_3027_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3039_, lean_object* v_sz_3040_, lean_object* v_i_3041_, lean_object* v_b_3042_, lean_object* v___y_3043_){
_start:
{
size_t v_sz_boxed_3044_; size_t v_i_boxed_3045_; lean_object* v_res_3046_; 
v_sz_boxed_3044_ = lean_unbox_usize(v_sz_3040_);
lean_dec(v_sz_3040_);
v_i_boxed_3045_ = lean_unbox_usize(v_i_3041_);
lean_dec(v_i_3041_);
v_res_3046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3039_, v_sz_boxed_3044_, v_i_boxed_3045_, v_b_3042_);
lean_dec_ref(v_as_3039_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3047_, size_t v_sz_3048_, size_t v_i_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_lt(v_i_3049_, v_sz_3048_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_b_3050_);
return v___x_3059_;
}
else
{
lean_object* v_snd_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3078_; 
v_snd_3060_ = lean_ctor_get(v_b_3050_, 1);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_b_3050_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v_b_3050_, 0);
lean_dec(v_unused_3079_);
v___x_3062_ = v_b_3050_;
v_isShared_3063_ = v_isSharedCheck_3078_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_snd_3060_);
lean_dec(v_b_3050_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3078_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v_a_3066_; lean_object* v_a_3073_; 
v___x_3064_ = lean_box(0);
v_a_3073_ = lean_array_uget_borrowed(v_as_3047_, v_i_3049_);
if (lean_obj_tag(v_a_3073_) == 0)
{
v_a_3066_ = v_snd_3060_;
goto v___jp_3065_;
}
else
{
lean_object* v_val_3074_; uint8_t v___x_3075_; 
v_val_3074_ = lean_ctor_get(v_a_3073_, 0);
v___x_3075_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_inc(v_val_3074_);
v___x_3076_ = l_Lean_LocalDecl_toExpr(v_val_3074_);
v___x_3077_ = lean_array_push(v_snd_3060_, v___x_3076_);
v_a_3066_ = v___x_3077_;
goto v___jp_3065_;
}
else
{
v_a_3066_ = v_snd_3060_;
goto v___jp_3065_;
}
}
v___jp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 1, v_a_3066_);
lean_ctor_set(v___x_3062_, 0, v___x_3064_);
v___x_3068_ = v___x_3062_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_a_3066_);
v___x_3068_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_add(v_i_3049_, v___x_3069_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3047_, v_sz_3048_, v___x_3070_, v___x_3068_);
return v___x_3071_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3080_, lean_object* v_sz_3081_, lean_object* v_i_3082_, lean_object* v_b_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
size_t v_sz_boxed_3091_; size_t v_i_boxed_3092_; lean_object* v_res_3093_; 
v_sz_boxed_3091_ = lean_unbox_usize(v_sz_3081_);
lean_dec(v_sz_3081_);
v_i_boxed_3092_ = lean_unbox_usize(v_i_3082_);
lean_dec(v_i_3082_);
v_res_3093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3080_, v_sz_boxed_3091_, v_i_boxed_3092_, v_b_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec_ref(v_as_3080_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3094_, size_t v_sz_3095_, size_t v_i_3096_, lean_object* v_b_3097_){
_start:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_lt(v_i_3096_, v_sz_3095_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_b_3097_);
return v___x_3100_;
}
else
{
lean_object* v_snd_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3119_; 
v_snd_3101_ = lean_ctor_get(v_b_3097_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_b_3097_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v_b_3097_, 0);
lean_dec(v_unused_3120_);
v___x_3103_ = v_b_3097_;
v_isShared_3104_ = v_isSharedCheck_3119_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_snd_3101_);
lean_dec(v_b_3097_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3119_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v_a_3107_; lean_object* v_a_3114_; 
v___x_3105_ = lean_box(0);
v_a_3114_ = lean_array_uget_borrowed(v_as_3094_, v_i_3096_);
if (lean_obj_tag(v_a_3114_) == 0)
{
v_a_3107_ = v_snd_3101_;
goto v___jp_3106_;
}
else
{
lean_object* v_val_3115_; uint8_t v___x_3116_; 
v_val_3115_ = lean_ctor_get(v_a_3114_, 0);
v___x_3116_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_inc(v_val_3115_);
v___x_3117_ = l_Lean_LocalDecl_toExpr(v_val_3115_);
v___x_3118_ = lean_array_push(v_snd_3101_, v___x_3117_);
v_a_3107_ = v___x_3118_;
goto v___jp_3106_;
}
else
{
v_a_3107_ = v_snd_3101_;
goto v___jp_3106_;
}
}
v___jp_3106_:
{
lean_object* v___x_3109_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 1, v_a_3107_);
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3109_ = v___x_3103_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3107_);
v___x_3109_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
size_t v___x_3110_; size_t v___x_3111_; 
v___x_3110_ = ((size_t)1ULL);
v___x_3111_ = lean_usize_add(v_i_3096_, v___x_3110_);
v_i_3096_ = v___x_3111_;
v_b_3097_ = v___x_3109_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3121_, lean_object* v_sz_3122_, lean_object* v_i_3123_, lean_object* v_b_3124_, lean_object* v___y_3125_){
_start:
{
size_t v_sz_boxed_3126_; size_t v_i_boxed_3127_; lean_object* v_res_3128_; 
v_sz_boxed_3126_ = lean_unbox_usize(v_sz_3122_);
lean_dec(v_sz_3122_);
v_i_boxed_3127_ = lean_unbox_usize(v_i_3123_);
lean_dec(v_i_3123_);
v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3121_, v_sz_boxed_3126_, v_i_boxed_3127_, v_b_3124_);
lean_dec_ref(v_as_3121_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3129_, size_t v_sz_3130_, size_t v_i_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
uint8_t v___x_3140_; 
v___x_3140_ = lean_usize_dec_lt(v_i_3131_, v_sz_3130_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v_b_3132_);
return v___x_3141_;
}
else
{
lean_object* v_snd_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3160_; 
v_snd_3142_ = lean_ctor_get(v_b_3132_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_b_3132_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v_b_3132_, 0);
lean_dec(v_unused_3161_);
v___x_3144_ = v_b_3132_;
v_isShared_3145_ = v_isSharedCheck_3160_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_snd_3142_);
lean_dec(v_b_3132_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3160_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v_a_3148_; lean_object* v_a_3155_; 
v___x_3146_ = lean_box(0);
v_a_3155_ = lean_array_uget_borrowed(v_as_3129_, v_i_3131_);
if (lean_obj_tag(v_a_3155_) == 0)
{
v_a_3148_ = v_snd_3142_;
goto v___jp_3147_;
}
else
{
lean_object* v_val_3156_; uint8_t v___x_3157_; 
v_val_3156_ = lean_ctor_get(v_a_3155_, 0);
v___x_3157_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_inc(v_val_3156_);
v___x_3158_ = l_Lean_LocalDecl_toExpr(v_val_3156_);
v___x_3159_ = lean_array_push(v_snd_3142_, v___x_3158_);
v_a_3148_ = v___x_3159_;
goto v___jp_3147_;
}
else
{
v_a_3148_ = v_snd_3142_;
goto v___jp_3147_;
}
}
v___jp_3147_:
{
lean_object* v___x_3150_; 
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 1, v_a_3148_);
lean_ctor_set(v___x_3144_, 0, v___x_3146_);
v___x_3150_ = v___x_3144_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_a_3148_);
v___x_3150_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
size_t v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = ((size_t)1ULL);
v___x_3152_ = lean_usize_add(v_i_3131_, v___x_3151_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3129_, v_sz_3130_, v___x_3152_, v___x_3150_);
return v___x_3153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3162_, lean_object* v_sz_3163_, lean_object* v_i_3164_, lean_object* v_b_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
size_t v_sz_boxed_3173_; size_t v_i_boxed_3174_; lean_object* v_res_3175_; 
v_sz_boxed_3173_ = lean_unbox_usize(v_sz_3163_);
lean_dec(v_sz_3163_);
v_i_boxed_3174_ = lean_unbox_usize(v_i_3164_);
lean_dec(v_i_3164_);
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3162_, v_sz_boxed_3173_, v_i_boxed_3174_, v_b_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec_ref(v_as_3162_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3176_, lean_object* v_n_3177_, lean_object* v_b_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
if (lean_obj_tag(v_n_3177_) == 0)
{
lean_object* v_cs_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; size_t v_sz_3189_; size_t v___x_3190_; lean_object* v___x_3191_; 
v_cs_3186_ = lean_ctor_get(v_n_3177_, 0);
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set(v___x_3188_, 1, v_b_3178_);
v_sz_3189_ = lean_array_size(v_cs_3186_);
v___x_3190_ = ((size_t)0ULL);
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3176_, v_cs_3186_, v_sz_3189_, v___x_3190_, v___x_3188_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3206_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3206_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3206_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v_fst_3196_; 
v_fst_3196_ = lean_ctor_get(v_a_3192_, 0);
if (lean_obj_tag(v_fst_3196_) == 0)
{
lean_object* v_snd_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
v_snd_3197_ = lean_ctor_get(v_a_3192_, 1);
lean_inc(v_snd_3197_);
lean_dec(v_a_3192_);
v___x_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3198_, 0, v_snd_3197_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3198_);
v___x_3200_ = v___x_3194_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
else
{
lean_object* v_val_3202_; lean_object* v___x_3204_; 
lean_inc_ref(v_fst_3196_);
lean_dec(v_a_3192_);
v_val_3202_ = lean_ctor_get(v_fst_3196_, 0);
lean_inc(v_val_3202_);
lean_dec_ref_known(v_fst_3196_, 1);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v_val_3202_);
v___x_3204_ = v___x_3194_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_val_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_a_3207_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3191_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3191_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_vs_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; size_t v_sz_3218_; size_t v___x_3219_; lean_object* v___x_3220_; 
v_vs_3215_ = lean_ctor_get(v_n_3177_, 0);
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v_b_3178_);
v_sz_3218_ = lean_array_size(v_vs_3215_);
v___x_3219_ = ((size_t)0ULL);
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3215_, v_sz_3218_, v___x_3219_, v___x_3217_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3235_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3223_ = v___x_3220_;
v_isShared_3224_ = v_isSharedCheck_3235_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3220_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3235_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v_fst_3225_; 
v_fst_3225_ = lean_ctor_get(v_a_3221_, 0);
if (lean_obj_tag(v_fst_3225_) == 0)
{
lean_object* v_snd_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v_snd_3226_ = lean_ctor_get(v_a_3221_, 1);
lean_inc(v_snd_3226_);
lean_dec(v_a_3221_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_snd_3226_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3227_);
v___x_3229_ = v___x_3223_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
else
{
lean_object* v_val_3231_; lean_object* v___x_3233_; 
lean_inc_ref(v_fst_3225_);
lean_dec(v_a_3221_);
v_val_3231_ = lean_ctor_get(v_fst_3225_, 0);
lean_inc(v_val_3231_);
lean_dec_ref_known(v_fst_3225_, 1);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v_val_3231_);
v___x_3233_ = v___x_3223_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_val_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
v_a_3236_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3220_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3220_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3244_, lean_object* v_as_3245_, size_t v_sz_3246_, size_t v_i_3247_, lean_object* v_b_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_usize_dec_lt(v_i_3247_, v_sz_3246_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_b_3248_);
return v___x_3257_;
}
else
{
lean_object* v_snd_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3292_; 
v_snd_3258_ = lean_ctor_get(v_b_3248_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_b_3248_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; 
v_unused_3293_ = lean_ctor_get(v_b_3248_, 0);
lean_dec(v_unused_3293_);
v___x_3260_ = v_b_3248_;
v_isShared_3261_ = v_isSharedCheck_3292_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_snd_3258_);
lean_dec(v_b_3248_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3292_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_a_3262_; lean_object* v___x_3263_; 
v_a_3262_ = lean_array_uget_borrowed(v_as_3245_, v_i_3247_);
lean_inc(v_snd_3258_);
v___x_3263_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3244_, v_a_3262_, v_snd_3258_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3283_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3283_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3283_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
if (lean_obj_tag(v_a_3264_) == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_a_3264_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3268_);
v___x_3270_ = v___x_3260_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_snd_3258_);
v___x_3270_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
lean_object* v___x_3272_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3270_);
v___x_3272_ = v___x_3266_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_del_object(v___x_3266_);
lean_dec(v_snd_3258_);
v_a_3275_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v_a_3264_, 1);
v___x_3276_ = lean_box(0);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v_a_3275_);
lean_ctor_set(v___x_3260_, 0, v___x_3276_);
v___x_3278_ = v___x_3260_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_a_3275_);
v___x_3278_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
size_t v___x_3279_; size_t v___x_3280_; 
v___x_3279_ = ((size_t)1ULL);
v___x_3280_ = lean_usize_add(v_i_3247_, v___x_3279_);
v_i_3247_ = v___x_3280_;
v_b_3248_ = v___x_3278_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_del_object(v___x_3260_);
lean_dec(v_snd_3258_);
v_a_3284_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3263_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3263_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3294_, lean_object* v_as_3295_, lean_object* v_sz_3296_, lean_object* v_i_3297_, lean_object* v_b_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
size_t v_sz_boxed_3306_; size_t v_i_boxed_3307_; lean_object* v_res_3308_; 
v_sz_boxed_3306_ = lean_unbox_usize(v_sz_3296_);
lean_dec(v_sz_3296_);
v_i_boxed_3307_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3294_, v_as_3295_, v_sz_boxed_3306_, v_i_boxed_3307_, v_b_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_as_3295_);
lean_dec_ref(v_init_3294_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3309_, lean_object* v_n_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3309_, v_n_3310_, v_b_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_n_3310_);
lean_dec_ref(v_init_3309_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3320_, lean_object* v_init_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_root_3329_; lean_object* v_tail_3330_; lean_object* v___x_3331_; 
v_root_3329_ = lean_ctor_get(v_t_3320_, 0);
v_tail_3330_ = lean_ctor_get(v_t_3320_, 1);
lean_inc_ref(v_init_3321_);
v___x_3331_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3321_, v_root_3329_, v_init_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec_ref(v_init_3321_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3368_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3368_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3368_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; 
v_a_3336_ = lean_ctor_get(v_a_3332_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v_a_3332_, 1);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v_a_3336_);
v___x_3338_ = v___x_3334_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; size_t v_sz_3343_; size_t v___x_3344_; lean_object* v___x_3345_; 
lean_del_object(v___x_3334_);
v_a_3340_ = lean_ctor_get(v_a_3332_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v_a_3332_, 1);
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v_a_3340_);
v_sz_3343_ = lean_array_size(v_tail_3330_);
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3330_, v_sz_3343_, v___x_3344_, v___x_3342_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3359_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3359_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3359_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_fst_3350_; 
v_fst_3350_ = lean_ctor_get(v_a_3346_, 0);
if (lean_obj_tag(v_fst_3350_) == 0)
{
lean_object* v_snd_3351_; lean_object* v___x_3353_; 
v_snd_3351_ = lean_ctor_get(v_a_3346_, 1);
lean_inc(v_snd_3351_);
lean_dec(v_a_3346_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_snd_3351_);
v___x_3353_ = v___x_3348_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_snd_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
else
{
lean_object* v_val_3355_; lean_object* v___x_3357_; 
lean_inc_ref(v_fst_3350_);
lean_dec(v_a_3346_);
v_val_3355_ = lean_ctor_get(v_fst_3350_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v_fst_3350_, 1);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_val_3355_);
v___x_3357_ = v___x_3348_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_val_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
v_a_3360_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3345_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3345_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_a_3369_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3331_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3331_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3377_, lean_object* v_init_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3377_, v_init_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v_t_3377_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_lctx_3396_; lean_object* v_decls_3397_; lean_object* v_hs_3398_; lean_object* v___x_3399_; 
v_lctx_3396_ = lean_ctor_get(v___y_3391_, 2);
v_decls_3397_ = lean_ctor_get(v_lctx_3396_, 1);
v_hs_3398_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3399_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3397_, v_hs_3398_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3408_, lean_object* v_cfg_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
if (v_only_3408_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_toApplyRulesConfig_3418_; lean_object* v_a_3419_; uint8_t v_symm_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_toApplyRulesConfig_3418_ = lean_ctor_get(v_cfg_3409_, 0);
v_a_3419_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3417_, 1);
v_symm_3420_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3418_, sizeof(void*)*2 + 1);
v___x_3421_ = lean_array_to_list(v_a_3419_);
v___x_3422_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3420_, v___x_3421_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3422_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
v_a_3423_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3417_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3417_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_box(0);
v___x_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3433_, lean_object* v_cfg_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v_only_boxed_3442_; lean_object* v_res_3443_; 
v_only_boxed_3442_ = lean_unbox(v_only_3433_);
v_res_3443_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3442_, v_cfg_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec_ref(v_cfg_3434_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3444_, lean_object* v_lemmas_3445_, uint8_t v_only_3446_, lean_object* v_g_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_toApplyRulesConfig_3453_; uint8_t v_intro_3454_; uint8_t v_constructor_3455_; uint8_t v_suggestions_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3469_; 
v_toApplyRulesConfig_3453_ = lean_ctor_get(v_cfg_3444_, 0);
v_intro_3454_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*1 + 1);
v_constructor_3455_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*1 + 2);
v_suggestions_3456_ = lean_ctor_get_uint8(v_cfg_3444_, sizeof(void*)*1 + 3);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_cfg_3444_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3458_ = v_cfg_3444_;
v_isShared_3459_ = v_isSharedCheck_3469_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_toApplyRulesConfig_3453_);
lean_dec(v_cfg_3444_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3469_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_ctx_3461_; uint8_t v___x_3462_; lean_object* v___x_3464_; 
v___x_3460_ = lean_box(v_only_3446_);
v_ctx_3461_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3461_, 0, v___x_3460_);
v___x_3462_ = 0;
if (v_isShared_3459_ == 0)
{
v___x_3464_ = v___x_3458_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_toApplyRulesConfig_3453_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*1 + 1, v_intro_3454_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*1 + 2, v_constructor_3455_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*1 + 3, v_suggestions_3456_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*1, v___x_3462_);
v___x_3465_ = lean_box(0);
v___x_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_g_3447_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3464_, v_lemmas_3445_, v_ctx_3461_, v___x_3466_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
return v___x_3467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3470_, lean_object* v_lemmas_3471_, lean_object* v_only_3472_, lean_object* v_g_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
uint8_t v_only_boxed_3479_; lean_object* v_res_3480_; 
v_only_boxed_3479_ = lean_unbox(v_only_3472_);
v_res_3480_ = l_Lean_MVarId_applyRules(v_cfg_3470_, v_lemmas_3471_, v_only_boxed_3479_, v_g_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3481_, size_t v_sz_3482_, size_t v_i_3483_, lean_object* v_b_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3481_, v_sz_3482_, v_i_3483_, v_b_3484_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3493_, lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
size_t v_sz_boxed_3504_; size_t v_i_boxed_3505_; lean_object* v_res_3506_; 
v_sz_boxed_3504_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3505_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3493_, v_sz_boxed_3504_, v_i_boxed_3505_, v_b_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_as_3493_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3507_, size_t v_sz_3508_, size_t v_i_3509_, lean_object* v_b_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3507_, v_sz_3508_, v_i_3509_, v_b_3510_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3519_, lean_object* v_sz_3520_, lean_object* v_i_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
size_t v_sz_boxed_3530_; size_t v_i_boxed_3531_; lean_object* v_res_3532_; 
v_sz_boxed_3530_ = lean_unbox_usize(v_sz_3520_);
lean_dec(v_sz_3520_);
v_i_boxed_3531_ = lean_unbox_usize(v_i_3521_);
lean_dec(v_i_3521_);
v_res_3532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3519_, v_sz_boxed_3530_, v_i_boxed_3531_, v_b_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v_as_3519_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_box(0);
v___x_3542_ = 1;
v___x_3543_ = l_Lean_Elab_Term_elabTerm(v_t_3533_, v___x_3541_, v___x_3542_, v___x_3542_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_ref_3558_; uint8_t v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_ref_3558_ = lean_ctor_get(v___y_3555_, 2);
v___x_3559_ = 0;
v___x_3560_ = l_Lean_SourceInfo_fromRef(v_ref_3558_, v___x_3559_);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
return v_res_3567_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3568_, lean_object* v_x_3569_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
uint8_t v___x_3570_; 
v___x_3570_ = 0;
return v___x_3570_;
}
else
{
lean_object* v_head_3571_; lean_object* v_tail_3572_; uint8_t v___x_3573_; 
v_head_3571_ = lean_ctor_get(v_x_3569_, 0);
v_tail_3572_ = lean_ctor_get(v_x_3569_, 1);
v___x_3573_ = lean_expr_eqv(v_a_3568_, v_head_3571_);
if (v___x_3573_ == 0)
{
v_x_3569_ = v_tail_3572_;
goto _start;
}
else
{
return v___x_3573_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3575_, lean_object* v_x_3576_){
_start:
{
uint8_t v_res_3577_; lean_object* v_r_3578_; 
v_res_3577_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3575_, v_x_3576_);
lean_dec(v_x_3576_);
lean_dec_ref(v_a_3575_);
v_r_3578_ = lean_box(v_res_3577_);
return v_r_3578_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3579_, lean_object* v_x_3580_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3580_, v_ys_3579_);
if (v___x_3581_ == 0)
{
uint8_t v___x_3582_; 
v___x_3582_ = 1;
return v___x_3582_;
}
else
{
uint8_t v___x_3583_; 
v___x_3583_ = 0;
return v___x_3583_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3584_, lean_object* v_x_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3584_, v_x_3585_);
lean_dec_ref(v_x_3585_);
lean_dec(v_ys_3584_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3588_, lean_object* v_ys_3589_){
_start:
{
lean_object* v___f_3590_; lean_object* v___x_3591_; 
v___f_3590_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3590_, 0, v_ys_3589_);
v___x_3591_ = l_List_filter___redArg(v___f_3590_, v_xs_3588_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = l_List_reverse___redArg(v_x_3593_);
v___x_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
return v___x_3602_;
}
else
{
lean_object* v_head_3603_; lean_object* v_tail_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3622_; 
v_head_3603_ = lean_ctor_get(v_x_3592_, 0);
v_tail_3604_ = lean_ctor_get(v_x_3592_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_x_3592_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3606_ = v_x_3592_;
v_isShared_3607_ = v_isSharedCheck_3622_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_tail_3604_);
lean_inc(v_head_3603_);
lean_dec(v_x_3592_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3622_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; 
v___x_3608_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3603_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3611_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 1, v_x_3593_);
lean_ctor_set(v___x_3606_, 0, v_a_3609_);
v___x_3611_ = v___x_3606_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3609_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_x_3593_);
v___x_3611_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
v_x_3592_ = v_tail_3604_;
v_x_3593_ = v___x_3611_;
goto _start;
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_del_object(v___x_3606_);
lean_dec(v_tail_3604_);
lean_dec(v_x_3593_);
v_a_3614_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3608_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3608_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3623_, lean_object* v_x_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3623_, v_x_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3633_, uint8_t v_noDefaults_3634_, uint8_t v_star_3635_, lean_object* v_cfg_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
if (v_noDefaults_3634_ == 0)
{
goto v___jp_3644_;
}
else
{
if (v_star_3635_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec(v_remove_3633_);
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
else
{
goto v___jp_3644_;
}
}
v___jp_3644_:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v___x_3647_ = lean_box(0);
v___x_3648_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3633_, v___x_3647_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_toApplyRulesConfig_3649_; lean_object* v_a_3650_; uint8_t v_symm_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_toApplyRulesConfig_3649_ = lean_ctor_get(v_cfg_3636_, 0);
v_a_3650_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3648_, 1);
v_symm_3651_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3649_, sizeof(void*)*2 + 1);
v___x_3652_ = lean_array_to_list(v_a_3646_);
v___x_3653_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3652_, v_a_3650_);
v___x_3654_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3651_, v___x_3653_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
return v___x_3654_;
}
else
{
lean_dec(v_a_3646_);
return v___x_3648_;
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_remove_3633_);
v_a_3655_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3645_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3645_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3665_, lean_object* v_noDefaults_3666_, lean_object* v_star_3667_, lean_object* v_cfg_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v_noDefaults_boxed_3676_; uint8_t v_star_boxed_3677_; lean_object* v_res_3678_; 
v_noDefaults_boxed_3676_ = lean_unbox(v_noDefaults_3666_);
v_star_boxed_3677_ = lean_unbox(v_star_3667_);
v_res_3678_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3665_, v_noDefaults_boxed_3676_, v_star_boxed_3677_, v_cfg_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_cfg_3668_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3679_, size_t v_i_3680_, size_t v_stop_3681_, lean_object* v_b_3682_){
_start:
{
uint8_t v___x_3683_; 
v___x_3683_ = lean_usize_dec_eq(v_i_3680_, v_stop_3681_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; 
v___x_3684_ = lean_array_uget_borrowed(v_as_3679_, v_i_3680_);
v___x_3685_ = l_Array_append___redArg(v_b_3682_, v___x_3684_);
v___x_3686_ = ((size_t)1ULL);
v___x_3687_ = lean_usize_add(v_i_3680_, v___x_3686_);
v_i_3680_ = v___x_3687_;
v_b_3682_ = v___x_3685_;
goto _start;
}
else
{
return v_b_3682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3689_, lean_object* v_i_3690_, lean_object* v_stop_3691_, lean_object* v_b_3692_){
_start:
{
size_t v_i_boxed_3693_; size_t v_stop_boxed_3694_; lean_object* v_res_3695_; 
v_i_boxed_3693_ = lean_unbox_usize(v_i_3690_);
lean_dec(v_i_3690_);
v_stop_boxed_3694_ = lean_unbox_usize(v_stop_3691_);
lean_dec(v_stop_3691_);
v_res_3695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3689_, v_i_boxed_3693_, v_stop_boxed_3694_, v_b_3692_);
lean_dec_ref(v_as_3689_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
if (lean_obj_tag(v_a_3696_) == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = l_List_reverse___redArg(v_a_3697_);
return v___x_3698_;
}
else
{
lean_object* v_head_3699_; lean_object* v_tail_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3709_; 
v_head_3699_ = lean_ctor_get(v_a_3696_, 0);
v_tail_3700_ = lean_ctor_get(v_a_3696_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_a_3696_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3702_ = v_a_3696_;
v_isShared_3703_ = v_isSharedCheck_3709_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_tail_3700_);
lean_inc(v_head_3699_);
lean_dec(v_a_3696_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3709_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3704_, 0, v_head_3699_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 1, v_a_3697_);
lean_ctor_set(v___x_3702_, 0, v___x_3704_);
v___x_3706_ = v___x_3702_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_a_3697_);
v___x_3706_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
v_a_3696_ = v_tail_3700_;
v_a_3697_ = v___x_3706_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3710_, size_t v_i_3711_, lean_object* v_bs_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_usize_dec_lt(v_i_3711_, v_sz_3710_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v_bs_3712_);
return v___x_3717_;
}
else
{
lean_object* v_v_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_v_3718_ = lean_array_uget_borrowed(v_bs_3712_, v_i_3711_);
v___x_3719_ = l_Lean_Syntax_getId(v_v_3718_);
v___x_3720_ = l_Lean_labelled(v___x_3719_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v_bs_x27_3723_; size_t v___x_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = lean_unsigned_to_nat(0u);
v_bs_x27_3723_ = lean_array_uset(v_bs_3712_, v_i_3711_, v___x_3722_);
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_add(v_i_3711_, v___x_3724_);
v___x_3726_ = lean_array_uset(v_bs_x27_3723_, v_i_3711_, v_a_3721_);
v_i_3711_ = v___x_3725_;
v_bs_3712_ = v___x_3726_;
goto _start;
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec_ref(v_bs_3712_);
v_a_3728_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3720_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3720_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3736_, lean_object* v_i_3737_, lean_object* v_bs_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
size_t v_sz_boxed_3742_; size_t v_i_boxed_3743_; lean_object* v_res_3744_; 
v_sz_boxed_3742_ = lean_unbox_usize(v_sz_3736_);
lean_dec(v_sz_3736_);
v_i_boxed_3743_ = lean_unbox_usize(v_i_3737_);
lean_dec(v_i_3737_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3742_, v_i_boxed_3743_, v_bs_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3745_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
if (lean_obj_tag(v_a_3763_) == 0)
{
lean_object* v___x_3765_; 
v___x_3765_ = l_List_reverse___redArg(v_a_3764_);
return v___x_3765_;
}
else
{
lean_object* v_head_3766_; lean_object* v_tail_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3776_; 
v_head_3766_ = lean_ctor_get(v_a_3763_, 0);
v_tail_3767_ = lean_ctor_get(v_a_3763_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3763_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3769_ = v_a_3763_;
v_isShared_3770_ = v_isSharedCheck_3776_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_tail_3767_);
lean_inc(v_head_3766_);
lean_dec(v_a_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3776_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___f_3771_; lean_object* v___x_3773_; 
v___f_3771_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3771_, 0, v_head_3766_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 1, v_a_3764_);
lean_ctor_set(v___x_3769_, 0, v___f_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___f_3771_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_a_3764_);
v___x_3773_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
v_a_3763_ = v_tail_3767_;
v_a_3764_ = v___x_3773_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3779_ = l_Lean_stringToMessageData(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3782_ = l_String_toRawSubstring_x27(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3787_ = l_String_toRawSubstring_x27(v___x_3786_);
return v___x_3787_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3792_ = l_String_toRawSubstring_x27(v___x_3791_);
return v___x_3792_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3797_ = l_String_toRawSubstring_x27(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3829_, uint8_t v_star_3830_, lean_object* v_add_3831_, lean_object* v_remove_3832_, lean_object* v_use_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___f_3864_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; 
v___x_3862_ = lean_box(v_noDefaults_3829_);
v___x_3863_ = lean_box(v_star_3830_);
lean_inc(v_remove_3832_);
v___f_3864_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3864_, 0, v_remove_3832_);
lean_closure_set(v___f_3864_, 1, v___x_3862_);
lean_closure_set(v___f_3864_, 2, v___x_3863_);
if (v_star_3830_ == 0)
{
v___y_3881_ = v_a_3834_;
v___y_3882_ = v_a_3835_;
v___y_3883_ = v_a_3836_;
v___y_3884_ = v_a_3837_;
goto v___jp_3880_;
}
else
{
if (v_noDefaults_3829_ == 0)
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v___f_3864_);
lean_dec_ref(v_use_3833_);
lean_dec(v_remove_3832_);
lean_dec(v_add_3831_);
v___x_3941_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3942_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3941_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
else
{
v___y_3881_ = v_a_3834_;
v___y_3882_ = v_a_3835_;
v___y_3883_ = v_a_3836_;
v___y_3884_ = v_a_3837_;
goto v___jp_3880_;
}
}
v___jp_3839_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___y_3841_);
lean_ctor_set(v___x_3842_, 1, v___y_3840_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
v___jp_3844_:
{
uint8_t v___x_3851_; 
v___x_3851_ = l_List_isEmpty___redArg(v_remove_3832_);
lean_dec(v_remove_3832_);
if (v___x_3851_ == 0)
{
if (v_noDefaults_3829_ == 0)
{
v___y_3840_ = v___y_3848_;
v___y_3841_ = v___y_3850_;
goto v___jp_3839_;
}
else
{
if (v_star_3830_ == 0)
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3848_);
v___x_3852_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3853_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3852_, v___y_3847_, v___y_3849_, v___y_3845_, v___y_3846_);
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
else
{
v___y_3840_ = v___y_3848_;
v___y_3841_ = v___y_3850_;
goto v___jp_3839_;
}
}
}
else
{
v___y_3840_ = v___y_3848_;
v___y_3841_ = v___y_3850_;
goto v___jp_3839_;
}
}
v___jp_3865_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_array_to_list(v___y_3872_);
lean_inc(v___y_3871_);
v___x_3874_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3873_, v___y_3871_);
if (v_noDefaults_3829_ == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3831_, v___y_3871_);
v___x_3876_ = l_List_appendTR___redArg(v___x_3875_, v___x_3874_);
v___x_3877_ = l_List_appendTR___redArg(v___x_3876_, v___y_3867_);
v___y_3845_ = v___y_3866_;
v___y_3846_ = v___y_3869_;
v___y_3847_ = v___y_3868_;
v___y_3848_ = v___f_3864_;
v___y_3849_ = v___y_3870_;
v___y_3850_ = v___x_3877_;
goto v___jp_3844_;
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec(v___y_3867_);
v___x_3878_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3831_, v___y_3871_);
v___x_3879_ = l_List_appendTR___redArg(v___x_3878_, v___x_3874_);
v___y_3845_ = v___y_3866_;
v___y_3846_ = v___y_3869_;
v___y_3847_ = v___y_3868_;
v___y_3848_ = v___f_3864_;
v___y_3849_ = v___y_3870_;
v___y_3850_ = v___x_3879_;
goto v___jp_3844_;
}
}
v___jp_3880_:
{
lean_object* v_toCold_3885_; lean_object* v_ref_3886_; lean_object* v_quotContext_3887_; lean_object* v_currMacroScope_3888_; lean_object* v___x_3889_; lean_object* v_a_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; size_t v_sz_3902_; size_t v___x_3903_; lean_object* v___x_3904_; 
v_toCold_3885_ = lean_ctor_get(v___y_3883_, 0);
v_ref_3886_ = lean_ctor_get(v___y_3883_, 2);
v_quotContext_3887_ = lean_ctor_get(v_toCold_3885_, 8);
v_currMacroScope_3888_ = lean_ctor_get(v_toCold_3885_, 9);
v___x_3889_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref(v___x_3889_);
v___x_3891_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3892_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3888_, 2);
lean_inc_n(v_quotContext_3887_, 2);
v___x_3895_ = l_Lean_addMacroScope(v_quotContext_3887_, v___x_3894_, v_currMacroScope_3888_);
v___x_3896_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_3897_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3897_);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3900_ = l_Lean_addMacroScope(v_quotContext_3887_, v___x_3899_, v_currMacroScope_3888_);
v___x_3901_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_3902_ = lean_array_size(v_use_3833_);
v___x_3903_ = ((size_t)0ULL);
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3902_, v___x_3903_, v_use_3833_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v___x_3906_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3888_, 2);
lean_inc_n(v_quotContext_3887_, 2);
v___x_3907_ = l_Lean_addMacroScope(v_quotContext_3887_, v___x_3906_, v_currMacroScope_3888_);
v___x_3908_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_3909_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_3910_ = l_Lean_addMacroScope(v_quotContext_3887_, v___x_3909_, v_currMacroScope_3888_);
v___x_3911_ = 0;
v___x_3912_ = l_Lean_SourceInfo_fromRef(v_ref_3886_, v___x_3911_);
v___x_3913_ = lean_box(0);
v___x_3914_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_3915_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3912_);
lean_ctor_set(v___x_3915_, 1, v___x_3891_);
lean_ctor_set(v___x_3915_, 2, v___x_3895_);
lean_ctor_set(v___x_3915_, 3, v___x_3914_);
v___x_3916_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3917_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3917_, 0, v_a_3890_);
lean_ctor_set(v___x_3917_, 1, v___x_3896_);
lean_ctor_set(v___x_3917_, 2, v___x_3900_);
lean_ctor_set(v___x_3917_, 3, v___x_3916_);
v___x_3918_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3919_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3919_, 0, v_a_3893_);
lean_ctor_set(v___x_3919_, 1, v___x_3901_);
lean_ctor_set(v___x_3919_, 2, v___x_3907_);
lean_ctor_set(v___x_3919_, 3, v___x_3918_);
v___x_3920_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3921_, 0, v_a_3898_);
lean_ctor_set(v___x_3921_, 1, v___x_3908_);
lean_ctor_set(v___x_3921_, 2, v___x_3910_);
lean_ctor_set(v___x_3921_, 3, v___x_3920_);
v___x_3922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v___x_3913_);
v___x_3923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3919_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3917_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3915_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_3925_, v___x_3913_);
v___x_3927_ = lean_unsigned_to_nat(0u);
v___x_3928_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3929_ = lean_array_get_size(v_a_3905_);
v___x_3930_ = lean_nat_dec_lt(v___x_3927_, v___x_3929_);
if (v___x_3930_ == 0)
{
lean_dec(v_a_3905_);
v___y_3866_ = v___y_3883_;
v___y_3867_ = v___x_3926_;
v___y_3868_ = v___y_3881_;
v___y_3869_ = v___y_3884_;
v___y_3870_ = v___y_3882_;
v___y_3871_ = v___x_3913_;
v___y_3872_ = v___x_3928_;
goto v___jp_3865_;
}
else
{
size_t v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = lean_usize_of_nat(v___x_3929_);
v___x_3932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3905_, v___x_3903_, v___x_3931_, v___x_3928_);
lean_dec(v_a_3905_);
v___y_3866_ = v___y_3883_;
v___y_3867_ = v___x_3926_;
v___y_3868_ = v___y_3881_;
v___y_3869_ = v___y_3884_;
v___y_3870_ = v___y_3882_;
v___y_3871_ = v___x_3913_;
v___y_3872_ = v___x_3932_;
goto v___jp_3865_;
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v___x_3900_);
lean_dec(v_a_3898_);
lean_dec(v___x_3895_);
lean_dec(v_a_3893_);
lean_dec(v_a_3890_);
lean_dec_ref(v___f_3864_);
lean_dec(v_remove_3832_);
lean_dec(v_add_3831_);
v_a_3933_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3904_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3904_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3951_, lean_object* v_star_3952_, lean_object* v_add_3953_, lean_object* v_remove_3954_, lean_object* v_use_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
uint8_t v_noDefaults_boxed_3961_; uint8_t v_star_boxed_3962_; lean_object* v_res_3963_; 
v_noDefaults_boxed_3961_ = lean_unbox(v_noDefaults_3951_);
v_star_boxed_3962_ = lean_unbox(v_star_3952_);
v_res_3963_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3961_, v_star_boxed_3962_, v_add_3953_, v_remove_3954_, v_use_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_3964_, size_t v_i_3965_, lean_object* v_bs_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3964_, v_i_3965_, v_bs_3966_, v___y_3969_, v___y_3970_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_3973_, lean_object* v_i_3974_, lean_object* v_bs_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
size_t v_sz_boxed_3981_; size_t v_i_boxed_3982_; lean_object* v_res_3983_; 
v_sz_boxed_3981_ = lean_unbox_usize(v_sz_3973_);
lean_dec(v_sz_3973_);
v_i_boxed_3982_ = lean_unbox_usize(v_i_3974_);
lean_dec(v_i_3974_);
v_res_3983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_3981_, v_i_boxed_3982_, v_bs_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
return v_res_3983_;
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

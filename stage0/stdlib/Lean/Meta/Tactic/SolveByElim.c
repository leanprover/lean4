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
lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* lean_array_uget(lean_object*, size_t);
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
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value),LEAN_SCALAR_PTR_LITERAL(16, 215, 57, 166, 49, 41, 228, 20)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_90_; lean_object* v_traceState_91_; lean_object* v_traces_92_; lean_object* v___x_93_; lean_object* v_traceState_94_; lean_object* v_env_95_; lean_object* v_nextMacroScope_96_; lean_object* v_ngen_97_; lean_object* v_auxDeclNGen_98_; lean_object* v_cache_99_; lean_object* v_recordedDeps_100_; lean_object* v_messages_101_; lean_object* v_infoState_102_; lean_object* v_snapshotTasks_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_122_; 
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
v_recordedDeps_100_ = lean_ctor_get(v___x_93_, 6);
v_messages_101_ = lean_ctor_get(v___x_93_, 7);
v_infoState_102_ = lean_ctor_get(v___x_93_, 8);
v_snapshotTasks_103_ = lean_ctor_get(v___x_93_, 9);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_122_ == 0)
{
v___x_105_ = v___x_93_;
v_isShared_106_ = v_isSharedCheck_122_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snapshotTasks_103_);
lean_inc(v_infoState_102_);
lean_inc(v_messages_101_);
lean_inc(v_recordedDeps_100_);
lean_inc(v_cache_99_);
lean_inc(v_traceState_94_);
lean_inc(v_auxDeclNGen_98_);
lean_inc(v_ngen_97_);
lean_inc(v_nextMacroScope_96_);
lean_inc(v_env_95_);
lean_dec(v___x_93_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_122_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
uint64_t v_tid_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_120_; 
v_tid_107_ = lean_ctor_get_uint64(v_traceState_94_, sizeof(void*)*1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_traceState_94_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v_traceState_94_, 0);
lean_dec(v_unused_121_);
v___x_109_ = v_traceState_94_;
v_isShared_110_ = v_isSharedCheck_120_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_traceState_94_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_120_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_111_);
lean_ctor_set_uint64(v_reuseFailAlloc_119_, sizeof(void*)*1, v_tid_107_);
v___x_113_ = v_reuseFailAlloc_119_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 4, v___x_113_);
v___x_115_ = v___x_105_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_env_95_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_nextMacroScope_96_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_ngen_97_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v_auxDeclNGen_98_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_118_, 5, v_cache_99_);
lean_ctor_set(v_reuseFailAlloc_118_, 6, v_recordedDeps_100_);
lean_ctor_set(v_reuseFailAlloc_118_, 7, v_messages_101_);
lean_ctor_set(v_reuseFailAlloc_118_, 8, v_infoState_102_);
lean_ctor_set(v_reuseFailAlloc_118_, 9, v_snapshotTasks_103_);
v___x_115_ = v_reuseFailAlloc_118_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_st_ref_put(v___y_88_, v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_traces_92_);
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_123_);
lean_dec(v___y_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_138_, lean_object* v_opt_139_){
_start:
{
lean_object* v_name_140_; lean_object* v_defValue_141_; lean_object* v_map_142_; lean_object* v___x_143_; 
v_name_140_ = lean_ctor_get(v_opt_139_, 0);
v_defValue_141_ = lean_ctor_get(v_opt_139_, 1);
v_map_142_ = lean_ctor_get(v_opts_138_, 0);
v___x_143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_142_, v_name_140_);
if (lean_obj_tag(v___x_143_) == 0)
{
uint8_t v___x_144_; 
v___x_144_ = lean_unbox(v_defValue_141_);
return v___x_144_;
}
else
{
lean_object* v_val_145_; 
v_val_145_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v___x_143_, 1);
if (lean_obj_tag(v_val_145_) == 1)
{
uint8_t v_v_146_; 
v_v_146_ = lean_ctor_get_uint8(v_val_145_, 0);
lean_dec_ref_known(v_val_145_, 0);
return v_v_146_;
}
else
{
uint8_t v___x_147_; 
lean_dec(v_val_145_);
v___x_147_ = lean_unbox(v_defValue_141_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_148_, lean_object* v_opt_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_148_, v_opt_149_);
lean_dec_ref(v_opt_149_);
lean_dec_ref(v_opts_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_saveState___redArg(v___y_154_, v___y_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
lean_inc(v___y_156_);
lean_inc_ref(v___y_155_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
v___x_160_ = lean_apply_5(v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, lean_box(0));
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
lean_dec(v_a_159_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_199_; 
v_a_170_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_199_ == 0)
{
v___x_172_ = v___x_160_;
v_isShared_173_ = v_isSharedCheck_199_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_160_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_199_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___y_175_; uint8_t v___x_197_; 
v___x_197_ = l_Lean_Exception_isInterrupt(v_a_170_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
lean_inc(v_a_170_);
v___x_198_ = l_Lean_Exception_isRuntime(v_a_170_);
v___y_175_ = v___x_198_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_197_;
goto v___jp_174_;
}
v___jp_174_:
{
if (v___y_175_ == 0)
{
lean_object* v___x_176_; 
lean_del_object(v___x_172_);
lean_dec(v_a_170_);
v___x_176_ = l_Lean_Meta_SavedState_restore___redArg(v_a_159_, v___y_154_, v___y_156_);
lean_dec(v_a_159_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_176_, 0);
lean_dec(v_unused_185_);
v___x_178_ = v___x_176_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_dec(v___x_176_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_176_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_176_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_a_159_);
if (v_isShared_173_ == 0)
{
v___x_195_ = v___x_172_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_170_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_x_152_);
v_a_200_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_158_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_158_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_215_, lean_object* v_x_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_223_, v_x_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_230_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_234_, lean_object* v_x_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_241_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_242_ = l_Lean_MessageData_ofExpr(v_e_234_);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec_ref(v_x_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_253_, uint8_t v___x_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_x_256_);
return v___x_262_;
}
else
{
lean_object* v_head_263_; lean_object* v_tail_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_288_; 
v_head_263_ = lean_ctor_get(v_x_255_, 0);
v_tail_264_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_288_ == 0)
{
v___x_266_ = v_x_255_;
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_tail_264_);
lean_inc(v_head_263_);
lean_dec(v_x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v_a_269_; lean_object* v___x_275_; 
lean_inc(v_head_263_);
v___x_275_ = l_Lean_MVarId_inferInstance(v_head_263_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref_known(v___x_275_, 1);
v_a_269_ = v___x_253_;
goto v___jp_268_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_287_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_287_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
uint8_t v___y_281_; uint8_t v___x_285_; 
v___x_285_ = l_Lean_Exception_isInterrupt(v_a_276_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
lean_inc(v_a_276_);
v___x_286_ = l_Lean_Exception_isRuntime(v_a_276_);
v___y_281_ = v___x_286_;
goto v___jp_280_;
}
else
{
v___y_281_ = v___x_285_;
goto v___jp_280_;
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
lean_del_object(v___x_278_);
lean_dec(v_a_276_);
v_a_269_ = v___x_254_;
goto v___jp_268_;
}
else
{
lean_object* v___x_283_; 
lean_del_object(v___x_266_);
lean_dec(v_tail_264_);
lean_dec(v_head_263_);
lean_dec(v_x_256_);
if (v_isShared_279_ == 0)
{
v___x_283_ = v___x_278_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_276_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
v___jp_268_:
{
if (v_a_269_ == 0)
{
lean_del_object(v___x_266_);
lean_dec(v_head_263_);
v_x_255_ = v_tail_264_;
goto _start;
}
else
{
lean_object* v___x_272_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v_x_256_);
v___x_272_ = v___x_266_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_head_263_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_x_256_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_x_255_ = v_tail_264_;
v_x_256_ = v___x_272_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_289_, lean_object* v___x_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_13911__boxed_298_; uint8_t v___x_13912__boxed_299_; lean_object* v_res_300_; 
v___x_13911__boxed_298_ = lean_unbox(v___x_289_);
v___x_13912__boxed_299_ = lean_unbox(v___x_290_);
v_res_300_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13911__boxed_298_, v___x_13912__boxed_299_, v_x_291_, v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_env_308_; lean_object* v___x_309_; lean_object* v_toCold_310_; lean_object* v_mctx_311_; lean_object* v_lctx_312_; lean_object* v_options_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v___x_309_ = lean_st_ref_get(v___y_303_);
v_toCold_310_ = lean_ctor_get(v___y_304_, 0);
v_mctx_311_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_mctx_311_);
lean_dec(v___x_309_);
v_lctx_312_ = lean_ctor_get(v___y_302_, 2);
v_options_313_ = lean_ctor_get(v_toCold_310_, 2);
lean_inc_ref(v_options_313_);
lean_inc_ref(v_lctx_312_);
v___x_314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_314_, 0, v_env_308_);
lean_ctor_set(v___x_314_, 1, v_mctx_311_);
lean_ctor_set(v___x_314_, 2, v_lctx_312_);
lean_ctor_set(v___x_314_, 3, v_options_313_);
v___x_315_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_msgData_301_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_324_, size_t v_i_325_, lean_object* v_bs_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_327_ == 0)
{
return v_bs_326_;
}
else
{
lean_object* v_v_328_; lean_object* v_msg_329_; lean_object* v___x_330_; lean_object* v_bs_x27_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_v_328_ = lean_array_uget_borrowed(v_bs_326_, v_i_325_);
v_msg_329_ = lean_ctor_get(v_v_328_, 1);
lean_inc_ref(v_msg_329_);
v___x_330_ = lean_unsigned_to_nat(0u);
v_bs_x27_331_ = lean_array_uset(v_bs_326_, v_i_325_, v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_325_, v___x_332_);
v___x_334_ = lean_array_uset(v_bs_x27_331_, v_i_325_, v_msg_329_);
v_i_325_ = v___x_333_;
v_bs_326_ = v___x_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_336_, lean_object* v_i_337_, lean_object* v_bs_338_){
_start:
{
size_t v_sz_boxed_339_; size_t v_i_boxed_340_; lean_object* v_res_341_; 
v_sz_boxed_339_ = lean_unbox_usize(v_sz_336_);
lean_dec(v_sz_336_);
v_i_boxed_340_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_339_, v_i_boxed_340_, v_bs_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_342_, lean_object* v_data_343_, lean_object* v_ref_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_toCold_351_; lean_object* v_currRecDepth_352_; lean_object* v_ref_353_; uint16_t v_optionFlags_354_; uint8_t v_suppressElabErrors_355_; uint8_t v_isRecordingDeps_356_; lean_object* v_ref_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_traceState_360_; lean_object* v_traces_361_; lean_object* v___x_362_; size_t v_sz_363_; size_t v___x_364_; lean_object* v___x_365_; lean_object* v_msg_366_; lean_object* v___x_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_406_; 
v_toCold_351_ = lean_ctor_get(v___y_348_, 0);
v_currRecDepth_352_ = lean_ctor_get(v___y_348_, 1);
v_ref_353_ = lean_ctor_get(v___y_348_, 2);
v_optionFlags_354_ = lean_ctor_get_uint16(v___y_348_, sizeof(void*)*3);
v_suppressElabErrors_355_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3 + 2);
v_isRecordingDeps_356_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3 + 3);
v_ref_357_ = l_Lean_replaceRef(v_ref_344_, v_ref_353_);
lean_inc(v_currRecDepth_352_);
lean_inc_ref(v_toCold_351_);
v___x_358_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_358_, 0, v_toCold_351_);
lean_ctor_set(v___x_358_, 1, v_currRecDepth_352_);
lean_ctor_set(v___x_358_, 2, v_ref_357_);
lean_ctor_set_uint16(v___x_358_, sizeof(void*)*3, v_optionFlags_354_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*3 + 2, v_suppressElabErrors_355_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*3 + 3, v_isRecordingDeps_356_);
v___x_359_ = lean_st_ref_get(v___y_349_);
v_traceState_360_ = lean_ctor_get(v___x_359_, 4);
lean_inc_ref(v_traceState_360_);
lean_dec(v___x_359_);
v_traces_361_ = lean_ctor_get(v_traceState_360_, 0);
lean_inc_ref(v_traces_361_);
lean_dec_ref(v_traceState_360_);
v___x_362_ = l_Lean_PersistentArray_toArray___redArg(v_traces_361_);
lean_dec_ref(v_traces_361_);
v_sz_363_ = lean_array_size(v___x_362_);
v___x_364_ = ((size_t)0ULL);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_363_, v___x_364_, v___x_362_);
v_msg_366_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_366_, 0, v_data_343_);
lean_ctor_set(v_msg_366_, 1, v_msg_345_);
lean_ctor_set(v_msg_366_, 2, v___x_365_);
v___x_367_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_366_, v___y_346_, v___y_347_, v___x_358_, v___y_349_);
lean_dec_ref_known(v___x_358_, 3);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_406_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_406_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_406_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v_traceState_373_; lean_object* v_env_374_; lean_object* v_nextMacroScope_375_; lean_object* v_ngen_376_; lean_object* v_auxDeclNGen_377_; lean_object* v_cache_378_; lean_object* v_recordedDeps_379_; lean_object* v_messages_380_; lean_object* v_infoState_381_; lean_object* v_snapshotTasks_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_405_; 
v___x_372_ = lean_st_ref_take(v___y_349_);
v_traceState_373_ = lean_ctor_get(v___x_372_, 4);
v_env_374_ = lean_ctor_get(v___x_372_, 0);
v_nextMacroScope_375_ = lean_ctor_get(v___x_372_, 1);
v_ngen_376_ = lean_ctor_get(v___x_372_, 2);
v_auxDeclNGen_377_ = lean_ctor_get(v___x_372_, 3);
v_cache_378_ = lean_ctor_get(v___x_372_, 5);
v_recordedDeps_379_ = lean_ctor_get(v___x_372_, 6);
v_messages_380_ = lean_ctor_get(v___x_372_, 7);
v_infoState_381_ = lean_ctor_get(v___x_372_, 8);
v_snapshotTasks_382_ = lean_ctor_get(v___x_372_, 9);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_405_ == 0)
{
v___x_384_ = v___x_372_;
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_snapshotTasks_382_);
lean_inc(v_infoState_381_);
lean_inc(v_messages_380_);
lean_inc(v_recordedDeps_379_);
lean_inc(v_cache_378_);
lean_inc(v_traceState_373_);
lean_inc(v_auxDeclNGen_377_);
lean_inc(v_ngen_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_env_374_);
lean_dec(v___x_372_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint64_t v_tid_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_403_; 
v_tid_386_ = lean_ctor_get_uint64(v_traceState_373_, sizeof(void*)*1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_traceState_373_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_traceState_373_, 0);
lean_dec(v_unused_404_);
v___x_388_ = v_traceState_373_;
v_isShared_389_ = v_isSharedCheck_403_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_traceState_373_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_403_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_344_);
lean_ctor_set(v___x_391_, 1, v_a_368_);
v___x_392_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_342_, v___x_391_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_392_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_402_, sizeof(void*)*1, v_tid_386_);
v___x_394_ = v_reuseFailAlloc_402_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v___x_394_);
v___x_396_ = v___x_384_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_env_374_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_ngen_376_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_auxDeclNGen_377_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_cache_378_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_recordedDeps_379_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_messages_380_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_infoState_381_);
lean_ctor_set(v_reuseFailAlloc_401_, 9, v_snapshotTasks_382_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_st_ref_put(v___y_349_, v___x_396_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_390_);
v___x_399_ = v___x_370_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_390_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_407_, lean_object* v_data_408_, lean_object* v_ref_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_407_, v_data_408_, v_ref_409_, v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_417_){
_start:
{
if (lean_obj_tag(v_e_417_) == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 2;
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_420_);
lean_dec_ref(v_e_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_423_, lean_object* v_opt_424_){
_start:
{
lean_object* v_name_425_; lean_object* v_defValue_426_; lean_object* v_map_427_; lean_object* v___x_428_; 
v_name_425_ = lean_ctor_get(v_opt_424_, 0);
v_defValue_426_ = lean_ctor_get(v_opt_424_, 1);
v_map_427_ = lean_ctor_get(v_opts_423_, 0);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_427_, v_name_425_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_inc(v_defValue_426_);
return v_defValue_426_;
}
else
{
lean_object* v_val_429_; 
v_val_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_429_);
lean_dec_ref_known(v___x_428_, 1);
if (lean_obj_tag(v_val_429_) == 3)
{
lean_object* v_v_430_; 
v_v_430_ = lean_ctor_get(v_val_429_, 0);
lean_inc(v_v_430_);
lean_dec_ref_known(v_val_429_, 1);
return v_v_430_;
}
else
{
lean_dec(v_val_429_);
lean_inc(v_defValue_426_);
return v_defValue_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_431_, lean_object* v_opt_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_431_, v_opt_432_);
lean_dec_ref(v_opt_432_);
lean_dec_ref(v_opts_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_a_436_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v_x_434_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v_x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 1);
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v_x_434_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v_x_434_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_452_);
return v_res_454_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_455_; double v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_float_of_nat(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_460_; double v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(1000u);
v___x_461_ = lean_float_of_nat(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_462_, uint8_t v_collapsed_463_, lean_object* v_tag_464_, lean_object* v_opts_465_, uint8_t v_clsEnabled_466_, lean_object* v_oldTraces_467_, lean_object* v_msg_468_, lean_object* v_resStartStop_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v_data_480_; lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___y_496_; lean_object* v_a_497_; uint8_t v___y_512_; double v___y_544_; 
v_fst_475_ = lean_ctor_get(v_resStartStop_469_, 0);
lean_inc(v_fst_475_);
v_snd_476_ = lean_ctor_get(v_resStartStop_469_, 1);
lean_inc(v_snd_476_);
lean_dec_ref(v_resStartStop_469_);
v_fst_491_ = lean_ctor_get(v_snd_476_, 0);
lean_inc(v_fst_491_);
v_snd_492_ = lean_ctor_get(v_snd_476_, 1);
lean_inc(v_snd_492_);
lean_dec(v_snd_476_);
v___x_493_ = l_Lean_trace_profiler;
v___x_494_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_465_, v___x_493_);
if (v___x_494_ == 0)
{
v___y_512_ = v___x_494_;
goto v___jp_511_;
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = l_Lean_trace_profiler_useHeartbeats;
v___x_550_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_465_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; double v___x_553_; double v___x_554_; double v___x_555_; 
v___x_551_ = l_Lean_trace_profiler_threshold;
v___x_552_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_465_, v___x_551_);
v___x_553_ = lean_float_of_nat(v___x_552_);
v___x_554_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_555_ = lean_float_div(v___x_553_, v___x_554_);
v___y_544_ = v___x_555_;
goto v___jp_543_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; double v___x_558_; 
v___x_556_ = l_Lean_trace_profiler_threshold;
v___x_557_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_465_, v___x_556_);
v___x_558_ = lean_float_of_nat(v___x_557_);
v___y_544_ = v___x_558_;
goto v___jp_543_;
}
}
v___jp_477_:
{
lean_object* v___x_481_; 
lean_inc(v___y_478_);
v___x_481_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_467_, v_data_480_, v___y_478_, v___y_479_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec_ref_known(v___x_481_, 1);
v___x_482_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_475_);
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_fst_475_);
v_a_483_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_481_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
v___jp_495_:
{
uint8_t v_result_498_; lean_object* v___x_499_; lean_object* v___x_500_; double v___x_501_; lean_object* v_data_502_; 
v_result_498_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_475_);
v___x_499_ = lean_box(v_result_498_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___x_501_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_464_);
lean_inc_ref(v___x_500_);
lean_inc(v_cls_462_);
v_data_502_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_502_, 0, v_cls_462_);
lean_ctor_set(v_data_502_, 1, v___x_500_);
lean_ctor_set(v_data_502_, 2, v_tag_464_);
lean_ctor_set_float(v_data_502_, sizeof(void*)*3, v___x_501_);
lean_ctor_set_float(v_data_502_, sizeof(void*)*3 + 8, v___x_501_);
lean_ctor_set_uint8(v_data_502_, sizeof(void*)*3 + 16, v_collapsed_463_);
if (v___x_494_ == 0)
{
lean_dec_ref_known(v___x_500_, 1);
lean_dec(v_snd_492_);
lean_dec(v_fst_491_);
lean_dec_ref(v_tag_464_);
lean_dec(v_cls_462_);
v___y_478_ = v___y_496_;
v___y_479_ = v_a_497_;
v_data_480_ = v_data_502_;
goto v___jp_477_;
}
else
{
lean_object* v_data_503_; double v___x_504_; double v___x_505_; 
lean_dec_ref_known(v_data_502_, 3);
v_data_503_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_503_, 0, v_cls_462_);
lean_ctor_set(v_data_503_, 1, v___x_500_);
lean_ctor_set(v_data_503_, 2, v_tag_464_);
v___x_504_ = lean_unbox_float(v_fst_491_);
lean_dec(v_fst_491_);
lean_ctor_set_float(v_data_503_, sizeof(void*)*3, v___x_504_);
v___x_505_ = lean_unbox_float(v_snd_492_);
lean_dec(v_snd_492_);
lean_ctor_set_float(v_data_503_, sizeof(void*)*3 + 8, v___x_505_);
lean_ctor_set_uint8(v_data_503_, sizeof(void*)*3 + 16, v_collapsed_463_);
v___y_478_ = v___y_496_;
v___y_479_ = v_a_497_;
v_data_480_ = v_data_503_;
goto v___jp_477_;
}
}
v___jp_506_:
{
lean_object* v_ref_507_; lean_object* v___x_508_; 
v_ref_507_ = lean_ctor_get(v___y_472_, 2);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v_fst_475_);
v___x_508_ = lean_apply_6(v_msg_468_, v_fst_475_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, lean_box(0));
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___y_496_ = v_ref_507_;
v_a_497_ = v_a_509_;
goto v___jp_495_;
}
else
{
lean_object* v___x_510_; 
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_496_ = v_ref_507_;
v_a_497_ = v___x_510_;
goto v___jp_495_;
}
}
v___jp_511_:
{
if (v_clsEnabled_466_ == 0)
{
if (v___y_512_ == 0)
{
lean_object* v___x_513_; lean_object* v_traceState_514_; lean_object* v_env_515_; lean_object* v_nextMacroScope_516_; lean_object* v_ngen_517_; lean_object* v_auxDeclNGen_518_; lean_object* v_cache_519_; lean_object* v_recordedDeps_520_; lean_object* v_messages_521_; lean_object* v_infoState_522_; lean_object* v_snapshotTasks_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_snd_492_);
lean_dec(v_fst_491_);
lean_dec_ref(v_msg_468_);
lean_dec_ref(v_tag_464_);
lean_dec(v_cls_462_);
v___x_513_ = lean_st_ref_take(v___y_473_);
v_traceState_514_ = lean_ctor_get(v___x_513_, 4);
v_env_515_ = lean_ctor_get(v___x_513_, 0);
v_nextMacroScope_516_ = lean_ctor_get(v___x_513_, 1);
v_ngen_517_ = lean_ctor_get(v___x_513_, 2);
v_auxDeclNGen_518_ = lean_ctor_get(v___x_513_, 3);
v_cache_519_ = lean_ctor_get(v___x_513_, 5);
v_recordedDeps_520_ = lean_ctor_get(v___x_513_, 6);
v_messages_521_ = lean_ctor_get(v___x_513_, 7);
v_infoState_522_ = lean_ctor_get(v___x_513_, 8);
v_snapshotTasks_523_ = lean_ctor_get(v___x_513_, 9);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_542_ == 0)
{
v___x_525_ = v___x_513_;
v_isShared_526_ = v_isSharedCheck_542_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snapshotTasks_523_);
lean_inc(v_infoState_522_);
lean_inc(v_messages_521_);
lean_inc(v_recordedDeps_520_);
lean_inc(v_cache_519_);
lean_inc(v_traceState_514_);
lean_inc(v_auxDeclNGen_518_);
lean_inc(v_ngen_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_env_515_);
lean_dec(v___x_513_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_542_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
uint64_t v_tid_527_; lean_object* v_traces_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_541_; 
v_tid_527_ = lean_ctor_get_uint64(v_traceState_514_, sizeof(void*)*1);
v_traces_528_ = lean_ctor_get(v_traceState_514_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_traceState_514_);
if (v_isSharedCheck_541_ == 0)
{
v___x_530_ = v_traceState_514_;
v_isShared_531_ = v_isSharedCheck_541_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_traces_528_);
lean_dec(v_traceState_514_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_541_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_467_, v_traces_528_);
lean_dec_ref(v_traces_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_532_);
lean_ctor_set_uint64(v_reuseFailAlloc_540_, sizeof(void*)*1, v_tid_527_);
v___x_534_ = v_reuseFailAlloc_540_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 4, v___x_534_);
v___x_536_ = v___x_525_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_env_515_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_ngen_517_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_auxDeclNGen_518_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v_cache_519_);
lean_ctor_set(v_reuseFailAlloc_539_, 6, v_recordedDeps_520_);
lean_ctor_set(v_reuseFailAlloc_539_, 7, v_messages_521_);
lean_ctor_set(v_reuseFailAlloc_539_, 8, v_infoState_522_);
lean_ctor_set(v_reuseFailAlloc_539_, 9, v_snapshotTasks_523_);
v___x_536_ = v_reuseFailAlloc_539_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_st_ref_put(v___y_473_, v___x_536_);
v___x_538_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_475_);
return v___x_538_;
}
}
}
}
}
else
{
goto v___jp_506_;
}
}
else
{
goto v___jp_506_;
}
}
v___jp_543_:
{
double v___x_545_; double v___x_546_; double v___x_547_; uint8_t v___x_548_; 
v___x_545_ = lean_unbox_float(v_snd_492_);
v___x_546_ = lean_unbox_float(v_fst_491_);
v___x_547_ = lean_float_sub(v___x_545_, v___x_546_);
v___x_548_ = lean_float_decLt(v___y_544_, v___x_547_);
v___y_512_ = v___x_548_;
goto v___jp_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_559_, lean_object* v_collapsed_560_, lean_object* v_tag_561_, lean_object* v_opts_562_, lean_object* v_clsEnabled_563_, lean_object* v_oldTraces_564_, lean_object* v_msg_565_, lean_object* v_resStartStop_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v_collapsed_boxed_572_; uint8_t v_clsEnabled_boxed_573_; lean_object* v_res_574_; 
v_collapsed_boxed_572_ = lean_unbox(v_collapsed_560_);
v_clsEnabled_boxed_573_ = lean_unbox(v_clsEnabled_563_);
v_res_574_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_559_, v_collapsed_boxed_572_, v_tag_561_, v_opts_562_, v_clsEnabled_boxed_573_, v_oldTraces_564_, v_msg_565_, v_resStartStop_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_opts_562_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_x_577_);
return v___x_583_;
}
else
{
lean_object* v_head_584_; lean_object* v_tail_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_608_; 
v_head_584_ = lean_ctor_get(v_x_576_, 0);
v_tail_585_ = lean_ctor_get(v_x_576_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_608_ == 0)
{
v___x_587_ = v_x_576_;
v_isShared_588_ = v_isSharedCheck_608_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_tail_585_);
lean_inc(v_head_584_);
lean_dec(v_x_576_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_608_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; 
lean_inc(v_head_584_);
v___x_589_ = l_Lean_MVarId_inferInstance(v_head_584_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_dec_ref_known(v___x_589_, 1);
lean_del_object(v___x_587_);
lean_dec(v_head_584_);
v_x_576_ = v_tail_585_;
goto _start;
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_607_; 
v_a_591_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_607_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_607_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_607_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___y_596_; uint8_t v___x_605_; 
v___x_605_ = l_Lean_Exception_isInterrupt(v_a_591_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; 
lean_inc(v_a_591_);
v___x_606_ = l_Lean_Exception_isRuntime(v_a_591_);
v___y_596_ = v___x_606_;
goto v___jp_595_;
}
else
{
v___y_596_ = v___x_605_;
goto v___jp_595_;
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
lean_del_object(v___x_593_);
lean_dec(v_a_591_);
if (v___x_575_ == 0)
{
lean_del_object(v___x_587_);
lean_dec(v_head_584_);
v_x_576_ = v_tail_585_;
goto _start;
}
else
{
lean_object* v___x_599_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_x_577_);
v___x_599_ = v___x_587_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_head_584_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_x_577_);
v___x_599_ = v_reuseFailAlloc_601_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
v_x_576_ = v_tail_585_;
v_x_577_ = v___x_599_;
goto _start;
}
}
}
else
{
lean_object* v___x_603_; 
lean_del_object(v___x_587_);
lean_dec(v_tail_585_);
lean_dec(v_head_584_);
lean_dec(v_x_577_);
if (v_isShared_594_ == 0)
{
v___x_603_ = v___x_593_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_591_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_14336__boxed_617_; lean_object* v_res_618_; 
v___x_14336__boxed_617_ = lean_unbox(v___x_609_);
v_res_618_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14336__boxed_617_, v_x_610_, v_x_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_x_621_);
return v___x_627_;
}
else
{
lean_object* v_head_628_; lean_object* v_tail_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_652_; 
v_head_628_ = lean_ctor_get(v_x_620_, 0);
v_tail_629_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_652_ == 0)
{
v___x_631_ = v_x_620_;
v_isShared_632_ = v_isSharedCheck_652_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_tail_629_);
lean_inc(v_head_628_);
lean_dec(v_x_620_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_652_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_638_; 
lean_inc(v_head_628_);
v___x_638_ = l_Lean_MVarId_inferInstance(v_head_628_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
if (v___x_619_ == 0)
{
lean_del_object(v___x_631_);
lean_dec(v_head_628_);
v_x_620_ = v_tail_629_;
goto _start;
}
else
{
goto v___jp_633_;
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_651_; 
v_a_640_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_651_ == 0)
{
v___x_642_ = v___x_638_;
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
uint8_t v___y_645_; uint8_t v___x_649_; 
v___x_649_ = l_Lean_Exception_isInterrupt(v_a_640_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
lean_inc(v_a_640_);
v___x_650_ = l_Lean_Exception_isRuntime(v_a_640_);
v___y_645_ = v___x_650_;
goto v___jp_644_;
}
else
{
v___y_645_ = v___x_649_;
goto v___jp_644_;
}
v___jp_644_:
{
if (v___y_645_ == 0)
{
lean_del_object(v___x_642_);
lean_dec(v_a_640_);
goto v___jp_633_;
}
else
{
lean_object* v___x_647_; 
lean_del_object(v___x_631_);
lean_dec(v_tail_629_);
lean_dec(v_head_628_);
lean_dec(v_x_621_);
if (v_isShared_643_ == 0)
{
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_640_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
v___jp_633_:
{
lean_object* v___x_635_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_x_621_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_head_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_x_621_);
v___x_635_ = v_reuseFailAlloc_637_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v_x_620_ = v_tail_629_;
v_x_621_ = v___x_635_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v___x_14413__boxed_661_; lean_object* v_res_662_; 
v___x_14413__boxed_661_ = lean_unbox(v___x_653_);
v_res_662_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14413__boxed_661_, v_x_654_, v_x_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_662_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_666_; double v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(1000000000u);
v___x_667_ = lean_float_of_nat(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_668_, lean_object* v_g_669_, lean_object* v_e_670_, lean_object* v_cfg_671_, lean_object* v___x_672_, lean_object* v___x_673_, uint8_t v___x_674_, lean_object* v___x_675_, lean_object* v___f_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_toCold_682_; lean_object* v_options_683_; lean_object* v_inheritedTraceOptions_684_; uint8_t v_hasTrace_685_; lean_object* v___y_687_; 
v_toCold_682_ = lean_ctor_get(v___y_679_, 0);
v_options_683_ = lean_ctor_get(v_toCold_682_, 2);
v_inheritedTraceOptions_684_ = lean_ctor_get(v_toCold_682_, 11);
v_hasTrace_685_ = lean_ctor_get_uint8(v_options_683_, sizeof(void*)*1);
if (v_hasTrace_685_ == 0)
{
lean_object* v___x_708_; uint8_t v_transparency_709_; uint8_t v___x_710_; 
lean_dec_ref(v___f_676_);
lean_dec_ref(v___x_675_);
lean_dec(v___x_673_);
v___x_708_ = l_Lean_Meta_Context_config(v___y_677_);
v_transparency_709_ = lean_ctor_get_uint8(v___x_708_, 9);
lean_dec_ref(v___x_708_);
v___x_710_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_709_, v_transparency_668_);
if (v___x_710_ == 0)
{
lean_object* v_keyedConfig_711_; uint8_t v_trackZetaDelta_712_; lean_object* v_zetaDeltaSet_713_; lean_object* v_lctx_714_; lean_object* v_localInstances_715_; lean_object* v_defEqCtx_x3f_716_; lean_object* v_synthPendingDepth_717_; lean_object* v_customCanUnfoldPredicate_x3f_718_; uint8_t v_univApprox_719_; uint8_t v_inTypeClassResolution_720_; uint8_t v_cacheInferType_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_keyedConfig_711_ = lean_ctor_get(v___y_677_, 0);
v_trackZetaDelta_712_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7);
v_zetaDeltaSet_713_ = lean_ctor_get(v___y_677_, 1);
v_lctx_714_ = lean_ctor_get(v___y_677_, 2);
v_localInstances_715_ = lean_ctor_get(v___y_677_, 3);
v_defEqCtx_x3f_716_ = lean_ctor_get(v___y_677_, 4);
v_synthPendingDepth_717_ = lean_ctor_get(v___y_677_, 5);
v_customCanUnfoldPredicate_x3f_718_ = lean_ctor_get(v___y_677_, 6);
v_univApprox_719_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_720_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 2);
v_cacheInferType_721_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_711_);
v___x_722_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_668_, v_keyedConfig_711_);
lean_inc(v_customCanUnfoldPredicate_x3f_718_);
lean_inc(v_synthPendingDepth_717_);
lean_inc(v_defEqCtx_x3f_716_);
lean_inc_ref(v_localInstances_715_);
lean_inc_ref(v_lctx_714_);
lean_inc(v_zetaDeltaSet_713_);
v___x_723_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_zetaDeltaSet_713_);
lean_ctor_set(v___x_723_, 2, v_lctx_714_);
lean_ctor_set(v___x_723_, 3, v_localInstances_715_);
lean_ctor_set(v___x_723_, 4, v_defEqCtx_x3f_716_);
lean_ctor_set(v___x_723_, 5, v_synthPendingDepth_717_);
lean_ctor_set(v___x_723_, 6, v_customCanUnfoldPredicate_x3f_718_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7, v_trackZetaDelta_712_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7 + 1, v_univApprox_719_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7 + 2, v_inTypeClassResolution_720_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7 + 3, v_cacheInferType_721_);
v___x_724_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___x_723_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref_known(v___x_723_, 7);
v___y_687_ = v___x_724_;
goto v___jp_686_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v___y_687_ = v___x_725_;
goto v___jp_686_;
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v_a_732_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v_a_747_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v_a_752_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v_a_770_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v_a_782_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_a_787_; lean_object* v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_793_; 
v___x_726_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_673_);
v___x_727_ = l_Lean_Name_append(v___x_726_, v___x_673_);
v___x_728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_684_, v_options_683_, v___x_727_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; lean_object* v___y_848_; 
v___x_845_ = l_Lean_trace_profiler;
v___x_846_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_683_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_869_; uint8_t v_transparency_870_; uint8_t v___x_871_; 
lean_dec_ref(v___f_676_);
lean_dec_ref(v___x_675_);
lean_dec(v___x_673_);
v___x_869_ = l_Lean_Meta_Context_config(v___y_677_);
v_transparency_870_ = lean_ctor_get_uint8(v___x_869_, 9);
lean_dec_ref(v___x_869_);
v___x_871_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_870_, v_transparency_668_);
if (v___x_871_ == 0)
{
lean_object* v_keyedConfig_872_; uint8_t v_trackZetaDelta_873_; lean_object* v_zetaDeltaSet_874_; lean_object* v_lctx_875_; lean_object* v_localInstances_876_; lean_object* v_defEqCtx_x3f_877_; lean_object* v_synthPendingDepth_878_; lean_object* v_customCanUnfoldPredicate_x3f_879_; uint8_t v_univApprox_880_; uint8_t v_inTypeClassResolution_881_; uint8_t v_cacheInferType_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_keyedConfig_872_ = lean_ctor_get(v___y_677_, 0);
v_trackZetaDelta_873_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7);
v_zetaDeltaSet_874_ = lean_ctor_get(v___y_677_, 1);
v_lctx_875_ = lean_ctor_get(v___y_677_, 2);
v_localInstances_876_ = lean_ctor_get(v___y_677_, 3);
v_defEqCtx_x3f_877_ = lean_ctor_get(v___y_677_, 4);
v_synthPendingDepth_878_ = lean_ctor_get(v___y_677_, 5);
v_customCanUnfoldPredicate_x3f_879_ = lean_ctor_get(v___y_677_, 6);
v_univApprox_880_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_881_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 2);
v_cacheInferType_882_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_872_);
v___x_883_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_668_, v_keyedConfig_872_);
lean_inc(v_customCanUnfoldPredicate_x3f_879_);
lean_inc(v_synthPendingDepth_878_);
lean_inc(v_defEqCtx_x3f_877_);
lean_inc_ref(v_localInstances_876_);
lean_inc_ref(v_lctx_875_);
lean_inc(v_zetaDeltaSet_874_);
v___x_884_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_zetaDeltaSet_874_);
lean_ctor_set(v___x_884_, 2, v_lctx_875_);
lean_ctor_set(v___x_884_, 3, v_localInstances_876_);
lean_ctor_set(v___x_884_, 4, v_defEqCtx_x3f_877_);
lean_ctor_set(v___x_884_, 5, v_synthPendingDepth_878_);
lean_ctor_set(v___x_884_, 6, v_customCanUnfoldPredicate_x3f_879_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7, v_trackZetaDelta_873_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7 + 1, v_univApprox_880_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7 + 2, v_inTypeClassResolution_881_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7 + 3, v_cacheInferType_882_);
v___x_885_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___x_884_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref_known(v___x_884_, 7);
v___y_848_ = v___x_885_;
goto v___jp_847_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v___y_848_ = v___x_886_;
goto v___jp_847_;
}
}
else
{
goto v___jp_802_;
}
v___jp_847_:
{
if (lean_obj_tag(v___y_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_849_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___y_848_, 1);
v___x_850_ = lean_box(0);
v___x_851_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_846_, v_hasTrace_685_, v_a_849_, v___x_850_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___y_677_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = l_List_reverse___redArg(v_a_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
return v___x_851_;
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v___y_677_);
v_a_861_ = lean_ctor_get(v___y_848_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___y_848_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___y_848_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___y_848_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
goto v___jp_802_;
}
v___jp_729_:
{
lean_object* v___x_733_; double v___x_734_; double v___x_735_; double v___x_736_; double v___x_737_; double v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_733_ = lean_io_mono_nanos_now();
v___x_734_ = lean_float_of_nat(v___y_731_);
v___x_735_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_736_ = lean_float_div(v___x_734_, v___x_735_);
v___x_737_ = lean_float_of_nat(v___x_733_);
v___x_738_ = lean_float_div(v___x_737_, v___x_735_);
v___x_739_ = lean_box_float(v___x_736_);
v___x_740_ = lean_box_float(v___x_738_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_a_732_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_673_, v___x_674_, v___x_675_, v_options_683_, v___x_728_, v___y_730_, v___f_676_, v___x_742_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___y_677_);
return v___x_743_;
}
v___jp_744_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v_a_747_);
v___y_730_ = v___y_746_;
v___y_731_ = v___y_745_;
v_a_732_ = v___x_748_;
goto v___jp_729_;
}
v___jp_749_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v_a_752_);
v___y_730_ = v___y_751_;
v___y_731_ = v___y_750_;
v_a_732_ = v___x_753_;
goto v___jp_729_;
}
v___jp_754_:
{
if (lean_obj_tag(v___y_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v___y_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___y_758_, 1);
v___x_760_ = lean_box(0);
v___x_761_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_757_, v_hasTrace_685_, v_a_759_, v___x_760_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = l_List_reverse___redArg(v_a_762_);
v___y_750_ = v___y_756_;
v___y_751_ = v___y_755_;
v_a_752_ = v___x_763_;
goto v___jp_749_;
}
else
{
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_761_, 1);
v___y_750_ = v___y_756_;
v___y_751_ = v___y_755_;
v_a_752_ = v_a_764_;
goto v___jp_749_;
}
else
{
lean_object* v_a_765_; 
v_a_765_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_761_, 1);
v___y_745_ = v___y_756_;
v___y_746_ = v___y_755_;
v_a_747_ = v_a_765_;
goto v___jp_744_;
}
}
}
else
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___y_758_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___y_758_, 1);
v___y_745_ = v___y_756_;
v___y_746_ = v___y_755_;
v_a_747_ = v_a_766_;
goto v___jp_744_;
}
}
v___jp_767_:
{
lean_object* v___x_771_; double v___x_772_; double v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_771_ = lean_io_get_num_heartbeats();
v___x_772_ = lean_float_of_nat(v___y_768_);
v___x_773_ = lean_float_of_nat(v___x_771_);
v___x_774_ = lean_box_float(v___x_772_);
v___x_775_ = lean_box_float(v___x_773_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_a_770_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_673_, v___x_674_, v___x_675_, v_options_683_, v___x_728_, v___y_769_, v___f_676_, v___x_777_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___y_677_);
return v___x_778_;
}
v___jp_779_:
{
lean_object* v___x_783_; 
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_a_782_);
v___y_768_ = v___y_780_;
v___y_769_ = v___y_781_;
v_a_770_ = v___x_783_;
goto v___jp_767_;
}
v___jp_784_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_a_787_);
v___y_768_ = v___y_785_;
v___y_769_ = v___y_786_;
v_a_770_ = v___x_788_;
goto v___jp_767_;
}
v___jp_789_:
{
if (lean_obj_tag(v___y_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_a_794_ = lean_ctor_get(v___y_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___y_793_, 1);
v___x_795_ = lean_box(0);
v___x_796_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_792_, v_a_794_, v___x_795_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_List_reverse___redArg(v_a_797_);
v___y_785_ = v___y_790_;
v___y_786_ = v___y_791_;
v_a_787_ = v___x_798_;
goto v___jp_784_;
}
else
{
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_796_, 1);
v___y_785_ = v___y_790_;
v___y_786_ = v___y_791_;
v_a_787_ = v_a_799_;
goto v___jp_784_;
}
else
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_796_, 1);
v___y_780_ = v___y_790_;
v___y_781_ = v___y_791_;
v_a_782_ = v_a_800_;
goto v___jp_779_;
}
}
}
else
{
lean_object* v_a_801_; 
v_a_801_ = lean_ctor_get(v___y_793_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___y_793_, 1);
v___y_780_ = v___y_790_;
v___y_781_ = v___y_791_;
v_a_782_ = v_a_801_;
goto v___jp_779_;
}
}
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v_a_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_803_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_680_);
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v___x_805_ = l_Lean_trace_profiler_useHeartbeats;
v___x_806_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_683_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v_transparency_809_; uint8_t v___x_810_; 
v___x_807_ = lean_io_mono_nanos_now();
v___x_808_ = l_Lean_Meta_Context_config(v___y_677_);
v_transparency_809_ = lean_ctor_get_uint8(v___x_808_, 9);
lean_dec_ref(v___x_808_);
v___x_810_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_809_, v_transparency_668_);
if (v___x_810_ == 0)
{
lean_object* v_keyedConfig_811_; uint8_t v_trackZetaDelta_812_; lean_object* v_zetaDeltaSet_813_; lean_object* v_lctx_814_; lean_object* v_localInstances_815_; lean_object* v_defEqCtx_x3f_816_; lean_object* v_synthPendingDepth_817_; lean_object* v_customCanUnfoldPredicate_x3f_818_; uint8_t v_univApprox_819_; uint8_t v_inTypeClassResolution_820_; uint8_t v_cacheInferType_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_keyedConfig_811_ = lean_ctor_get(v___y_677_, 0);
v_trackZetaDelta_812_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7);
v_zetaDeltaSet_813_ = lean_ctor_get(v___y_677_, 1);
v_lctx_814_ = lean_ctor_get(v___y_677_, 2);
v_localInstances_815_ = lean_ctor_get(v___y_677_, 3);
v_defEqCtx_x3f_816_ = lean_ctor_get(v___y_677_, 4);
v_synthPendingDepth_817_ = lean_ctor_get(v___y_677_, 5);
v_customCanUnfoldPredicate_x3f_818_ = lean_ctor_get(v___y_677_, 6);
v_univApprox_819_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_820_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 2);
v_cacheInferType_821_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_811_);
v___x_822_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_668_, v_keyedConfig_811_);
lean_inc(v_customCanUnfoldPredicate_x3f_818_);
lean_inc(v_synthPendingDepth_817_);
lean_inc(v_defEqCtx_x3f_816_);
lean_inc_ref(v_localInstances_815_);
lean_inc_ref(v_lctx_814_);
lean_inc(v_zetaDeltaSet_813_);
v___x_823_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_zetaDeltaSet_813_);
lean_ctor_set(v___x_823_, 2, v_lctx_814_);
lean_ctor_set(v___x_823_, 3, v_localInstances_815_);
lean_ctor_set(v___x_823_, 4, v_defEqCtx_x3f_816_);
lean_ctor_set(v___x_823_, 5, v_synthPendingDepth_817_);
lean_ctor_set(v___x_823_, 6, v_customCanUnfoldPredicate_x3f_818_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*7, v_trackZetaDelta_812_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*7 + 1, v_univApprox_819_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*7 + 2, v_inTypeClassResolution_820_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*7 + 3, v_cacheInferType_821_);
v___x_824_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___x_823_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref_known(v___x_823_, 7);
v___y_755_ = v_a_804_;
v___y_756_ = v___x_807_;
v___y_757_ = v___x_806_;
v___y_758_ = v___x_824_;
goto v___jp_754_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v___y_755_ = v_a_804_;
v___y_756_ = v___x_807_;
v___y_757_ = v___x_806_;
v___y_758_ = v___x_825_;
goto v___jp_754_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v_transparency_828_; uint8_t v___x_829_; 
v___x_826_ = lean_io_get_num_heartbeats();
v___x_827_ = l_Lean_Meta_Context_config(v___y_677_);
v_transparency_828_ = lean_ctor_get_uint8(v___x_827_, 9);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_828_, v_transparency_668_);
if (v___x_829_ == 0)
{
lean_object* v_keyedConfig_830_; uint8_t v_trackZetaDelta_831_; lean_object* v_zetaDeltaSet_832_; lean_object* v_lctx_833_; lean_object* v_localInstances_834_; lean_object* v_defEqCtx_x3f_835_; lean_object* v_synthPendingDepth_836_; lean_object* v_customCanUnfoldPredicate_x3f_837_; uint8_t v_univApprox_838_; uint8_t v_inTypeClassResolution_839_; uint8_t v_cacheInferType_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_keyedConfig_830_ = lean_ctor_get(v___y_677_, 0);
v_trackZetaDelta_831_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7);
v_zetaDeltaSet_832_ = lean_ctor_get(v___y_677_, 1);
v_lctx_833_ = lean_ctor_get(v___y_677_, 2);
v_localInstances_834_ = lean_ctor_get(v___y_677_, 3);
v_defEqCtx_x3f_835_ = lean_ctor_get(v___y_677_, 4);
v_synthPendingDepth_836_ = lean_ctor_get(v___y_677_, 5);
v_customCanUnfoldPredicate_x3f_837_ = lean_ctor_get(v___y_677_, 6);
v_univApprox_838_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_839_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 2);
v_cacheInferType_840_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_830_);
v___x_841_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_668_, v_keyedConfig_830_);
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
v___x_843_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___x_842_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref_known(v___x_842_, 7);
v___y_790_ = v___x_826_;
v___y_791_ = v_a_804_;
v___y_792_ = v___x_806_;
v___y_793_ = v___x_843_;
goto v___jp_789_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_MVarId_apply(v_g_669_, v_e_670_, v_cfg_671_, v___x_672_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v___y_790_ = v___x_826_;
v___y_791_ = v_a_804_;
v___y_792_ = v___x_806_;
v___y_793_ = v___x_844_;
goto v___jp_789_;
}
}
}
}
v___jp_686_:
{
if (lean_obj_tag(v___y_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_a_688_ = lean_ctor_get(v___y_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___y_687_, 1);
v___x_689_ = lean_box(0);
v___x_690_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_685_, v_a_688_, v___x_689_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___y_677_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = l_List_reverse___redArg(v_a_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
return v___x_690_;
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v___y_677_);
v_a_700_ = lean_ctor_get(v___y_687_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___y_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___y_687_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___y_687_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_887_, lean_object* v_g_888_, lean_object* v_e_889_, lean_object* v_cfg_890_, lean_object* v___x_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v___f_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v_transparency_boxed_901_; uint8_t v___x_14501__boxed_902_; lean_object* v_res_903_; 
v_transparency_boxed_901_ = lean_unbox(v_transparency_887_);
v___x_14501__boxed_902_ = lean_unbox(v___x_893_);
v_res_903_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_901_, v_g_888_, v_e_889_, v_cfg_890_, v___x_891_, v___x_892_, v___x_14501__boxed_902_, v___x_894_, v___f_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_905_, lean_object* v_g_906_, lean_object* v_cfg_907_, lean_object* v_e_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
lean_inc_ref(v_e_908_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_914_, 0, v_e_908_);
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_916_ = lean_box(0);
v___x_917_ = 1;
v___x_918_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_919_ = lean_box(v_transparency_905_);
v___x_920_ = lean_box(v___x_917_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_921_, 0, v___x_919_);
lean_closure_set(v___f_921_, 1, v_g_906_);
lean_closure_set(v___f_921_, 2, v_e_908_);
lean_closure_set(v___f_921_, 3, v_cfg_907_);
lean_closure_set(v___f_921_, 4, v___x_916_);
lean_closure_set(v___f_921_, 5, v___x_915_);
lean_closure_set(v___f_921_, 6, v___x_920_);
lean_closure_set(v___f_921_, 7, v___x_918_);
lean_closure_set(v___f_921_, 8, v___f_914_);
v___x_922_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_921_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_923_, lean_object* v_g_924_, lean_object* v_cfg_925_, lean_object* v_e_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v_transparency_boxed_932_; lean_object* v_res_933_; 
v_transparency_boxed_932_ = lean_unbox(v_transparency_923_);
v_res_933_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_932_, v_g_924_, v_cfg_925_, v_e_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_934_, uint8_t v_transparency_935_, lean_object* v_lemmas_936_, lean_object* v_g_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v___f_942_; lean_object* v___x_943_; 
v___x_941_ = lean_box(v_transparency_935_);
v___f_942_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_942_, 0, v___x_941_);
lean_closure_set(v___f_942_, 1, v_g_937_);
lean_closure_set(v___f_942_, 2, v_cfg_934_);
v___x_943_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_936_, v_a_938_, v_a_939_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_952_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_952_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, lean_box(0));
lean_closure_set(v___x_948_, 2, v___f_942_);
lean_closure_set(v___x_948_, 3, v_a_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___f_942_);
v_a_953_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_943_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_943_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_961_, lean_object* v_transparency_962_, lean_object* v_lemmas_963_, lean_object* v_g_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
uint8_t v_transparency_boxed_968_; lean_object* v_res_969_; 
v_transparency_boxed_968_ = lean_unbox(v_transparency_962_);
v_res_969_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_961_, v_transparency_boxed_968_, v_lemmas_963_, v_g_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec(v_a_965_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_970_, uint8_t v_transparency_971_, lean_object* v_lemmas_972_, lean_object* v_g_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_970_, v_transparency_971_, v_lemmas_972_, v_g_973_, v_a_975_, v_a_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_980_, lean_object* v_transparency_981_, lean_object* v_lemmas_982_, lean_object* v_g_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
uint8_t v_transparency_boxed_989_; lean_object* v_res_990_; 
v_transparency_boxed_989_ = lean_unbox(v_transparency_981_);
v_res_990_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_980_, v_transparency_boxed_989_, v_lemmas_982_, v_g_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_992_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_999_, v_x_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1007_, uint8_t v_transparency_1008_, lean_object* v_lemmas_1009_, lean_object* v_g_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1007_, v_transparency_1008_, v_lemmas_1009_, v_g_1010_, v_a_1012_, v_a_1014_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = l_Lean_Meta_Iterator_head___redArg(v_a_1017_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1016_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1027_, lean_object* v_transparency_1028_, lean_object* v_lemmas_1029_, lean_object* v_g_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
uint8_t v_transparency_boxed_1036_; lean_object* v_res_1037_; 
v_transparency_boxed_1036_ = lean_unbox(v_transparency_1028_);
v_res_1037_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1027_, v_transparency_boxed_1036_, v_lemmas_1029_, v_g_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1038_){
_start:
{
lean_object* v_toApplyRulesConfig_1039_; lean_object* v_toBacktrackConfig_1040_; 
v_toApplyRulesConfig_1039_ = lean_ctor_get(v_x_1038_, 0);
v_toBacktrackConfig_1040_ = lean_ctor_get(v_toApplyRulesConfig_1039_, 0);
lean_inc_ref(v_toBacktrackConfig_1040_);
return v_toBacktrackConfig_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1041_);
lean_dec_ref(v_x_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1045_, lean_object* v_discharge_1046_, lean_object* v_g_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v_g_1047_);
v___x_1053_ = lean_apply_6(v_test_1045_, v_g_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1064_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1064_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1064_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_unbox(v_a_1054_);
lean_dec(v_a_1054_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_del_object(v___x_1056_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1059_ = lean_apply_6(v_discharge_1046_, v_g_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec(v_g_1047_);
lean_dec_ref(v_discharge_1046_);
v___x_1060_ = lean_box(0);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1060_);
v___x_1062_ = v___x_1056_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_g_1047_);
lean_dec_ref(v_discharge_1046_);
v_a_1065_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1053_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1053_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1073_, lean_object* v_discharge_1074_, lean_object* v_g_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1073_, v_discharge_1074_, v_g_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1082_, lean_object* v_test_1083_){
_start:
{
lean_object* v_toApplyRulesConfig_1084_; lean_object* v_toBacktrackConfig_1085_; uint8_t v_backtracking_1086_; uint8_t v_intro_1087_; uint8_t v_constructor_1088_; uint8_t v_suggestions_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1121_; 
v_toApplyRulesConfig_1084_ = lean_ctor_get(v_cfg_1082_, 0);
lean_inc_ref(v_toApplyRulesConfig_1084_);
v_toBacktrackConfig_1085_ = lean_ctor_get(v_toApplyRulesConfig_1084_, 0);
lean_inc_ref(v_toBacktrackConfig_1085_);
v_backtracking_1086_ = lean_ctor_get_uint8(v_cfg_1082_, sizeof(void*)*1);
v_intro_1087_ = lean_ctor_get_uint8(v_cfg_1082_, sizeof(void*)*1 + 1);
v_constructor_1088_ = lean_ctor_get_uint8(v_cfg_1082_, sizeof(void*)*1 + 2);
v_suggestions_1089_ = lean_ctor_get_uint8(v_cfg_1082_, sizeof(void*)*1 + 3);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_cfg_1082_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_cfg_1082_, 0);
lean_dec(v_unused_1122_);
v___x_1091_ = v_cfg_1082_;
v_isShared_1092_ = v_isSharedCheck_1121_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_cfg_1082_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1121_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_toApplyConfig_1093_; uint8_t v_transparency_1094_; uint8_t v_symm_1095_; uint8_t v_exfalso_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1119_; 
v_toApplyConfig_1093_ = lean_ctor_get(v_toApplyRulesConfig_1084_, 1);
v_transparency_1094_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1084_, sizeof(void*)*2);
v_symm_1095_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1084_, sizeof(void*)*2 + 1);
v_exfalso_1096_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1084_, sizeof(void*)*2 + 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_toApplyRulesConfig_1084_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_toApplyRulesConfig_1084_, 0);
lean_dec(v_unused_1120_);
v___x_1098_ = v_toApplyRulesConfig_1084_;
v_isShared_1099_ = v_isSharedCheck_1119_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_toApplyConfig_1093_);
lean_dec(v_toApplyRulesConfig_1084_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1119_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_maxDepth_1100_; lean_object* v_proc_1101_; lean_object* v_suspend_1102_; lean_object* v_discharge_1103_; uint8_t v_commitIndependentGoals_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1118_; 
v_maxDepth_1100_ = lean_ctor_get(v_toBacktrackConfig_1085_, 0);
v_proc_1101_ = lean_ctor_get(v_toBacktrackConfig_1085_, 1);
v_suspend_1102_ = lean_ctor_get(v_toBacktrackConfig_1085_, 2);
v_discharge_1103_ = lean_ctor_get(v_toBacktrackConfig_1085_, 3);
v_commitIndependentGoals_1104_ = lean_ctor_get_uint8(v_toBacktrackConfig_1085_, sizeof(void*)*4);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_toBacktrackConfig_1085_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1106_ = v_toBacktrackConfig_1085_;
v_isShared_1107_ = v_isSharedCheck_1118_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_discharge_1103_);
lean_inc(v_suspend_1102_);
lean_inc(v_proc_1101_);
lean_inc(v_maxDepth_1100_);
lean_dec(v_toBacktrackConfig_1085_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1118_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___f_1108_; lean_object* v___x_1110_; 
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1108_, 0, v_test_1083_);
lean_closure_set(v___f_1108_, 1, v_discharge_1103_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 3, v___f_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_maxDepth_1100_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_proc_1101_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_suspend_1102_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v___f_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1117_, sizeof(void*)*4, v_commitIndependentGoals_1104_);
v___x_1110_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1110_);
v___x_1112_ = v___x_1098_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_toApplyConfig_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1116_, sizeof(void*)*2, v_transparency_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1116_, sizeof(void*)*2 + 1, v_symm_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1116_, sizeof(void*)*2 + 2, v_exfalso_1096_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1112_);
v___x_1114_ = v___x_1091_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*1, v_backtracking_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*1 + 1, v_intro_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*1 + 2, v_constructor_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*1 + 3, v_suggestions_1089_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1123_, lean_object* v_proc_1124_, lean_object* v_orig_1125_, lean_object* v_goals_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
if (lean_obj_tag(v_goals_1126_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_proc_1124_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
v___x_1132_ = lean_apply_7(v_proc_1123_, v_orig_1125_, v_goals_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, lean_box(0));
return v___x_1132_;
}
else
{
lean_object* v_head_1133_; lean_object* v_tail_1134_; lean_object* v___x_1135_; 
v_head_1133_ = lean_ctor_get(v_goals_1126_, 0);
v_tail_1134_ = lean_ctor_get(v_goals_1126_, 1);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
lean_inc(v_head_1133_);
v___x_1135_ = lean_apply_6(v_proc_1124_, v_head_1133_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, lean_box(0));
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1145_; 
lean_inc(v_tail_1134_);
lean_dec_ref_known(v_goals_1126_, 2);
lean_dec(v_orig_1125_);
lean_dec_ref(v_proc_1123_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1140_ = l_List_appendTR___redArg(v_a_1136_, v_tail_1134_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1158_; 
v_a_1146_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1148_ = v___x_1135_;
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1135_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___y_1151_; uint8_t v___x_1156_; 
v___x_1156_ = l_Lean_Exception_isInterrupt(v_a_1146_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; 
lean_inc(v_a_1146_);
v___x_1157_ = l_Lean_Exception_isRuntime(v_a_1146_);
v___y_1151_ = v___x_1157_;
goto v___jp_1150_;
}
else
{
v___y_1151_ = v___x_1156_;
goto v___jp_1150_;
}
v___jp_1150_:
{
if (v___y_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_del_object(v___x_1148_);
lean_dec(v_a_1146_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
v___x_1152_ = lean_apply_7(v_proc_1123_, v_orig_1125_, v_goals_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, lean_box(0));
return v___x_1152_;
}
else
{
lean_object* v___x_1154_; 
lean_dec_ref_known(v_goals_1126_, 2);
lean_dec(v_orig_1125_);
lean_dec_ref(v_proc_1123_);
if (v_isShared_1149_ == 0)
{
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1146_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1159_, lean_object* v_proc_1160_, lean_object* v_orig_1161_, lean_object* v_goals_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1159_, v_proc_1160_, v_orig_1161_, v_goals_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1169_, lean_object* v_proc_1170_){
_start:
{
lean_object* v_toApplyRulesConfig_1171_; lean_object* v_toBacktrackConfig_1172_; uint8_t v_backtracking_1173_; uint8_t v_intro_1174_; uint8_t v_constructor_1175_; uint8_t v_suggestions_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1208_; 
v_toApplyRulesConfig_1171_ = lean_ctor_get(v_cfg_1169_, 0);
lean_inc_ref(v_toApplyRulesConfig_1171_);
v_toBacktrackConfig_1172_ = lean_ctor_get(v_toApplyRulesConfig_1171_, 0);
lean_inc_ref(v_toBacktrackConfig_1172_);
v_backtracking_1173_ = lean_ctor_get_uint8(v_cfg_1169_, sizeof(void*)*1);
v_intro_1174_ = lean_ctor_get_uint8(v_cfg_1169_, sizeof(void*)*1 + 1);
v_constructor_1175_ = lean_ctor_get_uint8(v_cfg_1169_, sizeof(void*)*1 + 2);
v_suggestions_1176_ = lean_ctor_get_uint8(v_cfg_1169_, sizeof(void*)*1 + 3);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_cfg_1169_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_cfg_1169_, 0);
lean_dec(v_unused_1209_);
v___x_1178_ = v_cfg_1169_;
v_isShared_1179_ = v_isSharedCheck_1208_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_cfg_1169_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1208_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_toApplyConfig_1180_; uint8_t v_transparency_1181_; uint8_t v_symm_1182_; uint8_t v_exfalso_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1206_; 
v_toApplyConfig_1180_ = lean_ctor_get(v_toApplyRulesConfig_1171_, 1);
v_transparency_1181_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1171_, sizeof(void*)*2);
v_symm_1182_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1171_, sizeof(void*)*2 + 1);
v_exfalso_1183_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1171_, sizeof(void*)*2 + 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_toApplyRulesConfig_1171_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v_toApplyRulesConfig_1171_, 0);
lean_dec(v_unused_1207_);
v___x_1185_ = v_toApplyRulesConfig_1171_;
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_toApplyConfig_1180_);
lean_dec(v_toApplyRulesConfig_1171_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_maxDepth_1187_; lean_object* v_proc_1188_; lean_object* v_suspend_1189_; lean_object* v_discharge_1190_; uint8_t v_commitIndependentGoals_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1205_; 
v_maxDepth_1187_ = lean_ctor_get(v_toBacktrackConfig_1172_, 0);
v_proc_1188_ = lean_ctor_get(v_toBacktrackConfig_1172_, 1);
v_suspend_1189_ = lean_ctor_get(v_toBacktrackConfig_1172_, 2);
v_discharge_1190_ = lean_ctor_get(v_toBacktrackConfig_1172_, 3);
v_commitIndependentGoals_1191_ = lean_ctor_get_uint8(v_toBacktrackConfig_1172_, sizeof(void*)*4);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_toBacktrackConfig_1172_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1193_ = v_toBacktrackConfig_1172_;
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_discharge_1190_);
lean_inc(v_suspend_1189_);
lean_inc(v_proc_1188_);
lean_inc(v_maxDepth_1187_);
lean_dec(v_toBacktrackConfig_1172_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___f_1195_; lean_object* v___x_1197_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1195_, 0, v_proc_1188_);
lean_closure_set(v___f_1195_, 1, v_proc_1170_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___f_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_maxDepth_1187_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___f_1195_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_suspend_1189_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_discharge_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*4, v_commitIndependentGoals_1191_);
v___x_1197_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1197_);
v___x_1199_ = v___x_1185_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_toApplyConfig_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*2, v_transparency_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*2 + 1, v_symm_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*2 + 2, v_exfalso_1183_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1199_);
v___x_1201_ = v___x_1178_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, sizeof(void*)*1, v_backtracking_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, sizeof(void*)*1 + 1, v_intro_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, sizeof(void*)*1 + 2, v_constructor_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, sizeof(void*)*1 + 3, v_suggestions_1176_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = 1;
v___x_1217_ = l_Lean_Meta_intro1Core(v_g_1210_, v___x_1216_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1235_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1235_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1235_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_snd_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1233_; 
v_snd_1222_ = lean_ctor_get(v_a_1218_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_a_1218_, 0);
lean_dec(v_unused_1234_);
v___x_1224_ = v_a_1218_;
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_snd_1222_);
lean_dec(v_a_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_box(0);
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 1);
lean_ctor_set(v___x_1224_, 1, v___x_1226_);
lean_ctor_set(v___x_1224_, 0, v_snd_1222_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_snd_1222_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1228_);
v___x_1230_ = v___x_1220_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_a_1236_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1217_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1217_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1252_){
_start:
{
lean_object* v___f_1253_; lean_object* v___x_1254_; 
v___f_1253_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1254_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1252_, v___f_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_ks_1259_; lean_object* v_vs_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1284_; 
v_ks_1259_ = lean_ctor_get(v_x_1255_, 0);
v_vs_1260_ = lean_ctor_get(v_x_1255_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1262_ = v_x_1255_;
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_vs_1260_);
lean_inc(v_ks_1259_);
lean_dec(v_x_1255_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = lean_array_get_size(v_ks_1259_);
v___x_1265_ = lean_nat_dec_lt(v_x_1256_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_dec(v_x_1256_);
v___x_1266_ = lean_array_push(v_ks_1259_, v_x_1257_);
v___x_1267_ = lean_array_push(v_vs_1260_, v_x_1258_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1267_);
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1269_ = v___x_1262_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
else
{
lean_object* v_k_x27_1271_; uint8_t v___x_1272_; 
v_k_x27_1271_ = lean_array_fget_borrowed(v_ks_1259_, v_x_1256_);
v___x_1272_ = l_Lean_instBEqMVarId_beq(v_x_1257_, v_k_x27_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1274_; 
if (v_isShared_1263_ == 0)
{
v___x_1274_ = v___x_1262_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_ks_1259_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_vs_1260_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v_x_1256_, v___x_1275_);
lean_dec(v_x_1256_);
v_x_1255_ = v___x_1274_;
v_x_1256_ = v___x_1276_;
goto _start;
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_array_fset(v_ks_1259_, v_x_1256_, v_x_1257_);
v___x_1280_ = lean_array_fset(v_vs_1260_, v_x_1256_, v_x_1258_);
lean_dec(v_x_1256_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1280_);
lean_ctor_set(v___x_1262_, 0, v___x_1279_);
v___x_1282_ = v___x_1262_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1285_, lean_object* v_k_1286_, lean_object* v_v_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1285_, v___x_1288_, v_k_1286_, v_v_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1291_, size_t v_x_1292_, size_t v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v_es_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v_j_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_es_1296_ = lean_ctor_get(v_x_1291_, 0);
v___x_1297_ = ((size_t)31ULL);
v___x_1298_ = lean_usize_land(v_x_1292_, v___x_1297_);
v_j_1299_ = lean_usize_to_nat(v___x_1298_);
v___x_1300_ = lean_array_get_size(v_es_1296_);
v___x_1301_ = lean_nat_dec_lt(v_j_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v_j_1299_);
lean_dec(v_x_1295_);
lean_dec(v_x_1294_);
return v_x_1291_;
}
else
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1340_; 
lean_inc_ref(v_es_1296_);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_x_1291_, 0);
lean_dec(v_unused_1341_);
v___x_1303_ = v_x_1291_;
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v_x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_v_1305_; lean_object* v___x_1306_; lean_object* v_xs_x27_1307_; lean_object* v___y_1309_; 
v_v_1305_ = lean_array_fget(v_es_1296_, v_j_1299_);
v___x_1306_ = lean_box(0);
v_xs_x27_1307_ = lean_array_fset(v_es_1296_, v_j_1299_, v___x_1306_);
switch(lean_obj_tag(v_v_1305_))
{
case 0:
{
lean_object* v_key_1314_; lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1325_; 
v_key_1314_ = lean_ctor_get(v_v_1305_, 0);
v_val_1315_ = lean_ctor_get(v_v_1305_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1317_ = v_v_1305_;
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_inc(v_key_1314_);
lean_dec(v_v_1305_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_instBEqMVarId_beq(v_x_1294_, v_key_1314_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_del_object(v___x_1317_);
v___x_1320_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1314_, v_val_1315_, v_x_1294_, v_x_1295_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___y_1309_ = v___x_1321_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_val_1315_);
lean_dec(v_key_1314_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_x_1295_);
lean_ctor_set(v___x_1317_, 0, v_x_1294_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_x_1294_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_x_1295_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v___y_1309_ = v___x_1323_;
goto v___jp_1308_;
}
}
}
}
case 1:
{
lean_object* v_node_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1338_; 
v_node_1326_ = lean_ctor_get(v_v_1305_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1328_ = v_v_1305_;
v_isShared_1329_ = v_isSharedCheck_1338_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_node_1326_);
lean_dec(v_v_1305_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1338_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1330_ = ((size_t)5ULL);
v___x_1331_ = lean_usize_shift_right(v_x_1292_, v___x_1330_);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_add(v_x_1293_, v___x_1332_);
v___x_1334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1326_, v___x_1331_, v___x_1333_, v_x_1294_, v_x_1295_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1334_);
v___x_1336_ = v___x_1328_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
v___y_1309_ = v___x_1336_;
goto v___jp_1308_;
}
}
}
default: 
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_x_1294_);
lean_ctor_set(v___x_1339_, 1, v_x_1295_);
v___y_1309_ = v___x_1339_;
goto v___jp_1308_;
}
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_array_fset(v_xs_x27_1307_, v_j_1299_, v___y_1309_);
lean_dec(v_j_1299_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1310_);
v___x_1312_ = v___x_1303_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
else
{
lean_object* v_ks_1342_; lean_object* v_vs_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1361_; 
v_ks_1342_ = lean_ctor_get(v_x_1291_, 0);
v_vs_1343_ = lean_ctor_get(v_x_1291_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1345_ = v_x_1291_;
v_isShared_1346_ = v_isSharedCheck_1361_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_vs_1343_);
lean_inc(v_ks_1342_);
lean_dec(v_x_1291_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1361_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_ks_1342_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_vs_1343_);
v___x_1348_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v_newNode_1349_; size_t v___x_1350_; uint8_t v___x_1351_; 
v_newNode_1349_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1348_, v_x_1294_, v_x_1295_);
v___x_1350_ = ((size_t)7ULL);
v___x_1351_ = lean_usize_dec_le(v___x_1350_, v_x_1293_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1352_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1349_);
v___x_1353_ = lean_unsigned_to_nat(4u);
v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
lean_dec(v___x_1352_);
if (v___x_1354_ == 0)
{
lean_object* v_ks_1355_; lean_object* v_vs_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_ks_1355_ = lean_ctor_get(v_newNode_1349_, 0);
lean_inc_ref(v_ks_1355_);
v_vs_1356_ = lean_ctor_get(v_newNode_1349_, 1);
lean_inc_ref(v_vs_1356_);
lean_dec_ref(v_newNode_1349_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1293_, v_ks_1355_, v_vs_1356_, v___x_1357_, v___x_1358_);
lean_dec_ref(v_vs_1356_);
lean_dec_ref(v_ks_1355_);
return v___x_1359_;
}
else
{
return v_newNode_1349_;
}
}
else
{
return v_newNode_1349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1362_, lean_object* v_keys_1363_, lean_object* v_vals_1364_, lean_object* v_i_1365_, lean_object* v_entries_1366_){
_start:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_keys_1363_);
v___x_1368_ = lean_nat_dec_lt(v_i_1365_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_i_1365_);
return v_entries_1366_;
}
else
{
lean_object* v_k_1369_; lean_object* v_v_1370_; uint64_t v___x_1371_; size_t v_h_1372_; size_t v___x_1373_; lean_object* v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; size_t v_h_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_k_1369_ = lean_array_fget_borrowed(v_keys_1363_, v_i_1365_);
v_v_1370_ = lean_array_fget_borrowed(v_vals_1364_, v_i_1365_);
v___x_1371_ = l_Lean_instHashableMVarId_hash(v_k_1369_);
v_h_1372_ = lean_uint64_to_usize(v___x_1371_);
v___x_1373_ = ((size_t)5ULL);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_sub(v_depth_1362_, v___x_1375_);
v___x_1377_ = lean_usize_mul(v___x_1373_, v___x_1376_);
v_h_1378_ = lean_usize_shift_right(v_h_1372_, v___x_1377_);
v___x_1379_ = lean_nat_add(v_i_1365_, v___x_1374_);
lean_dec(v_i_1365_);
lean_inc(v_v_1370_);
lean_inc(v_k_1369_);
v___x_1380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1366_, v_h_1378_, v_depth_1362_, v_k_1369_, v_v_1370_);
v_i_1365_ = v___x_1379_;
v_entries_1366_ = v___x_1380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_i_1385_, lean_object* v_entries_1386_){
_start:
{
size_t v_depth_boxed_1387_; lean_object* v_res_1388_; 
v_depth_boxed_1387_ = lean_unbox_usize(v_depth_1382_);
lean_dec(v_depth_1382_);
v_res_1388_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1387_, v_keys_1383_, v_vals_1384_, v_i_1385_, v_entries_1386_);
lean_dec_ref(v_vals_1384_);
lean_dec_ref(v_keys_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
size_t v_x_835__boxed_1394_; size_t v_x_836__boxed_1395_; lean_object* v_res_1396_; 
v_x_835__boxed_1394_ = lean_unbox_usize(v_x_1390_);
lean_dec(v_x_1390_);
v_x_836__boxed_1395_ = lean_unbox_usize(v_x_1391_);
lean_dec(v_x_1391_);
v_res_1396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1389_, v_x_835__boxed_1394_, v_x_836__boxed_1395_, v_x_1392_, v_x_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
uint64_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = l_Lean_instHashableMVarId_hash(v_x_1398_);
v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1397_, v___x_1401_, v___x_1402_, v_x_1398_, v_x_1399_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1404_, lean_object* v_val_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v_mctx_1409_; lean_object* v_cache_1410_; lean_object* v_zetaDeltaFVarIds_1411_; lean_object* v_postponed_1412_; lean_object* v_diag_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1442_; 
v___x_1408_ = lean_st_ref_take(v___y_1406_);
v_mctx_1409_ = lean_ctor_get(v___x_1408_, 0);
v_cache_1410_ = lean_ctor_get(v___x_1408_, 1);
v_zetaDeltaFVarIds_1411_ = lean_ctor_get(v___x_1408_, 2);
v_postponed_1412_ = lean_ctor_get(v___x_1408_, 3);
v_diag_1413_ = lean_ctor_get(v___x_1408_, 4);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1415_ = v___x_1408_;
v_isShared_1416_ = v_isSharedCheck_1442_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_diag_1413_);
lean_inc(v_postponed_1412_);
lean_inc(v_zetaDeltaFVarIds_1411_);
lean_inc(v_cache_1410_);
lean_inc(v_mctx_1409_);
lean_dec(v___x_1408_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1442_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_depth_1417_; lean_object* v_levelAssignDepth_1418_; lean_object* v_lmvarCounter_1419_; lean_object* v_mvarCounter_1420_; lean_object* v_lDecls_1421_; lean_object* v_decls_1422_; lean_object* v_userNames_1423_; lean_object* v_lAssignment_1424_; lean_object* v_eAssignment_1425_; lean_object* v_dAssignment_1426_; lean_object* v_instanceTypedMVars_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1441_; 
v_depth_1417_ = lean_ctor_get(v_mctx_1409_, 0);
v_levelAssignDepth_1418_ = lean_ctor_get(v_mctx_1409_, 1);
v_lmvarCounter_1419_ = lean_ctor_get(v_mctx_1409_, 2);
v_mvarCounter_1420_ = lean_ctor_get(v_mctx_1409_, 3);
v_lDecls_1421_ = lean_ctor_get(v_mctx_1409_, 4);
v_decls_1422_ = lean_ctor_get(v_mctx_1409_, 5);
v_userNames_1423_ = lean_ctor_get(v_mctx_1409_, 6);
v_lAssignment_1424_ = lean_ctor_get(v_mctx_1409_, 7);
v_eAssignment_1425_ = lean_ctor_get(v_mctx_1409_, 8);
v_dAssignment_1426_ = lean_ctor_get(v_mctx_1409_, 9);
v_instanceTypedMVars_1427_ = lean_ctor_get(v_mctx_1409_, 10);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_mctx_1409_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1429_ = v_mctx_1409_;
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_instanceTypedMVars_1427_);
lean_inc(v_dAssignment_1426_);
lean_inc(v_eAssignment_1425_);
lean_inc(v_lAssignment_1424_);
lean_inc(v_userNames_1423_);
lean_inc(v_decls_1422_);
lean_inc(v_lDecls_1421_);
lean_inc(v_mvarCounter_1420_);
lean_inc(v_lmvarCounter_1419_);
lean_inc(v_levelAssignDepth_1418_);
lean_inc(v_depth_1417_);
lean_dec(v_mctx_1409_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1425_, v_mvarId_1404_, v_val_1405_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 8, v___x_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_depth_1417_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_levelAssignDepth_1418_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_lmvarCounter_1419_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_mvarCounter_1420_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_lDecls_1421_);
lean_ctor_set(v_reuseFailAlloc_1440_, 5, v_decls_1422_);
lean_ctor_set(v_reuseFailAlloc_1440_, 6, v_userNames_1423_);
lean_ctor_set(v_reuseFailAlloc_1440_, 7, v_lAssignment_1424_);
lean_ctor_set(v_reuseFailAlloc_1440_, 8, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1440_, 9, v_dAssignment_1426_);
lean_ctor_set(v_reuseFailAlloc_1440_, 10, v_instanceTypedMVars_1427_);
v___x_1434_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1434_);
v___x_1436_ = v___x_1415_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_cache_1410_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_zetaDeltaFVarIds_1411_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_postponed_1412_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_diag_1413_);
v___x_1436_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_st_ref_put(v___y_1406_, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1431_);
return v___x_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1443_, lean_object* v_val_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1443_, v_val_1444_, v___y_1445_);
lean_dec(v___y_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
lean_inc(v_g_1448_);
v___x_1454_ = l_Lean_MVarId_getType(v_g_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Lean_Meta_synthInstance(v_a_1455_, v___x_1456_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1448_, v_a_1458_, v___y_1450_);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v___x_1459_, 0);
lean_dec(v_unused_1468_);
v___x_1461_ = v___x_1459_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_dec(v___x_1459_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_box(0);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_g_1448_);
v_a_1469_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1457_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1457_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_g_1448_);
v_a_1477_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1454_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1454_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1493_){
_start:
{
lean_object* v___f_1494_; lean_object* v___x_1495_; 
v___f_1494_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1495_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1493_, v___f_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1496_, lean_object* v_val_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1496_, v_val_1497_, v___y_1499_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1504_, lean_object* v_val_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1504_, v_val_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1513_, v_x_1514_, v_x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1517_, lean_object* v_x_1518_, size_t v_x_1519_, size_t v_x_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1518_, v_x_1519_, v_x_1520_, v_x_1521_, v_x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
size_t v_x_1156__boxed_1530_; size_t v_x_1157__boxed_1531_; lean_object* v_res_1532_; 
v_x_1156__boxed_1530_ = lean_unbox_usize(v_x_1526_);
lean_dec(v_x_1526_);
v_x_1157__boxed_1531_ = lean_unbox_usize(v_x_1527_);
lean_dec(v_x_1527_);
v_res_1532_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1524_, v_x_1525_, v_x_1156__boxed_1530_, v_x_1157__boxed_1531_, v_x_1528_, v_x_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1533_, lean_object* v_n_1534_, lean_object* v_k_1535_, lean_object* v_v_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1534_, v_k_1535_, v_v_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1538_, size_t v_depth_1539_, lean_object* v_keys_1540_, lean_object* v_vals_1541_, lean_object* v_heq_1542_, lean_object* v_i_1543_, lean_object* v_entries_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1539_, v_keys_1540_, v_vals_1541_, v_i_1543_, v_entries_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1546_, lean_object* v_depth_1547_, lean_object* v_keys_1548_, lean_object* v_vals_1549_, lean_object* v_heq_1550_, lean_object* v_i_1551_, lean_object* v_entries_1552_){
_start:
{
size_t v_depth_boxed_1553_; lean_object* v_res_1554_; 
v_depth_boxed_1553_ = lean_unbox_usize(v_depth_1547_);
lean_dec(v_depth_1547_);
v_res_1554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1546_, v_depth_boxed_1553_, v_keys_1548_, v_vals_1549_, v_heq_1550_, v_i_1551_, v_entries_1552_);
lean_dec_ref(v_vals_1549_);
lean_dec_ref(v_keys_1548_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1556_, v_x_1557_, v_x_1558_, v_x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1561_, lean_object* v_discharge_1562_, lean_object* v_g_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
lean_inc(v_g_1563_);
v___x_1569_ = lean_apply_6(v_discharge_1561_, v_g_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, lean_box(0));
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_dec(v_g_1563_);
lean_dec_ref(v_discharge_1562_);
return v___x_1569_;
}
else
{
lean_object* v_a_1570_; uint8_t v___y_1572_; uint8_t v___x_1574_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
v___x_1574_ = l_Lean_Exception_isInterrupt(v_a_1570_);
if (v___x_1574_ == 0)
{
uint8_t v___x_1575_; 
v___x_1575_ = l_Lean_Exception_isRuntime(v_a_1570_);
v___y_1572_ = v___x_1575_;
goto v___jp_1571_;
}
else
{
lean_dec(v_a_1570_);
v___y_1572_ = v___x_1574_;
goto v___jp_1571_;
}
v___jp_1571_:
{
if (v___y_1572_ == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1569_, 1);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
v___x_1573_ = lean_apply_6(v_discharge_1562_, v_g_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, lean_box(0));
return v___x_1573_;
}
else
{
lean_dec(v_g_1563_);
lean_dec_ref(v_discharge_1562_);
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1576_, lean_object* v_discharge_1577_, lean_object* v_g_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1576_, v_discharge_1577_, v_g_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1585_, lean_object* v_discharge_1586_){
_start:
{
lean_object* v_toApplyRulesConfig_1587_; lean_object* v_toBacktrackConfig_1588_; uint8_t v_backtracking_1589_; uint8_t v_intro_1590_; uint8_t v_constructor_1591_; uint8_t v_suggestions_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1624_; 
v_toApplyRulesConfig_1587_ = lean_ctor_get(v_cfg_1585_, 0);
lean_inc_ref(v_toApplyRulesConfig_1587_);
v_toBacktrackConfig_1588_ = lean_ctor_get(v_toApplyRulesConfig_1587_, 0);
lean_inc_ref(v_toBacktrackConfig_1588_);
v_backtracking_1589_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*1);
v_intro_1590_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*1 + 1);
v_constructor_1591_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*1 + 2);
v_suggestions_1592_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*1 + 3);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_cfg_1585_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v_cfg_1585_, 0);
lean_dec(v_unused_1625_);
v___x_1594_ = v_cfg_1585_;
v_isShared_1595_ = v_isSharedCheck_1624_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_cfg_1585_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1624_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_toApplyConfig_1596_; uint8_t v_transparency_1597_; uint8_t v_symm_1598_; uint8_t v_exfalso_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1622_; 
v_toApplyConfig_1596_ = lean_ctor_get(v_toApplyRulesConfig_1587_, 1);
v_transparency_1597_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1587_, sizeof(void*)*2);
v_symm_1598_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1587_, sizeof(void*)*2 + 1);
v_exfalso_1599_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1587_, sizeof(void*)*2 + 2);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_toApplyRulesConfig_1587_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v_toApplyRulesConfig_1587_, 0);
lean_dec(v_unused_1623_);
v___x_1601_ = v_toApplyRulesConfig_1587_;
v_isShared_1602_ = v_isSharedCheck_1622_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_toApplyConfig_1596_);
lean_dec(v_toApplyRulesConfig_1587_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1622_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_maxDepth_1603_; lean_object* v_proc_1604_; lean_object* v_suspend_1605_; lean_object* v_discharge_1606_; uint8_t v_commitIndependentGoals_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1621_; 
v_maxDepth_1603_ = lean_ctor_get(v_toBacktrackConfig_1588_, 0);
v_proc_1604_ = lean_ctor_get(v_toBacktrackConfig_1588_, 1);
v_suspend_1605_ = lean_ctor_get(v_toBacktrackConfig_1588_, 2);
v_discharge_1606_ = lean_ctor_get(v_toBacktrackConfig_1588_, 3);
v_commitIndependentGoals_1607_ = lean_ctor_get_uint8(v_toBacktrackConfig_1588_, sizeof(void*)*4);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_toBacktrackConfig_1588_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1609_ = v_toBacktrackConfig_1588_;
v_isShared_1610_ = v_isSharedCheck_1621_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_discharge_1606_);
lean_inc(v_suspend_1605_);
lean_inc(v_proc_1604_);
lean_inc(v_maxDepth_1603_);
lean_dec(v_toBacktrackConfig_1588_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1621_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___f_1611_; lean_object* v___x_1613_; 
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1611_, 0, v_discharge_1586_);
lean_closure_set(v___f_1611_, 1, v_discharge_1606_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v___f_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_maxDepth_1603_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_proc_1604_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_suspend_1605_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v___f_1611_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*4, v_commitIndependentGoals_1607_);
v___x_1613_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1613_);
v___x_1615_ = v___x_1601_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_toApplyConfig_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*2, v_transparency_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*2 + 1, v_symm_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*2 + 2, v_exfalso_1599_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1617_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1615_);
v___x_1617_ = v___x_1594_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*1, v_backtracking_1589_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*1 + 1, v_intro_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*1 + 2, v_constructor_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*1 + 3, v_suggestions_1592_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = 1;
v___x_1633_ = l_Lean_Meta_intro1Core(v_g_1626_, v___x_1632_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1652_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1652_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1652_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_snd_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1650_; 
v_snd_1638_ = lean_ctor_get(v_a_1634_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_a_1634_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v_a_1634_, 0);
lean_dec(v_unused_1651_);
v___x_1640_ = v_a_1634_;
v_isShared_1641_ = v_isSharedCheck_1650_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_snd_1638_);
lean_dec(v_a_1634_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1650_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 1, v___x_1642_);
lean_ctor_set(v___x_1640_, 0, v_snd_1638_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_snd_1638_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1645_);
v___x_1647_ = v___x_1636_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1633_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1633_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1669_){
_start:
{
lean_object* v___f_1670_; lean_object* v___x_1671_; 
v___f_1670_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1671_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1669_, v___f_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1683_ = l_Lean_MVarId_constructor(v_g_1676_, v___x_1682_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_a_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1709_){
_start:
{
lean_object* v___f_1710_; lean_object* v___x_1711_; 
v___f_1710_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1711_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1709_, v___f_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
lean_inc(v_g_1714_);
v___x_1720_ = l_Lean_MVarId_getType(v_g_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_box(0);
v___x_1723_ = l_Lean_Meta_synthInstance(v_a_1721_, v___x_1722_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1714_, v_a_1724_, v___y_1716_);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1725_, 0);
lean_dec(v_unused_1734_);
v___x_1727_ = v___x_1725_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v___x_1725_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_g_1714_);
v_a_1735_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1723_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1723_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v_g_1714_);
v_a_1743_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1720_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1720_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1759_){
_start:
{
lean_object* v___f_1760_; lean_object* v___x_1761_; 
v___f_1760_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1761_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1759_, v___f_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_Expr_hasMVar(v_e_1762_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_e_1762_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v_mctx_1768_; lean_object* v___x_1769_; lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___x_1772_; lean_object* v_cache_1773_; lean_object* v_zetaDeltaFVarIds_1774_; lean_object* v_postponed_1775_; lean_object* v_diag_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v___x_1767_ = lean_st_ref_get(v___y_1763_);
v_mctx_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc_ref(v_mctx_1768_);
lean_dec(v___x_1767_);
v___x_1769_ = l_Lean_instantiateMVarsCore(v_mctx_1768_, v_e_1762_);
v_fst_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_fst_1770_);
v_snd_1771_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_snd_1771_);
lean_dec_ref(v___x_1769_);
v___x_1772_ = lean_st_ref_take(v___y_1763_);
v_cache_1773_ = lean_ctor_get(v___x_1772_, 1);
v_zetaDeltaFVarIds_1774_ = lean_ctor_get(v___x_1772_, 2);
v_postponed_1775_ = lean_ctor_get(v___x_1772_, 3);
v_diag_1776_ = lean_ctor_get(v___x_1772_, 4);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v___x_1772_, 0);
lean_dec(v_unused_1786_);
v___x_1778_ = v___x_1772_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_diag_1776_);
lean_inc(v_postponed_1775_);
lean_inc(v_zetaDeltaFVarIds_1774_);
lean_inc(v_cache_1773_);
lean_dec(v___x_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v_snd_1771_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_snd_1771_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_cache_1773_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_zetaDeltaFVarIds_1774_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_postponed_1775_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_diag_1776_);
v___x_1781_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_st_ref_put(v___y_1763_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_fst_1770_);
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1787_, v___y_1788_);
lean_dec(v___y_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1791_, v___y_1793_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1805_, lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1805_, v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1812_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1812_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1829_, lean_object* v_x_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1829_, v_x_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1837_, lean_object* v_mvarId_1838_, lean_object* v_x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1838_, v_x_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_mvarId_1847_, lean_object* v_x_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1846_, v_mvarId_1847_, v_x_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_ref_1861_; lean_object* v___x_1862_; lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_ref_1861_ = lean_ctor_get(v___y_1858_, 2);
v___x_1862_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_inc(v_ref_1861_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_ref_1861_);
lean_ctor_set(v___x_1867_, 1, v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 1);
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = l_List_reverse___redArg(v_x_1880_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
else
{
lean_object* v_head_1888_; lean_object* v_tail_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1909_; 
v_head_1888_ = lean_ctor_get(v_x_1879_, 0);
v_tail_1889_ = lean_ctor_get(v_x_1879_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1891_ = v_x_1879_;
v_isShared_1892_ = v_isSharedCheck_1909_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_tail_1889_);
lean_inc(v_head_1888_);
lean_dec(v_x_1879_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1909_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_inc(v_head_1888_);
v___x_1893_ = l_Lean_Expr_mvar___override(v_head_1888_);
v___x_1894_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1894_, 0, v___x_1893_);
v___x_1895_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1888_, v___x_1894_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_x_1880_);
lean_ctor_set(v___x_1891_, 0, v_a_1896_);
v___x_1898_ = v___x_1891_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1896_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_x_1880_);
v___x_1898_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v_x_1879_ = v_tail_1889_;
v_x_1880_ = v___x_1898_;
goto _start;
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_del_object(v___x_1891_);
lean_dec(v_tail_1889_);
lean_dec(v_x_1880_);
v_a_1901_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1895_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1895_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1910_, lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1910_, v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1917_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1921_, lean_object* v_proc_1922_, lean_object* v_orig_1923_, lean_object* v_goals_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_box(0);
lean_inc(v_orig_1923_);
v___x_1931_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1923_, v___x_1930_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
v___x_1933_ = lean_apply_6(v_test_1921_, v_a_1932_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, lean_box(0));
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; uint8_t v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = lean_unbox(v_a_1934_);
lean_dec(v_a_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_goals_1924_);
lean_dec(v_orig_1923_);
lean_dec_ref(v_proc_1922_);
v___x_1936_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1937_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1936_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
lean_object* v___x_1946_; 
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
v___x_1946_ = lean_apply_7(v_proc_1922_, v_orig_1923_, v_goals_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, lean_box(0));
return v___x_1946_;
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_goals_1924_);
lean_dec(v_orig_1923_);
lean_dec_ref(v_proc_1922_);
v_a_1947_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1933_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1933_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
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
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_goals_1924_);
lean_dec(v_orig_1923_);
lean_dec_ref(v_proc_1922_);
lean_dec_ref(v_test_1921_);
v_a_1955_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1931_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1931_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1963_, lean_object* v_proc_1964_, lean_object* v_orig_1965_, lean_object* v_goals_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1963_, v_proc_1964_, v_orig_1965_, v_goals_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1973_, lean_object* v_test_1974_){
_start:
{
lean_object* v_toApplyRulesConfig_1975_; lean_object* v_toBacktrackConfig_1976_; uint8_t v_backtracking_1977_; uint8_t v_intro_1978_; uint8_t v_constructor_1979_; uint8_t v_suggestions_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2012_; 
v_toApplyRulesConfig_1975_ = lean_ctor_get(v_cfg_1973_, 0);
lean_inc_ref(v_toApplyRulesConfig_1975_);
v_toBacktrackConfig_1976_ = lean_ctor_get(v_toApplyRulesConfig_1975_, 0);
lean_inc_ref(v_toBacktrackConfig_1976_);
v_backtracking_1977_ = lean_ctor_get_uint8(v_cfg_1973_, sizeof(void*)*1);
v_intro_1978_ = lean_ctor_get_uint8(v_cfg_1973_, sizeof(void*)*1 + 1);
v_constructor_1979_ = lean_ctor_get_uint8(v_cfg_1973_, sizeof(void*)*1 + 2);
v_suggestions_1980_ = lean_ctor_get_uint8(v_cfg_1973_, sizeof(void*)*1 + 3);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_cfg_1973_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v_cfg_1973_, 0);
lean_dec(v_unused_2013_);
v___x_1982_ = v_cfg_1973_;
v_isShared_1983_ = v_isSharedCheck_2012_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v_cfg_1973_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2012_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_toApplyConfig_1984_; uint8_t v_transparency_1985_; uint8_t v_symm_1986_; uint8_t v_exfalso_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2010_; 
v_toApplyConfig_1984_ = lean_ctor_get(v_toApplyRulesConfig_1975_, 1);
v_transparency_1985_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1975_, sizeof(void*)*2);
v_symm_1986_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1975_, sizeof(void*)*2 + 1);
v_exfalso_1987_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1975_, sizeof(void*)*2 + 2);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_toApplyRulesConfig_1975_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_toApplyRulesConfig_1975_, 0);
lean_dec(v_unused_2011_);
v___x_1989_ = v_toApplyRulesConfig_1975_;
v_isShared_1990_ = v_isSharedCheck_2010_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_toApplyConfig_1984_);
lean_dec(v_toApplyRulesConfig_1975_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2010_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_maxDepth_1991_; lean_object* v_proc_1992_; lean_object* v_suspend_1993_; lean_object* v_discharge_1994_; uint8_t v_commitIndependentGoals_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2009_; 
v_maxDepth_1991_ = lean_ctor_get(v_toBacktrackConfig_1976_, 0);
v_proc_1992_ = lean_ctor_get(v_toBacktrackConfig_1976_, 1);
v_suspend_1993_ = lean_ctor_get(v_toBacktrackConfig_1976_, 2);
v_discharge_1994_ = lean_ctor_get(v_toBacktrackConfig_1976_, 3);
v_commitIndependentGoals_1995_ = lean_ctor_get_uint8(v_toBacktrackConfig_1976_, sizeof(void*)*4);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_toBacktrackConfig_1976_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1997_ = v_toBacktrackConfig_1976_;
v_isShared_1998_ = v_isSharedCheck_2009_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_discharge_1994_);
lean_inc(v_suspend_1993_);
lean_inc(v_proc_1992_);
lean_inc(v_maxDepth_1991_);
lean_dec(v_toBacktrackConfig_1976_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2009_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___f_1999_; lean_object* v___x_2001_; 
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1999_, 0, v_test_1974_);
lean_closure_set(v___f_1999_, 1, v_proc_1992_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___f_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_maxDepth_1991_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___f_1999_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_suspend_1993_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_discharge_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*4, v_commitIndependentGoals_1995_);
v___x_2001_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2001_);
v___x_2003_ = v___x_1989_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_toApplyConfig_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*2, v_transparency_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*2 + 1, v_symm_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*2 + 2, v_exfalso_1987_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2003_);
v___x_2005_ = v___x_1982_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*1, v_backtracking_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*1 + 1, v_intro_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*1 + 2, v_constructor_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*1 + 3, v_suggestions_1980_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2014_, lean_object* v_msg_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2022_, v_msg_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2029_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2030_){
_start:
{
if (lean_obj_tag(v_x_2030_) == 0)
{
uint8_t v___x_2031_; 
v___x_2031_ = 0;
return v___x_2031_;
}
else
{
lean_object* v_head_2032_; lean_object* v_tail_2033_; uint8_t v___x_2034_; 
v_head_2032_ = lean_ctor_get(v_x_2030_, 0);
v_tail_2033_ = lean_ctor_get(v_x_2030_, 1);
v___x_2034_ = l_Lean_Expr_hasMVar(v_head_2032_);
if (v___x_2034_ == 0)
{
v_x_2030_ = v_tail_2033_;
goto _start;
}
else
{
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2036_){
_start:
{
uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_res_2037_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2036_);
lean_dec(v_x_2036_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2039_, lean_object* v_sols_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2040_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
v___x_2047_ = lean_apply_6(v_test_2039_, v_sols_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_sols_2040_);
lean_dec_ref(v_test_2039_);
v___x_2048_ = lean_box(v___x_2046_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2050_, lean_object* v_sols_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2050_, v_sols_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2058_, lean_object* v_test_2059_){
_start:
{
lean_object* v___f_2060_; lean_object* v___x_2061_; 
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2060_, 0, v_test_2059_);
v___x_2061_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2058_, v___f_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2062_, lean_object* v_x_2063_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
uint8_t v___x_2064_; 
lean_dec_ref(v_e_2062_);
v___x_2064_ = 0;
return v___x_2064_;
}
else
{
lean_object* v_head_2065_; lean_object* v_tail_2066_; uint8_t v___x_2067_; 
v_head_2065_ = lean_ctor_get(v_x_2063_, 0);
v_tail_2066_ = lean_ctor_get(v_x_2063_, 1);
lean_inc_ref(v_e_2062_);
v___x_2067_ = l_Lean_Expr_occurs(v_e_2062_, v_head_2065_);
if (v___x_2067_ == 0)
{
v_x_2063_ = v_tail_2066_;
goto _start;
}
else
{
lean_dec_ref(v_e_2062_);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2069_, lean_object* v_x_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2069_, v_x_2070_);
lean_dec(v_x_2070_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2073_, lean_object* v_x_2074_){
_start:
{
if (lean_obj_tag(v_x_2074_) == 0)
{
uint8_t v___x_2075_; 
v___x_2075_ = 1;
return v___x_2075_;
}
else
{
lean_object* v_head_2076_; lean_object* v_tail_2077_; uint8_t v___x_2078_; 
v_head_2076_ = lean_ctor_get(v_x_2074_, 0);
lean_inc(v_head_2076_);
v_tail_2077_ = lean_ctor_get(v_x_2074_, 1);
lean_inc(v_tail_2077_);
lean_dec_ref_known(v_x_2074_, 2);
v___x_2078_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2076_, v_sols_2073_);
if (v___x_2078_ == 0)
{
lean_dec(v_tail_2077_);
return v___x_2078_;
}
else
{
v_x_2074_ = v_tail_2077_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2080_, lean_object* v_x_2081_){
_start:
{
uint8_t v_res_2082_; lean_object* v_r_2083_; 
v_res_2082_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2080_, v_x_2081_);
lean_dec(v_sols_2080_);
v_r_2083_ = lean_box(v_res_2082_);
return v_r_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2084_, lean_object* v_sols_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2085_, v_use_2084_);
v___x_2092_ = lean_box(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2094_, lean_object* v_sols_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2094_, v_sols_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_sols_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2102_, lean_object* v_use_2103_){
_start:
{
lean_object* v___f_2104_; lean_object* v___x_2105_; 
v___f_2104_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2104_, 0, v_use_2103_);
v___x_2105_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2102_, v___f_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2106_){
_start:
{
lean_object* v___y_2108_; lean_object* v_toApplyRulesConfig_2109_; uint8_t v_backtracking_2110_; uint8_t v_intro_2111_; uint8_t v_constructor_2112_; uint8_t v_suggestions_2113_; uint8_t v_intro_2117_; 
v_intro_2117_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1 + 1);
if (v_intro_2117_ == 0)
{
lean_object* v_toApplyRulesConfig_2118_; uint8_t v_backtracking_2119_; uint8_t v_constructor_2120_; uint8_t v_suggestions_2121_; 
v_toApplyRulesConfig_2118_ = lean_ctor_get(v_cfg_2106_, 0);
lean_inc_ref(v_toApplyRulesConfig_2118_);
v_backtracking_2119_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1);
v_constructor_2120_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1 + 2);
v_suggestions_2121_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1 + 3);
v___y_2108_ = v_cfg_2106_;
v_toApplyRulesConfig_2109_ = v_toApplyRulesConfig_2118_;
v_backtracking_2110_ = v_backtracking_2119_;
v_intro_2111_ = v_intro_2117_;
v_constructor_2112_ = v_constructor_2120_;
v_suggestions_2113_ = v_suggestions_2121_;
goto v___jp_2107_;
}
else
{
lean_object* v_toApplyRulesConfig_2122_; uint8_t v_backtracking_2123_; uint8_t v_constructor_2124_; uint8_t v_suggestions_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2139_; 
v_toApplyRulesConfig_2122_ = lean_ctor_get(v_cfg_2106_, 0);
v_backtracking_2123_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1);
v_constructor_2124_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1 + 2);
v_suggestions_2125_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*1 + 3);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_cfg_2106_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2127_ = v_cfg_2106_;
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_toApplyRulesConfig_2122_);
lean_dec(v_cfg_2106_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint8_t v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = 0;
if (v_isShared_2128_ == 0)
{
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_toApplyRulesConfig_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*1, v_backtracking_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*1 + 2, v_constructor_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*1 + 3, v_suggestions_2125_);
v___x_2131_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v_toApplyRulesConfig_2133_; uint8_t v_backtracking_2134_; uint8_t v_intro_2135_; uint8_t v_constructor_2136_; uint8_t v_suggestions_2137_; 
lean_ctor_set_uint8(v___x_2131_, sizeof(void*)*1 + 1, v___x_2129_);
v___x_2132_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2131_);
v_toApplyRulesConfig_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc_ref(v_toApplyRulesConfig_2133_);
v_backtracking_2134_ = lean_ctor_get_uint8(v___x_2132_, sizeof(void*)*1);
v_intro_2135_ = lean_ctor_get_uint8(v___x_2132_, sizeof(void*)*1 + 1);
v_constructor_2136_ = lean_ctor_get_uint8(v___x_2132_, sizeof(void*)*1 + 2);
v_suggestions_2137_ = lean_ctor_get_uint8(v___x_2132_, sizeof(void*)*1 + 3);
v___y_2108_ = v___x_2132_;
v_toApplyRulesConfig_2109_ = v_toApplyRulesConfig_2133_;
v_backtracking_2110_ = v_backtracking_2134_;
v_intro_2111_ = v_intro_2135_;
v_constructor_2112_ = v_constructor_2136_;
v_suggestions_2113_ = v_suggestions_2137_;
goto v___jp_2107_;
}
}
}
v___jp_2107_:
{
if (v_constructor_2112_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2109_);
return v___y_2108_;
}
else
{
uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v___y_2108_);
v___x_2114_ = 0;
v___x_2115_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2115_, 0, v_toApplyRulesConfig_2109_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1, v_backtracking_2110_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 1, v_intro_2111_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 2, v___x_2114_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 3, v_suggestions_2113_);
v___x_2116_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2115_);
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
if (lean_obj_tag(v_x_2140_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = l_List_reverse___redArg(v_x_2141_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
else
{
lean_object* v_head_2151_; lean_object* v_tail_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2170_; 
v_head_2151_ = lean_ctor_get(v_x_2140_, 0);
v_tail_2152_ = lean_ctor_get(v_x_2140_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_x_2140_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2154_ = v_x_2140_;
v_isShared_2155_ = v_isSharedCheck_2170_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_tail_2152_);
lean_inc(v_head_2151_);
lean_dec(v_x_2140_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2170_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; 
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
lean_inc(v___y_2145_);
lean_inc_ref(v___y_2144_);
lean_inc(v___y_2143_);
lean_inc_ref(v___y_2142_);
v___x_2156_ = lean_apply_7(v_head_2151_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, lean_box(0));
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_x_2141_);
lean_ctor_set(v___x_2154_, 0, v_a_2157_);
v___x_2159_ = v___x_2154_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2157_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_x_2141_);
v___x_2159_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v_x_2140_ = v_tail_2152_;
v_x_2141_ = v___x_2159_;
goto _start;
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2154_);
lean_dec(v_tail_2152_);
lean_dec(v_x_2141_);
v_a_2162_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2156_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2156_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2171_, v_x_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2181_, lean_object* v_cfg_2182_, lean_object* v_lemmas_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2185_);
lean_inc_ref(v___y_2184_);
v___x_2191_ = lean_apply_8(v_ctx_2181_, v_cfg_2182_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, lean_box(0));
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2193_ = lean_box(0);
v___x_2194_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2183_, v___x_2193_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2203_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2203_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2203_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = l_List_appendTR___redArg(v_a_2192_, v_a_2195_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2199_);
v___x_2201_ = v___x_2197_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_dec(v_a_2192_);
return v___x_2194_;
}
}
else
{
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v_lemmas_2183_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2204_, lean_object* v_cfg_2205_, lean_object* v_lemmas_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2204_, v_cfg_2205_, v_lemmas_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2215_){
_start:
{
uint8_t v___x_2216_; 
v___x_2216_ = 0;
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2217_);
lean_dec(v_x_2217_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2220_, lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2220_, v___x_2221_, v___x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_fst_2233_; lean_object* v___x_2235_; 
v_fst_2233_ = lean_ctor_get(v_a_2229_, 0);
lean_inc(v_fst_2233_);
lean_dec(v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_fst_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_fst_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_a_2238_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2228_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2228_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2246_, lean_object* v___x_2247_, lean_object* v___x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2246_, v___x_2247_, v___x_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2269_, lean_object* v_g_2270_, lean_object* v_lemmas_2271_, lean_object* v_ctx_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2278_, 0, v_ctx_2272_);
lean_closure_set(v___f_2278_, 1, v_cfg_2269_);
lean_closure_set(v___f_2278_, 2, v_lemmas_2271_);
v___x_2279_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2280_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2281_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2281_, 0, v___f_2278_);
lean_closure_set(v___f_2281_, 1, v___x_2279_);
lean_closure_set(v___f_2281_, 2, v___x_2280_);
v___x_2282_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2270_, v___f_2281_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2283_, lean_object* v_g_2284_, lean_object* v_lemmas_2285_, lean_object* v_ctx_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2283_, v_g_2284_, v_lemmas_2285_, v_ctx_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2293_, lean_object* v_lemmas_2294_, lean_object* v_ctx_2295_, lean_object* v_g_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; 
lean_inc(v_g_2296_);
lean_inc_ref(v_cfg_2293_);
v___x_2302_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2293_, v_g_2296_, v_lemmas_2294_, v_ctx_2295_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_toApplyRulesConfig_2303_; lean_object* v_a_2304_; lean_object* v_toApplyConfig_2305_; uint8_t v_transparency_2306_; lean_object* v___x_2307_; 
v_toApplyRulesConfig_2303_ = lean_ctor_get(v_cfg_2293_, 0);
lean_inc_ref(v_toApplyRulesConfig_2303_);
lean_dec_ref(v_cfg_2293_);
v_a_2304_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2302_, 1);
v_toApplyConfig_2305_ = lean_ctor_get(v_toApplyRulesConfig_2303_, 1);
lean_inc_ref(v_toApplyConfig_2305_);
v_transparency_2306_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2303_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2303_);
v___x_2307_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2305_, v_transparency_2306_, v_a_2304_, v_g_2296_, v_a_2298_, v_a_2300_);
return v___x_2307_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_g_2296_);
lean_dec_ref(v_cfg_2293_);
v_a_2308_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2302_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2302_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2316_, lean_object* v_lemmas_2317_, lean_object* v_ctx_2318_, lean_object* v_g_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2316_, v_lemmas_2317_, v_ctx_2318_, v_g_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2326_, lean_object* v_lemmas_2327_, lean_object* v_ctx_2328_, lean_object* v_g_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2335_; 
lean_inc(v_g_2329_);
lean_inc_ref(v_cfg_2326_);
v___x_2335_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2326_, v_g_2329_, v_lemmas_2327_, v_ctx_2328_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_toApplyRulesConfig_2336_; lean_object* v_a_2337_; lean_object* v_toApplyConfig_2338_; uint8_t v_transparency_2339_; lean_object* v___x_2340_; 
v_toApplyRulesConfig_2336_ = lean_ctor_get(v_cfg_2326_, 0);
lean_inc_ref(v_toApplyRulesConfig_2336_);
lean_dec_ref(v_cfg_2326_);
v_a_2337_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2335_, 1);
v_toApplyConfig_2338_ = lean_ctor_get(v_toApplyRulesConfig_2336_, 1);
lean_inc_ref(v_toApplyConfig_2338_);
v_transparency_2339_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2336_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2336_);
v___x_2340_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2338_, v_transparency_2339_, v_a_2337_, v_g_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
return v___x_2340_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_g_2329_);
lean_dec_ref(v_cfg_2326_);
v_a_2341_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2335_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2335_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2349_, lean_object* v_lemmas_2350_, lean_object* v_ctx_2351_, lean_object* v_g_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2349_, v_lemmas_2350_, v_ctx_2351_, v_g_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2359_, lean_object* v_i_2360_, lean_object* v_k_2361_){
_start:
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = lean_array_get_size(v_keys_2359_);
v___x_2363_ = lean_nat_dec_lt(v_i_2360_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_dec(v_i_2360_);
return v___x_2363_;
}
else
{
lean_object* v_k_x27_2364_; uint8_t v___x_2365_; 
v_k_x27_2364_ = lean_array_fget_borrowed(v_keys_2359_, v_i_2360_);
v___x_2365_ = l_Lean_instBEqMVarId_beq(v_k_2361_, v_k_x27_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_add(v_i_2360_, v___x_2366_);
lean_dec(v_i_2360_);
v_i_2360_ = v___x_2367_;
goto _start;
}
else
{
lean_dec(v_i_2360_);
return v___x_2363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2369_, lean_object* v_i_2370_, lean_object* v_k_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2369_, v_i_2370_, v_k_2371_);
lean_dec(v_k_2371_);
lean_dec_ref(v_keys_2369_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2374_, size_t v_x_2375_, lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2374_) == 0)
{
lean_object* v_es_2377_; lean_object* v___x_2378_; size_t v___x_2379_; size_t v___x_2380_; lean_object* v_j_2381_; lean_object* v___x_2382_; 
v_es_2377_ = lean_ctor_get(v_x_2374_, 0);
v___x_2378_ = lean_box(2);
v___x_2379_ = ((size_t)31ULL);
v___x_2380_ = lean_usize_land(v_x_2375_, v___x_2379_);
v_j_2381_ = lean_usize_to_nat(v___x_2380_);
v___x_2382_ = lean_array_get_borrowed(v___x_2378_, v_es_2377_, v_j_2381_);
lean_dec(v_j_2381_);
switch(lean_obj_tag(v___x_2382_))
{
case 0:
{
lean_object* v_key_2383_; uint8_t v___x_2384_; 
v_key_2383_ = lean_ctor_get(v___x_2382_, 0);
v___x_2384_ = l_Lean_instBEqMVarId_beq(v_x_2376_, v_key_2383_);
return v___x_2384_;
}
case 1:
{
lean_object* v_node_2385_; size_t v___x_2386_; size_t v___x_2387_; 
v_node_2385_ = lean_ctor_get(v___x_2382_, 0);
v___x_2386_ = ((size_t)5ULL);
v___x_2387_ = lean_usize_shift_right(v_x_2375_, v___x_2386_);
v_x_2374_ = v_node_2385_;
v_x_2375_ = v___x_2387_;
goto _start;
}
default: 
{
uint8_t v___x_2389_; 
v___x_2389_ = 0;
return v___x_2389_;
}
}
}
else
{
lean_object* v_ks_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_ks_2390_ = lean_ctor_get(v_x_2374_, 0);
v___x_2391_ = lean_unsigned_to_nat(0u);
v___x_2392_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2390_, v___x_2391_, v_x_2376_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2393_, lean_object* v_x_2394_, lean_object* v_x_2395_){
_start:
{
size_t v_x_1988__boxed_2396_; uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_x_1988__boxed_2396_ = lean_unbox_usize(v_x_2394_);
lean_dec(v_x_2394_);
v_res_2397_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2393_, v_x_1988__boxed_2396_, v_x_2395_);
lean_dec(v_x_2395_);
lean_dec_ref(v_x_2393_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2399_, lean_object* v_x_2400_){
_start:
{
uint64_t v___x_2401_; size_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = l_Lean_instHashableMVarId_hash(v_x_2400_);
v___x_2402_ = lean_uint64_to_usize(v___x_2401_);
v___x_2403_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2399_, v___x_2402_, v_x_2400_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2404_, lean_object* v_x_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2404_, v_x_2405_);
lean_dec(v_x_2405_);
lean_dec_ref(v_x_2404_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v_mctx_2412_; lean_object* v_eAssignment_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2411_ = lean_st_ref_get(v___y_2409_);
v_mctx_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_ref(v_mctx_2412_);
lean_dec(v___x_2411_);
v_eAssignment_2413_ = lean_ctor_get(v_mctx_2412_, 8);
lean_inc_ref(v_eAssignment_2413_);
lean_dec_ref(v_mctx_2412_);
v___x_2414_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2413_, v_mvarId_2408_);
lean_dec_ref(v_eAssignment_2413_);
v___x_2415_ = lean_box(v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec(v_mvarId_2417_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
return v_x_2421_;
}
else
{
lean_object* v_head_2423_; lean_object* v_tail_2424_; lean_object* v___x_2425_; 
v_head_2423_ = lean_ctor_get(v_x_2422_, 0);
lean_inc(v_head_2423_);
v_tail_2424_ = lean_ctor_get(v_x_2422_, 1);
lean_inc(v_tail_2424_);
lean_dec_ref_known(v_x_2422_, 2);
v___x_2425_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2421_, v_head_2423_);
v_x_2421_ = v___x_2425_;
v_x_2422_ = v_tail_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2427_, lean_object* v_a_2428_, uint8_t v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
if (lean_obj_tag(v_a_2430_) == 0)
{
if (lean_obj_tag(v_a_2431_) == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec(v_a_2428_);
lean_dec_ref(v_f_2427_);
v___x_2438_ = lean_box(v_a_2429_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v_a_2432_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
else
{
lean_object* v_head_2441_; lean_object* v_tail_2442_; 
v_head_2441_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_head_2441_);
v_tail_2442_ = lean_ctor_get(v_a_2431_, 1);
lean_inc(v_tail_2442_);
lean_dec_ref_known(v_a_2431_, 2);
v_a_2430_ = v_head_2441_;
v_a_2431_ = v_tail_2442_;
goto _start;
}
}
else
{
lean_object* v_head_2444_; lean_object* v_tail_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2488_; 
v_head_2444_ = lean_ctor_get(v_a_2430_, 0);
v_tail_2445_ = lean_ctor_get(v_a_2430_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_a_2430_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2447_ = v_a_2430_;
v_isShared_2448_ = v_isSharedCheck_2488_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_tail_2445_);
lean_inc(v_head_2444_);
lean_dec(v_a_2430_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2488_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2487_; 
v___x_2449_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2444_, v___y_2434_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2487_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2487_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_unbox(v_a_2450_);
lean_dec(v_a_2450_);
if (v___x_2454_ == 0)
{
lean_object* v_zero_2455_; uint8_t v_isZero_2456_; 
v_zero_2455_ = lean_unsigned_to_nat(0u);
v_isZero_2456_ = lean_nat_dec_eq(v_a_2428_, v_zero_2455_);
if (v_isZero_2456_ == 1)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_del_object(v___x_2447_);
lean_dec(v_a_2428_);
lean_dec_ref(v_f_2427_);
v___x_2457_ = lean_array_push(v_a_2432_, v_head_2444_);
v___x_2458_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2457_, v_tail_2445_);
v___x_2459_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2458_, v_a_2431_);
v___x_2460_ = lean_box(v_a_2429_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2461_);
v___x_2463_ = v___x_2452_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
else
{
lean_object* v_one_2465_; lean_object* v_n_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_del_object(v___x_2452_);
v_one_2465_ = lean_unsigned_to_nat(1u);
v_n_2466_ = lean_nat_sub(v_a_2428_, v_one_2465_);
lean_dec(v_a_2428_);
v___x_2467_ = 1;
lean_inc_ref(v_f_2427_);
lean_inc(v_head_2444_);
v___x_2468_ = lean_apply_1(v_f_2427_, v_head_2444_);
v___x_2469_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2468_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
if (lean_obj_tag(v_a_2470_) == 0)
{
lean_object* v___x_2471_; 
lean_del_object(v___x_2447_);
v___x_2471_ = lean_array_push(v_a_2432_, v_head_2444_);
v_a_2428_ = v_n_2466_;
v_a_2430_ = v_tail_2445_;
v_a_2432_ = v___x_2471_;
goto _start;
}
else
{
lean_object* v_val_2473_; lean_object* v___x_2475_; 
lean_dec(v_head_2444_);
v_val_2473_ = lean_ctor_get(v_a_2470_, 0);
lean_inc(v_val_2473_);
lean_dec_ref_known(v_a_2470_, 1);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v_a_2431_);
lean_ctor_set(v___x_2447_, 0, v_tail_2445_);
v___x_2475_ = v___x_2447_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_tail_2445_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_a_2431_);
v___x_2475_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
v_a_2428_ = v_n_2466_;
v_a_2429_ = v___x_2467_;
v_a_2430_ = v_val_2473_;
v_a_2431_ = v___x_2475_;
goto _start;
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_n_2466_);
lean_del_object(v___x_2447_);
lean_dec(v_tail_2445_);
lean_dec(v_head_2444_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_f_2427_);
v_a_2478_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2469_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2469_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
else
{
lean_del_object(v___x_2452_);
lean_del_object(v___x_2447_);
lean_dec(v_head_2444_);
v_a_2430_ = v_tail_2445_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v_a_2067__boxed_2500_; lean_object* v_res_2501_; 
v_a_2067__boxed_2500_ = lean_unbox(v_a_2491_);
v_res_2501_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2489_, v_a_2490_, v_a_2067__boxed_2500_, v_a_2492_, v_a_2493_, v_a_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2502_, size_t v_i_2503_, size_t v_stop_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_a_2512_; uint8_t v___x_2516_; 
v___x_2516_ = lean_usize_dec_eq(v_i_2503_, v_stop_2504_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2520_; 
v___x_2517_ = lean_array_uget_borrowed(v_as_2502_, v_i_2503_);
v___x_2520_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2517_, v___y_2507_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; uint8_t v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
if (v___x_2522_ == 0)
{
goto v___jp_2518_;
}
else
{
v_a_2512_ = v_b_2505_;
goto v___jp_2511_;
}
}
else
{
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2523_; uint8_t v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2524_ = lean_unbox(v_a_2523_);
lean_dec(v_a_2523_);
if (v___x_2524_ == 0)
{
v_a_2512_ = v_b_2505_;
goto v___jp_2511_;
}
else
{
goto v___jp_2518_;
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v_b_2505_);
v_a_2525_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2520_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2520_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
v___jp_2518_:
{
lean_object* v___x_2519_; 
lean_inc(v___x_2517_);
v___x_2519_ = lean_array_push(v_b_2505_, v___x_2517_);
v_a_2512_ = v___x_2519_;
goto v___jp_2511_;
}
}
else
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2505_);
return v___x_2533_;
}
v___jp_2511_:
{
size_t v___x_2513_; size_t v___x_2514_; 
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2503_, v___x_2513_);
v_i_2503_ = v___x_2514_;
v_b_2505_ = v_a_2512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2534_, lean_object* v_i_2535_, lean_object* v_stop_2536_, lean_object* v_b_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
size_t v_i_boxed_2543_; size_t v_stop_boxed_2544_; lean_object* v_res_2545_; 
v_i_boxed_2543_ = lean_unbox_usize(v_i_2535_);
lean_dec(v_i_2535_);
v_stop_boxed_2544_ = lean_unbox_usize(v_stop_2536_);
lean_dec(v_stop_2536_);
v_res_2545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2534_, v_i_boxed_2543_, v_stop_boxed_2544_, v_b_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v_as_2534_);
return v_res_2545_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2549_ = lean_array_to_list(v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2550_, lean_object* v_goals_2551_, lean_object* v_maxIters_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2558_ = 0;
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_unsigned_to_nat(0u);
v___x_2561_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2562_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2550_, v_maxIters_2552_, v___x_2558_, v_goals_2551_, v___x_2559_, v___x_2561_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2605_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2605_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2605_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_fst_2567_; lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2604_; 
v_fst_2567_ = lean_ctor_get(v_a_2563_, 0);
v_snd_2568_ = lean_ctor_get(v_a_2563_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_a_2563_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2570_ = v_a_2563_;
v_isShared_2571_ = v_isSharedCheck_2604_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_inc(v_fst_2567_);
lean_dec(v_a_2563_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2604_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_array_get_size(v_snd_2568_);
v___x_2573_ = lean_nat_dec_lt(v___x_2560_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_dec(v_snd_2568_);
v___x_2574_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2574_);
v___x_2576_ = v___x_2570_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_fst_2567_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2576_);
v___x_2578_ = v___x_2565_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
lean_del_object(v___x_2565_);
v___x_2581_ = ((size_t)0ULL);
v___x_2582_ = lean_usize_of_nat(v___x_2572_);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2568_, v___x_2581_, v___x_2582_, v___x_2561_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v_snd_2568_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2595_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2595_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2595_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_array_to_list(v_a_2584_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2588_);
v___x_2590_ = v___x_2570_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_fst_2567_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2590_);
v___x_2592_ = v___x_2586_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_del_object(v___x_2570_);
lean_dec(v_fst_2567_);
v_a_2596_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2583_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2583_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
v_a_2606_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2562_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2562_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2614_, lean_object* v_goals_2615_, lean_object* v_maxIters_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2614_, v_goals_2615_, v_maxIters_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2622_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2626_, lean_object* v_goals_2627_, lean_object* v_maxIters_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2626_, v_goals_2627_, v_maxIters_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2647_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_fst_2639_; uint8_t v___x_2640_; 
v_fst_2639_ = lean_ctor_get(v_a_2635_, 0);
v___x_2640_ = lean_unbox(v_fst_2639_);
if (v___x_2640_ == 1)
{
lean_object* v_snd_2641_; lean_object* v___x_2643_; 
v_snd_2641_ = lean_ctor_get(v_a_2635_, 1);
lean_inc(v_snd_2641_);
lean_dec(v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_snd_2641_);
v___x_2643_ = v___x_2637_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_snd_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
v___x_2645_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2646_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2645_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_a_2648_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2634_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2634_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2656_, lean_object* v_goals_2657_, lean_object* v_maxIters_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2656_, v_goals_2657_, v_maxIters_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2665_, lean_object* v_ctx_2666_, lean_object* v_cfg_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
uint8_t v_backtracking_2674_; 
v_backtracking_2674_ = lean_ctor_get_uint8(v_cfg_2667_, sizeof(void*)*1);
if (v_backtracking_2674_ == 0)
{
lean_object* v_toApplyRulesConfig_2675_; lean_object* v_toBacktrackConfig_2676_; lean_object* v_maxDepth_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_toApplyRulesConfig_2675_ = lean_ctor_get(v_cfg_2667_, 0);
v_toBacktrackConfig_2676_ = lean_ctor_get(v_toApplyRulesConfig_2675_, 0);
v_maxDepth_2677_ = lean_ctor_get(v_toBacktrackConfig_2676_, 0);
lean_inc(v_maxDepth_2677_);
v___x_2678_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2678_, 0, v_cfg_2667_);
lean_closure_set(v___x_2678_, 1, v_lemmas_2665_);
lean_closure_set(v___x_2678_, 2, v_ctx_2666_);
v___x_2679_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2678_, v_a_2668_, v_maxDepth_2677_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2679_;
}
else
{
lean_object* v_toApplyRulesConfig_2680_; lean_object* v_toBacktrackConfig_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_toApplyRulesConfig_2680_ = lean_ctor_get(v_cfg_2667_, 0);
v_toBacktrackConfig_2681_ = lean_ctor_get(v_toApplyRulesConfig_2680_, 0);
lean_inc_ref(v_toBacktrackConfig_2681_);
v___x_2682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2683_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2683_, 0, v_cfg_2667_);
lean_closure_set(v___x_2683_, 1, v_lemmas_2665_);
lean_closure_set(v___x_2683_, 2, v_ctx_2666_);
v___x_2684_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2681_, v___x_2682_, v___x_2683_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2685_, lean_object* v_ctx_2686_, lean_object* v_cfg_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2685_, v_ctx_2686_, v_cfg_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2695_, v___y_2697_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v_mvarId_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
uint8_t v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2710_, v_x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_){
_start:
{
uint8_t v_res_2716_; lean_object* v_r_2717_; 
v_res_2716_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2713_, v_x_2714_, v_x_2715_);
lean_dec(v_x_2715_);
lean_dec_ref(v_x_2714_);
v_r_2717_ = lean_box(v_res_2716_);
return v_r_2717_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2718_, lean_object* v_x_2719_, size_t v_x_2720_, lean_object* v_x_2721_){
_start:
{
uint8_t v___x_2722_; 
v___x_2722_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2719_, v_x_2720_, v_x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v_x_2726_){
_start:
{
size_t v_x_2513__boxed_2727_; uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_x_2513__boxed_2727_ = lean_unbox_usize(v_x_2725_);
lean_dec(v_x_2725_);
v_res_2728_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2723_, v_x_2724_, v_x_2513__boxed_2727_, v_x_2726_);
lean_dec(v_x_2726_);
lean_dec_ref(v_x_2724_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2730_, lean_object* v_keys_2731_, lean_object* v_vals_2732_, lean_object* v_heq_2733_, lean_object* v_i_2734_, lean_object* v_k_2735_){
_start:
{
uint8_t v___x_2736_; 
v___x_2736_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2731_, v_i_2734_, v_k_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2737_, lean_object* v_keys_2738_, lean_object* v_vals_2739_, lean_object* v_heq_2740_, lean_object* v_i_2741_, lean_object* v_k_2742_){
_start:
{
uint8_t v_res_2743_; lean_object* v_r_2744_; 
v_res_2743_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2737_, v_keys_2738_, v_vals_2739_, v_heq_2740_, v_i_2741_, v_k_2742_);
lean_dec(v_k_2742_);
lean_dec_ref(v_vals_2739_);
lean_dec_ref(v_keys_2738_);
v_r_2744_ = lean_box(v_res_2743_);
return v_r_2744_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2747_ = l_Lean_stringToMessageData(v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v_x_2756_);
return v_res_2762_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2765_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2766_ = l_Lean_Name_append(v___x_2765_, v___x_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2767_, lean_object* v_lemmas_2768_, lean_object* v_ctx_2769_, lean_object* v_goals_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___f_2776_; uint8_t v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v_a_2785_; uint8_t v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; uint8_t v___y_2800_; lean_object* v___y_2801_; lean_object* v_a_2802_; uint8_t v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v_a_2812_; uint8_t v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; uint8_t v___y_2830_; lean_object* v___y_2831_; lean_object* v_a_2832_; lean_object* v_cfg_2834_; lean_object* v___x_2835_; 
v___f_2776_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v_cfg_2834_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2767_);
lean_inc(v_goals_2770_);
lean_inc_ref(v_cfg_2834_);
lean_inc_ref(v_ctx_2769_);
lean_inc(v_lemmas_2768_);
v___x_2835_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2768_, v_ctx_2769_, v_cfg_2834_, v_goals_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_dec_ref(v_cfg_2834_);
lean_dec(v_goals_2770_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
return v___x_2835_;
}
else
{
lean_object* v_a_2836_; uint8_t v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; uint8_t v___y_2880_; uint8_t v___x_2934_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
v___x_2934_ = l_Lean_Exception_isInterrupt(v_a_2836_);
if (v___x_2934_ == 0)
{
uint8_t v___x_2935_; 
v___x_2935_ = l_Lean_Exception_isRuntime(v_a_2836_);
v___y_2880_ = v___x_2935_;
goto v___jp_2879_;
}
else
{
lean_dec(v_a_2836_);
v___y_2880_ = v___x_2934_;
goto v___jp_2879_;
}
v___jp_2837_:
{
lean_object* v___x_2845_; lean_object* v_a_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2774_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2848_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2840_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_io_mono_nanos_now();
v___x_2850_ = l_Lean_MVarId_exfalso(v___y_2843_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2852_, 0, v_a_2851_);
lean_ctor_set(v___x_2852_, 1, v___y_2841_);
v___x_2853_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2768_, v_ctx_2769_, v_cfg_2834_, v___x_2852_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 1);
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
v___y_2805_ = v___y_2838_;
v___y_2806_ = v_a_2846_;
v___y_2807_ = v___x_2849_;
v___y_2808_ = v___y_2839_;
v___y_2809_ = v___y_2840_;
v___y_2810_ = v___y_2842_;
v___y_2811_ = v___y_2844_;
v_a_2812_ = v___x_2859_;
goto v___jp_2804_;
}
}
}
else
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2853_, 1);
v___y_2825_ = v___y_2838_;
v___y_2826_ = v_a_2846_;
v___y_2827_ = v___x_2849_;
v___y_2828_ = v___y_2839_;
v___y_2829_ = v___y_2840_;
v___y_2830_ = v___y_2842_;
v___y_2831_ = v___y_2844_;
v_a_2832_ = v_a_2862_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2863_; 
lean_dec(v___y_2841_);
lean_dec_ref(v_cfg_2834_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
v_a_2863_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2850_, 1);
v___y_2825_ = v___y_2838_;
v___y_2826_ = v_a_2846_;
v___y_2827_ = v___x_2849_;
v___y_2828_ = v___y_2839_;
v___y_2829_ = v___y_2840_;
v___y_2830_ = v___y_2842_;
v___y_2831_ = v___y_2844_;
v_a_2832_ = v_a_2863_;
goto v___jp_2824_;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_io_get_num_heartbeats();
v___x_2865_ = l_Lean_MVarId_exfalso(v___y_2843_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2866_);
lean_ctor_set(v___x_2867_, 1, v___y_2841_);
v___x_2868_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2768_, v_ctx_2769_, v_cfg_2834_, v___x_2867_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set_tag(v___x_2871_, 1);
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v___y_2778_ = v___y_2838_;
v___y_2779_ = v_a_2846_;
v___y_2780_ = v___y_2839_;
v___y_2781_ = v___x_2864_;
v___y_2782_ = v___y_2840_;
v___y_2783_ = v___y_2842_;
v___y_2784_ = v___y_2844_;
v_a_2785_ = v___x_2874_;
goto v___jp_2777_;
}
}
}
else
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2868_, 1);
v___y_2795_ = v___y_2838_;
v___y_2796_ = v_a_2846_;
v___y_2797_ = v___x_2864_;
v___y_2798_ = v___y_2839_;
v___y_2799_ = v___y_2840_;
v___y_2800_ = v___y_2842_;
v___y_2801_ = v___y_2844_;
v_a_2802_ = v_a_2877_;
goto v___jp_2794_;
}
}
else
{
lean_object* v_a_2878_; 
lean_dec(v___y_2841_);
lean_dec_ref(v_cfg_2834_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
v_a_2878_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2865_, 1);
v___y_2795_ = v___y_2838_;
v___y_2796_ = v_a_2846_;
v___y_2797_ = v___x_2864_;
v___y_2798_ = v___y_2839_;
v___y_2799_ = v___y_2840_;
v___y_2800_ = v___y_2842_;
v___y_2801_ = v___y_2844_;
v_a_2802_ = v_a_2878_;
goto v___jp_2794_;
}
}
}
v___jp_2879_:
{
if (v___y_2880_ == 0)
{
if (lean_obj_tag(v_goals_2770_) == 1)
{
lean_object* v_tail_2881_; 
v_tail_2881_ = lean_ctor_get(v_goals_2770_, 1);
lean_inc(v_tail_2881_);
if (lean_obj_tag(v_tail_2881_) == 0)
{
lean_object* v_toApplyRulesConfig_2882_; uint8_t v_exfalso_2883_; 
v_toApplyRulesConfig_2882_ = lean_ctor_get(v_cfg_2834_, 0);
lean_inc_ref(v_toApplyRulesConfig_2882_);
v_exfalso_2883_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2882_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2882_);
if (v_exfalso_2883_ == 1)
{
lean_object* v_toCold_2884_; lean_object* v_options_2885_; uint8_t v_hasTrace_2886_; 
lean_dec_ref_known(v___x_2835_, 1);
v_toCold_2884_ = lean_ctor_get(v_a_2773_, 0);
v_options_2885_ = lean_ctor_get(v_toCold_2884_, 2);
v_hasTrace_2886_ = lean_ctor_get_uint8(v_options_2885_, sizeof(void*)*1);
if (v_hasTrace_2886_ == 0)
{
lean_object* v_head_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2905_; 
v_head_2887_ = lean_ctor_get(v_goals_2770_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_goals_2770_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; 
v_unused_2906_ = lean_ctor_get(v_goals_2770_, 1);
lean_dec(v_unused_2906_);
v___x_2889_ = v_goals_2770_;
v_isShared_2890_ = v_isSharedCheck_2905_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_head_2887_);
lean_dec(v_goals_2770_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2905_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_MVarId_exfalso(v_head_2887_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v_a_2892_);
v___x_2894_ = v___x_2889_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2892_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_tail_2881_);
v___x_2894_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2768_, v_ctx_2769_, v_cfg_2834_, v___x_2894_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
return v___x_2895_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_del_object(v___x_2889_);
lean_dec_ref(v_cfg_2834_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
v_a_2897_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2891_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2891_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
else
{
lean_object* v_head_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2932_; 
v_head_2907_ = lean_ctor_get(v_goals_2770_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_goals_2770_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v_goals_2770_, 1);
lean_dec(v_unused_2933_);
v___x_2909_ = v_goals_2770_;
v_isShared_2910_ = v_isSharedCheck_2932_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_head_2907_);
lean_dec(v_goals_2770_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2932_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_inheritedTraceOptions_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_inheritedTraceOptions_2911_ = lean_ctor_get(v_toCold_2884_, 11);
v___x_2912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2913_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2914_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2911_, v_options_2885_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = l_Lean_trace_profiler;
v___x_2917_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2885_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_MVarId_exfalso(v_head_2907_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2921_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v_a_2919_);
v___x_2921_ = v___x_2909_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2919_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_tail_2881_);
v___x_2921_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2768_, v_ctx_2769_, v_cfg_2834_, v___x_2921_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
return v___x_2922_;
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_del_object(v___x_2909_);
lean_dec_ref(v_cfg_2834_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
v_a_2924_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2918_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2918_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_del_object(v___x_2909_);
v___y_2838_ = v_exfalso_2883_;
v___y_2839_ = v___x_2913_;
v___y_2840_ = v_options_2885_;
v___y_2841_ = v_tail_2881_;
v___y_2842_ = v___x_2915_;
v___y_2843_ = v_head_2907_;
v___y_2844_ = v___x_2912_;
goto v___jp_2837_;
}
}
else
{
lean_del_object(v___x_2909_);
v___y_2838_ = v_exfalso_2883_;
v___y_2839_ = v___x_2913_;
v___y_2840_ = v_options_2885_;
v___y_2841_ = v_tail_2881_;
v___y_2842_ = v___x_2915_;
v___y_2843_ = v_head_2907_;
v___y_2844_ = v___x_2912_;
goto v___jp_2837_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2770_, 2);
lean_dec_ref(v_cfg_2834_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
return v___x_2835_;
}
}
else
{
lean_dec_ref_known(v_goals_2770_, 2);
lean_dec(v_tail_2881_);
lean_dec_ref(v_cfg_2834_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
return v___x_2835_;
}
}
else
{
lean_dec_ref(v_cfg_2834_);
lean_dec(v_goals_2770_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
return v___x_2835_;
}
}
else
{
lean_dec_ref(v_cfg_2834_);
lean_dec(v_goals_2770_);
lean_dec_ref(v_ctx_2769_);
lean_dec(v_lemmas_2768_);
return v___x_2835_;
}
}
}
v___jp_2777_:
{
lean_object* v___x_2786_; double v___x_2787_; double v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2786_ = lean_io_get_num_heartbeats();
v___x_2787_ = lean_float_of_nat(v___y_2781_);
v___x_2788_ = lean_float_of_nat(v___x_2786_);
v___x_2789_ = lean_box_float(v___x_2787_);
v___x_2790_ = lean_box_float(v___x_2788_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2785_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2784_);
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2784_, v___y_2778_, v___y_2780_, v___y_2782_, v___y_2783_, v___y_2779_, v___f_2776_, v___x_2792_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
return v___x_2793_;
}
v___jp_2794_:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_a_2802_);
v___y_2778_ = v___y_2795_;
v___y_2779_ = v___y_2796_;
v___y_2780_ = v___y_2798_;
v___y_2781_ = v___y_2797_;
v___y_2782_ = v___y_2799_;
v___y_2783_ = v___y_2800_;
v___y_2784_ = v___y_2801_;
v_a_2785_ = v___x_2803_;
goto v___jp_2777_;
}
v___jp_2804_:
{
lean_object* v___x_2813_; double v___x_2814_; double v___x_2815_; double v___x_2816_; double v___x_2817_; double v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2813_ = lean_io_mono_nanos_now();
v___x_2814_ = lean_float_of_nat(v___y_2807_);
v___x_2815_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2816_ = lean_float_div(v___x_2814_, v___x_2815_);
v___x_2817_ = lean_float_of_nat(v___x_2813_);
v___x_2818_ = lean_float_div(v___x_2817_, v___x_2815_);
v___x_2819_ = lean_box_float(v___x_2816_);
v___x_2820_ = lean_box_float(v___x_2818_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2812_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
lean_inc_ref(v___y_2808_);
lean_inc(v___y_2811_);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2811_, v___y_2805_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2806_, v___f_2776_, v___x_2822_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
return v___x_2823_;
}
v___jp_2824_:
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2832_);
v___y_2805_ = v___y_2825_;
v___y_2806_ = v___y_2826_;
v___y_2807_ = v___y_2827_;
v___y_2808_ = v___y_2828_;
v___y_2809_ = v___y_2829_;
v___y_2810_ = v___y_2830_;
v___y_2811_ = v___y_2831_;
v_a_2812_ = v___x_2833_;
goto v___jp_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2936_, lean_object* v_lemmas_2937_, lean_object* v_ctx_2938_, lean_object* v_goals_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2936_, v_lemmas_2937_, v_ctx_2938_, v_goals_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = l_List_reverse___redArg(v_x_2947_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
else
{
lean_object* v_head_2955_; lean_object* v_tail_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2979_; 
v_head_2955_ = lean_ctor_get(v_x_2946_, 0);
v_tail_2956_ = lean_ctor_get(v_x_2946_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2958_ = v_x_2946_;
v_isShared_2959_ = v_isSharedCheck_2979_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_tail_2956_);
lean_inc(v_head_2955_);
lean_dec(v_x_2946_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2979_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Expr_applySymm(v_head_2955_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v_x_2947_);
lean_ctor_set(v___x_2958_, 0, v_a_2961_);
v___x_2963_ = v___x_2958_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2961_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_x_2947_);
v___x_2963_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
v_x_2946_ = v_tail_2956_;
v_x_2947_ = v___x_2963_;
goto _start;
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2978_; 
lean_del_object(v___x_2958_);
v_a_2966_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2968_ = v___x_2960_;
v_isShared_2969_ = v_isSharedCheck_2978_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2960_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2978_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
uint8_t v___y_2971_; uint8_t v___x_2976_; 
v___x_2976_ = l_Lean_Exception_isInterrupt(v_a_2966_);
if (v___x_2976_ == 0)
{
uint8_t v___x_2977_; 
lean_inc(v_a_2966_);
v___x_2977_ = l_Lean_Exception_isRuntime(v_a_2966_);
v___y_2971_ = v___x_2977_;
goto v___jp_2970_;
}
else
{
v___y_2971_ = v___x_2976_;
goto v___jp_2970_;
}
v___jp_2970_:
{
if (v___y_2971_ == 0)
{
lean_del_object(v___x_2968_);
lean_dec(v_a_2966_);
v_x_2946_ = v_tail_2956_;
goto _start;
}
else
{
lean_object* v___x_2974_; 
lean_dec(v_tail_2956_);
lean_dec(v_x_2947_);
if (v_isShared_2969_ == 0)
{
v___x_2974_ = v___x_2968_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2966_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2980_, v_x_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2988_, lean_object* v_hyps_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
if (v_symm_2988_ == 0)
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_hyps_2989_);
return v___x_2995_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_box(0);
lean_inc(v_hyps_2989_);
v___x_2997_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2989_, v___x_2996_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3006_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = l_List_appendTR___redArg(v_hyps_2989_, v_a_2998_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3002_);
v___x_3004_ = v___x_3000_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_dec(v_hyps_2989_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3007_, lean_object* v_hyps_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
uint8_t v_symm_boxed_3014_; lean_object* v_res_3015_; 
v_symm_boxed_3014_ = lean_unbox(v_symm_3007_);
v_res_3015_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3014_, v_hyps_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3016_, size_t v_sz_3017_, size_t v_i_3018_, lean_object* v_b_3019_){
_start:
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_usize_dec_lt(v_i_3018_, v_sz_3017_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_b_3019_);
return v___x_3022_;
}
else
{
lean_object* v_snd_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3041_; 
v_snd_3023_ = lean_ctor_get(v_b_3019_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_b_3019_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_b_3019_, 0);
lean_dec(v_unused_3042_);
v___x_3025_ = v_b_3019_;
v_isShared_3026_ = v_isSharedCheck_3041_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_snd_3023_);
lean_dec(v_b_3019_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3041_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v_a_3029_; lean_object* v_a_3036_; 
v___x_3027_ = lean_box(0);
v_a_3036_ = lean_array_uget_borrowed(v_as_3016_, v_i_3018_);
if (lean_obj_tag(v_a_3036_) == 0)
{
v_a_3029_ = v_snd_3023_;
goto v___jp_3028_;
}
else
{
lean_object* v_val_3037_; uint8_t v___x_3038_; 
v_val_3037_ = lean_ctor_get(v_a_3036_, 0);
v___x_3038_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_inc(v_val_3037_);
v___x_3039_ = l_Lean_LocalDecl_toExpr(v_val_3037_);
v___x_3040_ = lean_array_push(v_snd_3023_, v___x_3039_);
v_a_3029_ = v___x_3040_;
goto v___jp_3028_;
}
else
{
v_a_3029_ = v_snd_3023_;
goto v___jp_3028_;
}
}
v___jp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 1, v_a_3029_);
lean_ctor_set(v___x_3025_, 0, v___x_3027_);
v___x_3031_ = v___x_3025_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_a_3029_);
v___x_3031_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
size_t v___x_3032_; size_t v___x_3033_; 
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_add(v_i_3018_, v___x_3032_);
v_i_3018_ = v___x_3033_;
v_b_3019_ = v___x_3031_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3043_, lean_object* v_sz_3044_, lean_object* v_i_3045_, lean_object* v_b_3046_, lean_object* v___y_3047_){
_start:
{
size_t v_sz_boxed_3048_; size_t v_i_boxed_3049_; lean_object* v_res_3050_; 
v_sz_boxed_3048_ = lean_unbox_usize(v_sz_3044_);
lean_dec(v_sz_3044_);
v_i_boxed_3049_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3043_, v_sz_boxed_3048_, v_i_boxed_3049_, v_b_3046_);
lean_dec_ref(v_as_3043_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3051_, size_t v_sz_3052_, size_t v_i_3053_, lean_object* v_b_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_usize_dec_lt(v_i_3053_, v_sz_3052_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_b_3054_);
return v___x_3063_;
}
else
{
lean_object* v_snd_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3082_; 
v_snd_3064_ = lean_ctor_get(v_b_3054_, 1);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_b_3054_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_b_3054_, 0);
lean_dec(v_unused_3083_);
v___x_3066_ = v_b_3054_;
v_isShared_3067_ = v_isSharedCheck_3082_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_snd_3064_);
lean_dec(v_b_3054_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3082_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v_a_3070_; lean_object* v_a_3077_; 
v___x_3068_ = lean_box(0);
v_a_3077_ = lean_array_uget_borrowed(v_as_3051_, v_i_3053_);
if (lean_obj_tag(v_a_3077_) == 0)
{
v_a_3070_ = v_snd_3064_;
goto v___jp_3069_;
}
else
{
lean_object* v_val_3078_; uint8_t v___x_3079_; 
v_val_3078_ = lean_ctor_get(v_a_3077_, 0);
v___x_3079_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_inc(v_val_3078_);
v___x_3080_ = l_Lean_LocalDecl_toExpr(v_val_3078_);
v___x_3081_ = lean_array_push(v_snd_3064_, v___x_3080_);
v_a_3070_ = v___x_3081_;
goto v___jp_3069_;
}
else
{
v_a_3070_ = v_snd_3064_;
goto v___jp_3069_;
}
}
v___jp_3069_:
{
lean_object* v___x_3072_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v_a_3070_);
lean_ctor_set(v___x_3066_, 0, v___x_3068_);
v___x_3072_ = v___x_3066_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_a_3070_);
v___x_3072_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = ((size_t)1ULL);
v___x_3074_ = lean_usize_add(v_i_3053_, v___x_3073_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3051_, v_sz_3052_, v___x_3074_, v___x_3072_);
return v___x_3075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3084_, lean_object* v_sz_3085_, lean_object* v_i_3086_, lean_object* v_b_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
size_t v_sz_boxed_3095_; size_t v_i_boxed_3096_; lean_object* v_res_3097_; 
v_sz_boxed_3095_ = lean_unbox_usize(v_sz_3085_);
lean_dec(v_sz_3085_);
v_i_boxed_3096_ = lean_unbox_usize(v_i_3086_);
lean_dec(v_i_3086_);
v_res_3097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3084_, v_sz_boxed_3095_, v_i_boxed_3096_, v_b_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec_ref(v_as_3084_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3098_, size_t v_sz_3099_, size_t v_i_3100_, lean_object* v_b_3101_){
_start:
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_usize_dec_lt(v_i_3100_, v_sz_3099_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_b_3101_);
return v___x_3104_;
}
else
{
lean_object* v_snd_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3123_; 
v_snd_3105_ = lean_ctor_get(v_b_3101_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_b_3101_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v_b_3101_, 0);
lean_dec(v_unused_3124_);
v___x_3107_ = v_b_3101_;
v_isShared_3108_ = v_isSharedCheck_3123_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_snd_3105_);
lean_dec(v_b_3101_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3123_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v_a_3111_; lean_object* v_a_3118_; 
v___x_3109_ = lean_box(0);
v_a_3118_ = lean_array_uget_borrowed(v_as_3098_, v_i_3100_);
if (lean_obj_tag(v_a_3118_) == 0)
{
v_a_3111_ = v_snd_3105_;
goto v___jp_3110_;
}
else
{
lean_object* v_val_3119_; uint8_t v___x_3120_; 
v_val_3119_ = lean_ctor_get(v_a_3118_, 0);
v___x_3120_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_inc(v_val_3119_);
v___x_3121_ = l_Lean_LocalDecl_toExpr(v_val_3119_);
v___x_3122_ = lean_array_push(v_snd_3105_, v___x_3121_);
v_a_3111_ = v___x_3122_;
goto v___jp_3110_;
}
else
{
v_a_3111_ = v_snd_3105_;
goto v___jp_3110_;
}
}
v___jp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v_a_3111_);
lean_ctor_set(v___x_3107_, 0, v___x_3109_);
v___x_3113_ = v___x_3107_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3111_);
v___x_3113_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
size_t v___x_3114_; size_t v___x_3115_; 
v___x_3114_ = ((size_t)1ULL);
v___x_3115_ = lean_usize_add(v_i_3100_, v___x_3114_);
v_i_3100_ = v___x_3115_;
v_b_3101_ = v___x_3113_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3125_, lean_object* v_sz_3126_, lean_object* v_i_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_){
_start:
{
size_t v_sz_boxed_3130_; size_t v_i_boxed_3131_; lean_object* v_res_3132_; 
v_sz_boxed_3130_ = lean_unbox_usize(v_sz_3126_);
lean_dec(v_sz_3126_);
v_i_boxed_3131_ = lean_unbox_usize(v_i_3127_);
lean_dec(v_i_3127_);
v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3125_, v_sz_boxed_3130_, v_i_boxed_3131_, v_b_3128_);
lean_dec_ref(v_as_3125_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3133_, size_t v_sz_3134_, size_t v_i_3135_, lean_object* v_b_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
uint8_t v___x_3144_; 
v___x_3144_ = lean_usize_dec_lt(v_i_3135_, v_sz_3134_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_b_3136_);
return v___x_3145_;
}
else
{
lean_object* v_snd_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3164_; 
v_snd_3146_ = lean_ctor_get(v_b_3136_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_b_3136_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v_b_3136_, 0);
lean_dec(v_unused_3165_);
v___x_3148_ = v_b_3136_;
v_isShared_3149_ = v_isSharedCheck_3164_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_snd_3146_);
lean_dec(v_b_3136_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3164_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v_a_3152_; lean_object* v_a_3159_; 
v___x_3150_ = lean_box(0);
v_a_3159_ = lean_array_uget_borrowed(v_as_3133_, v_i_3135_);
if (lean_obj_tag(v_a_3159_) == 0)
{
v_a_3152_ = v_snd_3146_;
goto v___jp_3151_;
}
else
{
lean_object* v_val_3160_; uint8_t v___x_3161_; 
v_val_3160_ = lean_ctor_get(v_a_3159_, 0);
v___x_3161_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_inc(v_val_3160_);
v___x_3162_ = l_Lean_LocalDecl_toExpr(v_val_3160_);
v___x_3163_ = lean_array_push(v_snd_3146_, v___x_3162_);
v_a_3152_ = v___x_3163_;
goto v___jp_3151_;
}
else
{
v_a_3152_ = v_snd_3146_;
goto v___jp_3151_;
}
}
v___jp_3151_:
{
lean_object* v___x_3154_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v_a_3152_);
lean_ctor_set(v___x_3148_, 0, v___x_3150_);
v___x_3154_ = v___x_3148_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_a_3152_);
v___x_3154_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
size_t v___x_3155_; size_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = ((size_t)1ULL);
v___x_3156_ = lean_usize_add(v_i_3135_, v___x_3155_);
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3133_, v_sz_3134_, v___x_3156_, v___x_3154_);
return v___x_3157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3166_, lean_object* v_sz_3167_, lean_object* v_i_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
size_t v_sz_boxed_3177_; size_t v_i_boxed_3178_; lean_object* v_res_3179_; 
v_sz_boxed_3177_ = lean_unbox_usize(v_sz_3167_);
lean_dec(v_sz_3167_);
v_i_boxed_3178_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_res_3179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3166_, v_sz_boxed_3177_, v_i_boxed_3178_, v_b_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v_as_3166_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3180_, lean_object* v_n_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
if (lean_obj_tag(v_n_3181_) == 0)
{
lean_object* v_cs_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v_cs_3190_ = lean_ctor_get(v_n_3181_, 0);
v___x_3191_ = lean_box(0);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v_b_3182_);
v_sz_3193_ = lean_array_size(v_cs_3190_);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3180_, v_cs_3190_, v_sz_3193_, v___x_3194_, v___x_3192_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3210_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3210_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3210_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v_fst_3200_; 
v_fst_3200_ = lean_ctor_get(v_a_3196_, 0);
if (lean_obj_tag(v_fst_3200_) == 0)
{
lean_object* v_snd_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v_snd_3201_ = lean_ctor_get(v_a_3196_, 1);
lean_inc(v_snd_3201_);
lean_dec(v_a_3196_);
v___x_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_snd_3201_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3202_);
v___x_3204_ = v___x_3198_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
else
{
lean_object* v_val_3206_; lean_object* v___x_3208_; 
lean_inc_ref(v_fst_3200_);
lean_dec(v_a_3196_);
v_val_3206_ = lean_ctor_get(v_fst_3200_, 0);
lean_inc(v_val_3206_);
lean_dec_ref_known(v_fst_3200_, 1);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v_val_3206_);
v___x_3208_ = v___x_3198_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_val_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
v_a_3211_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3195_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3195_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_vs_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; size_t v_sz_3222_; size_t v___x_3223_; lean_object* v___x_3224_; 
v_vs_3219_ = lean_ctor_get(v_n_3181_, 0);
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v_b_3182_);
v_sz_3222_ = lean_array_size(v_vs_3219_);
v___x_3223_ = ((size_t)0ULL);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3219_, v_sz_3222_, v___x_3223_, v___x_3221_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3239_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3239_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3239_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_fst_3229_; 
v_fst_3229_ = lean_ctor_get(v_a_3225_, 0);
if (lean_obj_tag(v_fst_3229_) == 0)
{
lean_object* v_snd_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v_snd_3230_ = lean_ctor_get(v_a_3225_, 1);
lean_inc(v_snd_3230_);
lean_dec(v_a_3225_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_snd_3230_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3231_);
v___x_3233_ = v___x_3227_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
else
{
lean_object* v_val_3235_; lean_object* v___x_3237_; 
lean_inc_ref(v_fst_3229_);
lean_dec(v_a_3225_);
v_val_3235_ = lean_ctor_get(v_fst_3229_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v_fst_3229_, 1);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v_val_3235_);
v___x_3237_ = v___x_3227_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_val_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
v_a_3240_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3224_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3224_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3248_, lean_object* v_as_3249_, size_t v_sz_3250_, size_t v_i_3251_, lean_object* v_b_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3251_, v_sz_3250_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_b_3252_);
return v___x_3261_;
}
else
{
lean_object* v_snd_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3296_; 
v_snd_3262_ = lean_ctor_get(v_b_3252_, 1);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_b_3252_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; 
v_unused_3297_ = lean_ctor_get(v_b_3252_, 0);
lean_dec(v_unused_3297_);
v___x_3264_ = v_b_3252_;
v_isShared_3265_ = v_isSharedCheck_3296_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_snd_3262_);
lean_dec(v_b_3252_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3296_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v_a_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_box(0);
v_a_3267_ = lean_array_uget_borrowed(v_as_3249_, v_i_3251_);
lean_inc(v_snd_3262_);
v___x_3268_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3248_, v_a_3267_, v_snd_3262_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3287_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3287_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3287_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
if (lean_obj_tag(v_a_3269_) == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_a_3269_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3273_);
v___x_3275_ = v___x_3264_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_snd_3262_);
v___x_3275_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3277_; 
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3275_);
v___x_3277_ = v___x_3271_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; 
lean_del_object(v___x_3271_);
lean_dec(v_snd_3262_);
v_a_3280_ = lean_ctor_get(v_a_3269_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v_a_3269_, 1);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 1, v_a_3280_);
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3282_ = v___x_3264_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_a_3280_);
v___x_3282_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
size_t v___x_3283_; size_t v___x_3284_; 
v___x_3283_ = ((size_t)1ULL);
v___x_3284_ = lean_usize_add(v_i_3251_, v___x_3283_);
v_i_3251_ = v___x_3284_;
v_b_3252_ = v___x_3282_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_del_object(v___x_3264_);
lean_dec(v_snd_3262_);
v_a_3288_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3268_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3268_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3298_, lean_object* v_as_3299_, lean_object* v_sz_3300_, lean_object* v_i_3301_, lean_object* v_b_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
size_t v_sz_boxed_3310_; size_t v_i_boxed_3311_; lean_object* v_res_3312_; 
v_sz_boxed_3310_ = lean_unbox_usize(v_sz_3300_);
lean_dec(v_sz_3300_);
v_i_boxed_3311_ = lean_unbox_usize(v_i_3301_);
lean_dec(v_i_3301_);
v_res_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3298_, v_as_3299_, v_sz_boxed_3310_, v_i_boxed_3311_, v_b_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v_as_3299_);
lean_dec_ref(v_init_3298_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3313_, lean_object* v_n_3314_, lean_object* v_b_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3313_, v_n_3314_, v_b_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_n_3314_);
lean_dec_ref(v_init_3313_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3324_, lean_object* v_init_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_root_3333_; lean_object* v_tail_3334_; lean_object* v___x_3335_; 
v_root_3333_ = lean_ctor_get(v_t_3324_, 0);
v_tail_3334_ = lean_ctor_get(v_t_3324_, 1);
lean_inc_ref(v_init_3325_);
v___x_3335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3325_, v_root_3333_, v_init_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec_ref(v_init_3325_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3372_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3372_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3372_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
if (lean_obj_tag(v_a_3336_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3342_; 
v_a_3340_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v_a_3336_, 1);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_a_3340_);
v___x_3342_ = v___x_3338_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; size_t v_sz_3347_; size_t v___x_3348_; lean_object* v___x_3349_; 
lean_del_object(v___x_3338_);
v_a_3344_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v_a_3336_, 1);
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v_a_3344_);
v_sz_3347_ = lean_array_size(v_tail_3334_);
v___x_3348_ = ((size_t)0ULL);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3334_, v_sz_3347_, v___x_3348_, v___x_3346_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3363_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3363_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3363_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_fst_3354_; 
v_fst_3354_ = lean_ctor_get(v_a_3350_, 0);
if (lean_obj_tag(v_fst_3354_) == 0)
{
lean_object* v_snd_3355_; lean_object* v___x_3357_; 
v_snd_3355_ = lean_ctor_get(v_a_3350_, 1);
lean_inc(v_snd_3355_);
lean_dec(v_a_3350_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v_snd_3355_);
v___x_3357_ = v___x_3352_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_snd_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3361_; 
lean_inc_ref(v_fst_3354_);
lean_dec(v_a_3350_);
v_val_3359_ = lean_ctor_get(v_fst_3354_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v_fst_3354_, 1);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v_val_3359_);
v___x_3361_ = v___x_3352_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_val_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
v_a_3364_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3349_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3349_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
v_a_3373_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3335_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3335_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3381_, lean_object* v_init_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3381_, v_init_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec_ref(v_t_3381_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_lctx_3400_; lean_object* v_decls_3401_; lean_object* v_hs_3402_; lean_object* v___x_3403_; 
v_lctx_3400_ = lean_ctor_get(v___y_3395_, 2);
v_decls_3401_ = lean_ctor_get(v_lctx_3400_, 1);
v_hs_3402_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3403_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3401_, v_hs_3402_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3412_, lean_object* v_cfg_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
if (v_only_3412_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_toApplyRulesConfig_3422_; lean_object* v_a_3423_; uint8_t v_symm_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_toApplyRulesConfig_3422_ = lean_ctor_get(v_cfg_3413_, 0);
v_a_3423_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3421_, 1);
v_symm_3424_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3422_, sizeof(void*)*2 + 1);
v___x_3425_ = lean_array_to_list(v_a_3423_);
v___x_3426_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3424_, v___x_3425_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3426_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v_a_3427_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3421_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3421_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3437_, lean_object* v_cfg_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v_only_boxed_3446_; lean_object* v_res_3447_; 
v_only_boxed_3446_ = lean_unbox(v_only_3437_);
v_res_3447_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3446_, v_cfg_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec_ref(v_cfg_3438_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3448_, lean_object* v_lemmas_3449_, uint8_t v_only_3450_, lean_object* v_g_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v_toApplyRulesConfig_3457_; uint8_t v_intro_3458_; uint8_t v_constructor_3459_; uint8_t v_suggestions_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3473_; 
v_toApplyRulesConfig_3457_ = lean_ctor_get(v_cfg_3448_, 0);
v_intro_3458_ = lean_ctor_get_uint8(v_cfg_3448_, sizeof(void*)*1 + 1);
v_constructor_3459_ = lean_ctor_get_uint8(v_cfg_3448_, sizeof(void*)*1 + 2);
v_suggestions_3460_ = lean_ctor_get_uint8(v_cfg_3448_, sizeof(void*)*1 + 3);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_cfg_3448_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3462_ = v_cfg_3448_;
v_isShared_3463_ = v_isSharedCheck_3473_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_toApplyRulesConfig_3457_);
lean_dec(v_cfg_3448_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3473_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v_ctx_3465_; uint8_t v___x_3466_; lean_object* v___x_3468_; 
v___x_3464_ = lean_box(v_only_3450_);
v_ctx_3465_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3465_, 0, v___x_3464_);
v___x_3466_ = 0;
if (v_isShared_3463_ == 0)
{
v___x_3468_ = v___x_3462_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_toApplyRulesConfig_3457_);
lean_ctor_set_uint8(v_reuseFailAlloc_3472_, sizeof(void*)*1 + 1, v_intro_3458_);
lean_ctor_set_uint8(v_reuseFailAlloc_3472_, sizeof(void*)*1 + 2, v_constructor_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3472_, sizeof(void*)*1 + 3, v_suggestions_3460_);
v___x_3468_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*1, v___x_3466_);
v___x_3469_ = lean_box(0);
v___x_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3470_, 0, v_g_3451_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3468_, v_lemmas_3449_, v_ctx_3465_, v___x_3470_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
return v___x_3471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3474_, lean_object* v_lemmas_3475_, lean_object* v_only_3476_, lean_object* v_g_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
uint8_t v_only_boxed_3483_; lean_object* v_res_3484_; 
v_only_boxed_3483_ = lean_unbox(v_only_3476_);
v_res_3484_ = l_Lean_MVarId_applyRules(v_cfg_3474_, v_lemmas_3475_, v_only_boxed_3483_, v_g_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3485_, size_t v_sz_3486_, size_t v_i_3487_, lean_object* v_b_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3485_, v_sz_3486_, v_i_3487_, v_b_3488_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3497_, lean_object* v_sz_3498_, lean_object* v_i_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
size_t v_sz_boxed_3508_; size_t v_i_boxed_3509_; lean_object* v_res_3510_; 
v_sz_boxed_3508_ = lean_unbox_usize(v_sz_3498_);
lean_dec(v_sz_3498_);
v_i_boxed_3509_ = lean_unbox_usize(v_i_3499_);
lean_dec(v_i_3499_);
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3497_, v_sz_boxed_3508_, v_i_boxed_3509_, v_b_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_as_3497_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3511_, size_t v_sz_3512_, size_t v_i_3513_, lean_object* v_b_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3511_, v_sz_3512_, v_i_3513_, v_b_3514_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3523_, lean_object* v_sz_3524_, lean_object* v_i_3525_, lean_object* v_b_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
size_t v_sz_boxed_3534_; size_t v_i_boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3524_);
lean_dec(v_sz_3524_);
v_i_boxed_3535_ = lean_unbox_usize(v_i_3525_);
lean_dec(v_i_3525_);
v_res_3536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3523_, v_sz_boxed_3534_, v_i_boxed_3535_, v_b_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec_ref(v_as_3523_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3545_; uint8_t v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = lean_box(0);
v___x_3546_ = 1;
v___x_3547_ = l_Lean_Elab_Term_elabTerm(v_t_3537_, v___x_3545_, v___x_3546_, v___x_3546_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_ref_3562_; uint8_t v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v_ref_3562_ = lean_ctor_get(v___y_3559_, 2);
v___x_3563_ = 0;
v___x_3564_ = l_Lean_SourceInfo_fromRef(v_ref_3562_, v___x_3563_);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3571_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object* v_a_3572_, lean_object* v_x_3573_){
_start:
{
if (lean_obj_tag(v_x_3573_) == 0)
{
uint8_t v___x_3574_; 
v___x_3574_ = 0;
return v___x_3574_;
}
else
{
lean_object* v_head_3575_; lean_object* v_tail_3576_; uint8_t v___x_3577_; 
v_head_3575_ = lean_ctor_get(v_x_3573_, 0);
v_tail_3576_ = lean_ctor_get(v_x_3573_, 1);
v___x_3577_ = lean_expr_eqv(v_a_3572_, v_head_3575_);
if (v___x_3577_ == 0)
{
v_x_3573_ = v_tail_3576_;
goto _start;
}
else
{
return v___x_3577_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object* v_a_3579_, lean_object* v_x_3580_){
_start:
{
uint8_t v_res_3581_; lean_object* v_r_3582_; 
v_res_3581_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3579_, v_x_3580_);
lean_dec(v_x_3580_);
lean_dec_ref(v_a_3579_);
v_r_3582_ = lean_box(v_res_3581_);
return v_r_3582_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(lean_object* v_ys_3583_, lean_object* v_x_3584_){
_start:
{
uint8_t v___x_3585_; 
v___x_3585_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_x_3584_, v_ys_3583_);
if (v___x_3585_ == 0)
{
uint8_t v___x_3586_; 
v___x_3586_ = 1;
return v___x_3586_;
}
else
{
uint8_t v___x_3587_; 
v___x_3587_ = 0;
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed(lean_object* v_ys_3588_, lean_object* v_x_3589_){
_start:
{
uint8_t v_res_3590_; lean_object* v_r_3591_; 
v_res_3590_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(v_ys_3588_, v_x_3589_);
lean_dec_ref(v_x_3589_);
lean_dec(v_ys_3588_);
v_r_3591_ = lean_box(v_res_3590_);
return v_r_3591_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_xs_3592_, lean_object* v_ys_3593_){
_start:
{
lean_object* v___f_3594_; lean_object* v___x_3595_; 
v___f_3594_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3594_, 0, v_ys_3593_);
v___x_3595_ = l_List_filter___redArg(v___f_3594_, v_xs_3592_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object* v_x_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = l_List_reverse___redArg(v_x_3597_);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
}
else
{
lean_object* v_head_3607_; lean_object* v_tail_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3626_; 
v_head_3607_ = lean_ctor_get(v_x_3596_, 0);
v_tail_3608_ = lean_ctor_get(v_x_3596_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_x_3596_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3610_ = v_x_3596_;
v_isShared_3611_ = v_isSharedCheck_3626_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_tail_3608_);
lean_inc(v_head_3607_);
lean_dec(v_x_3596_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3626_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; 
v___x_3612_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3607_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 1, v_x_3597_);
lean_ctor_set(v___x_3610_, 0, v_a_3613_);
v___x_3615_ = v___x_3610_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3613_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_x_3597_);
v___x_3615_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
v_x_3596_ = v_tail_3608_;
v_x_3597_ = v___x_3615_;
goto _start;
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_del_object(v___x_3610_);
lean_dec(v_tail_3608_);
lean_dec(v_x_3597_);
v_a_3618_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3612_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3612_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_x_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3627_, v_x_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3637_, uint8_t v_noDefaults_3638_, uint8_t v_star_3639_, lean_object* v_cfg_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
if (v_noDefaults_3638_ == 0)
{
goto v___jp_3648_;
}
else
{
if (v_star_3639_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
lean_dec(v_remove_3637_);
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
else
{
goto v___jp_3648_;
}
}
v___jp_3648_:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v___x_3651_ = lean_box(0);
v___x_3652_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_remove_3637_, v___x_3651_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_toApplyRulesConfig_3653_; lean_object* v_a_3654_; uint8_t v_symm_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_toApplyRulesConfig_3653_ = lean_ctor_get(v_cfg_3640_, 0);
v_a_3654_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3652_, 1);
v_symm_3655_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3653_, sizeof(void*)*2 + 1);
v___x_3656_ = lean_array_to_list(v_a_3650_);
v___x_3657_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v___x_3656_, v_a_3654_);
v___x_3658_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3655_, v___x_3657_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
return v___x_3658_;
}
else
{
lean_dec(v_a_3650_);
return v___x_3652_;
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_remove_3637_);
v_a_3659_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3649_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3649_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3669_, lean_object* v_noDefaults_3670_, lean_object* v_star_3671_, lean_object* v_cfg_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
uint8_t v_noDefaults_boxed_3680_; uint8_t v_star_boxed_3681_; lean_object* v_res_3682_; 
v_noDefaults_boxed_3680_ = lean_unbox(v_noDefaults_3670_);
v_star_boxed_3681_ = lean_unbox(v_star_3671_);
v_res_3682_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3669_, v_noDefaults_boxed_3680_, v_star_boxed_3681_, v_cfg_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v_cfg_3672_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t v_sz_3683_, size_t v_i_3684_, lean_object* v_bs_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_usize_dec_lt(v_i_3684_, v_sz_3683_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v_bs_3685_);
return v___x_3690_;
}
else
{
lean_object* v_v_3691_; lean_object* v___x_3692_; lean_object* v_bs_x27_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_v_3691_ = lean_array_uget(v_bs_3685_, v_i_3684_);
v___x_3692_ = lean_unsigned_to_nat(0u);
v_bs_x27_3693_ = lean_array_uset(v_bs_3685_, v_i_3684_, v___x_3692_);
v___x_3694_ = l_Lean_Syntax_getId(v_v_3691_);
lean_dec(v_v_3691_);
v___x_3695_ = l_Lean_labelled(v___x_3694_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; size_t v___x_3697_; size_t v___x_3698_; lean_object* v___x_3699_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = ((size_t)1ULL);
v___x_3698_ = lean_usize_add(v_i_3684_, v___x_3697_);
v___x_3699_ = lean_array_uset(v_bs_x27_3693_, v_i_3684_, v_a_3696_);
v_i_3684_ = v___x_3698_;
v_bs_3685_ = v___x_3699_;
goto _start;
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v_bs_x27_3693_);
v_a_3701_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3695_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3695_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object* v_sz_3709_, lean_object* v_i_3710_, lean_object* v_bs_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
size_t v_sz_boxed_3715_; size_t v_i_boxed_3716_; lean_object* v_res_3717_; 
v_sz_boxed_3715_ = lean_unbox_usize(v_sz_3709_);
lean_dec(v_sz_3709_);
v_i_boxed_3716_ = lean_unbox_usize(v_i_3710_);
lean_dec(v_i_3710_);
v_res_3717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_boxed_3715_, v_i_boxed_3716_, v_bs_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3718_, size_t v_i_3719_, size_t v_stop_3720_, lean_object* v_b_3721_){
_start:
{
uint8_t v___x_3722_; 
v___x_3722_ = lean_usize_dec_eq(v_i_3719_, v_stop_3720_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; 
v___x_3723_ = lean_array_uget_borrowed(v_as_3718_, v_i_3719_);
v___x_3724_ = l_Array_append___redArg(v_b_3721_, v___x_3723_);
v___x_3725_ = ((size_t)1ULL);
v___x_3726_ = lean_usize_add(v_i_3719_, v___x_3725_);
v_i_3719_ = v___x_3726_;
v_b_3721_ = v___x_3724_;
goto _start;
}
else
{
return v_b_3721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3728_, lean_object* v_i_3729_, lean_object* v_stop_3730_, lean_object* v_b_3731_){
_start:
{
size_t v_i_boxed_3732_; size_t v_stop_boxed_3733_; lean_object* v_res_3734_; 
v_i_boxed_3732_ = lean_unbox_usize(v_i_3729_);
lean_dec(v_i_3729_);
v_stop_boxed_3733_ = lean_unbox_usize(v_stop_3730_);
lean_dec(v_stop_3730_);
v_res_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3728_, v_i_boxed_3732_, v_stop_boxed_3733_, v_b_3731_);
lean_dec_ref(v_as_3728_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3735_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
if (lean_obj_tag(v_a_3753_) == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = l_List_reverse___redArg(v_a_3754_);
return v___x_3755_;
}
else
{
lean_object* v_head_3756_; lean_object* v_tail_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3766_; 
v_head_3756_ = lean_ctor_get(v_a_3753_, 0);
v_tail_3757_ = lean_ctor_get(v_a_3753_, 1);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_a_3753_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3759_ = v_a_3753_;
v_isShared_3760_ = v_isSharedCheck_3766_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_tail_3757_);
lean_inc(v_head_3756_);
lean_dec(v_a_3753_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3766_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___f_3761_; lean_object* v___x_3763_; 
v___f_3761_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3761_, 0, v_head_3756_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v_a_3754_);
lean_ctor_set(v___x_3759_, 0, v___f_3761_);
v___x_3763_ = v___x_3759_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___f_3761_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_a_3754_);
v___x_3763_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
v_a_3753_ = v_tail_3757_;
v_a_3754_ = v___x_3763_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
if (lean_obj_tag(v_a_3767_) == 0)
{
lean_object* v___x_3769_; 
v___x_3769_ = l_List_reverse___redArg(v_a_3768_);
return v___x_3769_;
}
else
{
lean_object* v_head_3770_; lean_object* v_tail_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3780_; 
v_head_3770_ = lean_ctor_get(v_a_3767_, 0);
v_tail_3771_ = lean_ctor_get(v_a_3767_, 1);
v_isSharedCheck_3780_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3773_ = v_a_3767_;
v_isShared_3774_ = v_isSharedCheck_3780_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_tail_3771_);
lean_inc(v_head_3770_);
lean_dec(v_a_3767_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3780_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3775_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3775_, 0, v_head_3770_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_a_3768_);
lean_ctor_set(v___x_3773_, 0, v___x_3775_);
v___x_3777_ = v___x_3773_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_a_3768_);
v___x_3777_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
v_a_3767_ = v_tail_3771_;
v_a_3768_ = v___x_3777_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
return v___x_3783_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3786_ = l_String_toRawSubstring_x27(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3797_ = l_String_toRawSubstring_x27(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12));
v___x_3808_ = l_String_toRawSubstring_x27(v___x_3807_);
return v___x_3808_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3819_ = l_String_toRawSubstring_x27(v___x_3818_);
return v___x_3819_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3832_ = l_Lean_stringToMessageData(v___x_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3833_, uint8_t v_star_3834_, lean_object* v_add_3835_, lean_object* v_remove_3836_, lean_object* v_use_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___f_3868_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; 
v___x_3866_ = lean_box(v_noDefaults_3833_);
v___x_3867_ = lean_box(v_star_3834_);
lean_inc(v_remove_3836_);
v___f_3868_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3868_, 0, v_remove_3836_);
lean_closure_set(v___f_3868_, 1, v___x_3866_);
lean_closure_set(v___f_3868_, 2, v___x_3867_);
if (v_star_3834_ == 0)
{
v___y_3885_ = v_a_3838_;
v___y_3886_ = v_a_3839_;
v___y_3887_ = v_a_3840_;
v___y_3888_ = v_a_3841_;
goto v___jp_3884_;
}
else
{
if (v_noDefaults_3833_ == 0)
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v___f_3868_);
lean_dec_ref(v_use_3837_);
lean_dec(v_remove_3836_);
lean_dec(v_add_3835_);
v___x_3945_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3946_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3945_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
else
{
v___y_3885_ = v_a_3838_;
v___y_3886_ = v_a_3839_;
v___y_3887_ = v_a_3840_;
v___y_3888_ = v_a_3841_;
goto v___jp_3884_;
}
}
v___jp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___y_3845_);
lean_ctor_set(v___x_3846_, 1, v___y_3844_);
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
v___jp_3848_:
{
uint8_t v___x_3855_; 
v___x_3855_ = l_List_isEmpty___redArg(v_remove_3836_);
lean_dec(v_remove_3836_);
if (v___x_3855_ == 0)
{
if (v_noDefaults_3833_ == 0)
{
v___y_3844_ = v___y_3849_;
v___y_3845_ = v___y_3854_;
goto v___jp_3843_;
}
else
{
if (v_star_3834_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3849_);
v___x_3856_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3857_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3856_, v___y_3852_, v___y_3853_, v___y_3850_, v___y_3851_);
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
else
{
v___y_3844_ = v___y_3849_;
v___y_3845_ = v___y_3854_;
goto v___jp_3843_;
}
}
}
else
{
v___y_3844_ = v___y_3849_;
v___y_3845_ = v___y_3854_;
goto v___jp_3843_;
}
}
v___jp_3869_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_array_to_list(v___y_3876_);
lean_inc(v___y_3872_);
v___x_3878_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3877_, v___y_3872_);
if (v_noDefaults_3833_ == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3835_, v___y_3872_);
v___x_3880_ = l_List_appendTR___redArg(v___x_3879_, v___x_3878_);
v___x_3881_ = l_List_appendTR___redArg(v___x_3880_, v___y_3870_);
v___y_3849_ = v___f_3868_;
v___y_3850_ = v___y_3871_;
v___y_3851_ = v___y_3874_;
v___y_3852_ = v___y_3873_;
v___y_3853_ = v___y_3875_;
v___y_3854_ = v___x_3881_;
goto v___jp_3848_;
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_dec(v___y_3870_);
v___x_3882_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3835_, v___y_3872_);
v___x_3883_ = l_List_appendTR___redArg(v___x_3882_, v___x_3878_);
v___y_3849_ = v___f_3868_;
v___y_3850_ = v___y_3871_;
v___y_3851_ = v___y_3874_;
v___y_3852_ = v___y_3873_;
v___y_3853_ = v___y_3875_;
v___y_3854_ = v___x_3883_;
goto v___jp_3848_;
}
}
v___jp_3884_:
{
lean_object* v_toCold_3889_; lean_object* v_ref_3890_; lean_object* v_quotContext_3891_; lean_object* v_currMacroScope_3892_; uint8_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v_a_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v_a_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; size_t v_sz_3927_; size_t v___x_3928_; lean_object* v___x_3929_; 
v_toCold_3889_ = lean_ctor_get(v___y_3887_, 0);
v_ref_3890_ = lean_ctor_get(v___y_3887_, 2);
v_quotContext_3891_ = lean_ctor_get(v_toCold_3889_, 8);
v_currMacroScope_3892_ = lean_ctor_get(v_toCold_3889_, 9);
v___x_3893_ = 0;
v___x_3894_ = l_Lean_SourceInfo_fromRef(v_ref_3890_, v___x_3893_);
v___x_3895_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3896_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3892_, 4);
lean_inc_n(v_quotContext_3891_, 4);
v___x_3897_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3896_, v_currMacroScope_3892_);
v___x_3898_ = lean_box(0);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6));
v___x_3900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3894_);
lean_ctor_set(v___x_3900_, 1, v___x_3895_);
lean_ctor_set(v___x_3900_, 2, v___x_3897_);
lean_ctor_set(v___x_3900_, 3, v___x_3899_);
v___x_3901_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref(v___x_3901_);
v___x_3903_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8);
v___x_3904_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9));
v___x_3905_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3904_, v_currMacroScope_3892_);
v___x_3906_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3907_, 0, v_a_3902_);
lean_ctor_set(v___x_3907_, 1, v___x_3903_);
lean_ctor_set(v___x_3907_, 2, v___x_3905_);
lean_ctor_set(v___x_3907_, 3, v___x_3906_);
v___x_3908_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3908_);
v___x_3910_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13);
v___x_3911_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14));
v___x_3912_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3911_, v_currMacroScope_3892_);
v___x_3913_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16));
v___x_3914_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3914_, 0, v_a_3909_);
lean_ctor_set(v___x_3914_, 1, v___x_3910_);
lean_ctor_set(v___x_3914_, 2, v___x_3912_);
lean_ctor_set(v___x_3914_, 3, v___x_3913_);
v___x_3915_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18);
v___x_3918_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3919_ = l_Lean_addMacroScope(v_quotContext_3891_, v___x_3918_, v_currMacroScope_3892_);
v___x_3920_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3921_, 0, v_a_3916_);
lean_ctor_set(v___x_3921_, 1, v___x_3917_);
lean_ctor_set(v___x_3921_, 2, v___x_3919_);
lean_ctor_set(v___x_3921_, 3, v___x_3920_);
v___x_3922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v___x_3898_);
v___x_3923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3914_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3907_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3900_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3925_, v___x_3898_);
v_sz_3927_ = lean_array_size(v_use_3837_);
v___x_3928_ = ((size_t)0ULL);
v___x_3929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3927_, v___x_3928_, v_use_3837_, v___y_3887_, v___y_3888_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3931_ = lean_unsigned_to_nat(0u);
v___x_3932_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3933_ = lean_array_get_size(v_a_3930_);
v___x_3934_ = lean_nat_dec_lt(v___x_3931_, v___x_3933_);
if (v___x_3934_ == 0)
{
lean_dec(v_a_3930_);
v___y_3870_ = v___x_3926_;
v___y_3871_ = v___y_3887_;
v___y_3872_ = v___x_3898_;
v___y_3873_ = v___y_3885_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___y_3886_;
v___y_3876_ = v___x_3932_;
goto v___jp_3869_;
}
else
{
size_t v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_usize_of_nat(v___x_3933_);
v___x_3936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3930_, v___x_3928_, v___x_3935_, v___x_3932_);
lean_dec(v_a_3930_);
v___y_3870_ = v___x_3926_;
v___y_3871_ = v___y_3887_;
v___y_3872_ = v___x_3898_;
v___y_3873_ = v___y_3885_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___y_3886_;
v___y_3876_ = v___x_3936_;
goto v___jp_3869_;
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v___x_3926_);
lean_dec_ref(v___f_3868_);
lean_dec(v_remove_3836_);
lean_dec(v_add_3835_);
v_a_3937_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3929_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3929_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3955_, lean_object* v_star_3956_, lean_object* v_add_3957_, lean_object* v_remove_3958_, lean_object* v_use_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
uint8_t v_noDefaults_boxed_3965_; uint8_t v_star_boxed_3966_; lean_object* v_res_3967_; 
v_noDefaults_boxed_3965_ = lean_unbox(v_noDefaults_3955_);
v_star_boxed_3966_ = lean_unbox(v_star_3956_);
v_res_3967_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3965_, v_star_boxed_3966_, v_add_3957_, v_remove_3958_, v_use_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t v_sz_3968_, size_t v_i_3969_, lean_object* v_bs_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3968_, v_i_3969_, v_bs_3970_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object* v_sz_3977_, lean_object* v_i_3978_, lean_object* v_bs_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
size_t v_sz_boxed_3985_; size_t v_i_boxed_3986_; lean_object* v_res_3987_; 
v_sz_boxed_3985_ = lean_unbox_usize(v_sz_3977_);
lean_dec(v_sz_3977_);
v_i_boxed_3986_ = lean_unbox_usize(v_i_3978_);
lean_dec(v_i_3978_);
v_res_3987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_boxed_3985_, v_i_boxed_3986_, v_bs_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3987_;
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

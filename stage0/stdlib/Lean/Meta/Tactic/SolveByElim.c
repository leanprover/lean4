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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t v___x_13917__boxed_298_; uint8_t v___x_13918__boxed_299_; lean_object* v_res_300_; 
v___x_13917__boxed_298_ = lean_unbox(v___x_289_);
v___x_13918__boxed_299_ = lean_unbox(v___x_290_);
v_res_300_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13917__boxed_298_, v___x_13918__boxed_299_, v_x_291_, v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
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
lean_object* v___x_307_; lean_object* v_env_308_; uint8_t v___x_309_; lean_object* v_env_310_; lean_object* v___x_311_; lean_object* v_toCold_312_; lean_object* v_mctx_313_; lean_object* v_lctx_314_; lean_object* v_options_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v___x_309_ = 0;
v_env_310_ = l_Lean_Environment_setRecordingDeps(v_env_308_, v___x_309_);
v___x_311_ = lean_st_ref_get(v___y_303_);
v_toCold_312_ = lean_ctor_get(v___y_304_, 0);
v_mctx_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_mctx_313_);
lean_dec(v___x_311_);
v_lctx_314_ = lean_ctor_get(v___y_302_, 2);
v_options_315_ = lean_ctor_get(v_toCold_312_, 2);
lean_inc_ref(v_options_315_);
lean_inc_ref(v_lctx_314_);
v___x_316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_316_, 0, v_env_310_);
lean_ctor_set(v___x_316_, 1, v_mctx_313_);
lean_ctor_set(v___x_316_, 2, v_lctx_314_);
lean_ctor_set(v___x_316_, 3, v_options_315_);
v___x_317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_msgData_301_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_326_, size_t v_i_327_, lean_object* v_bs_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_329_ == 0)
{
return v_bs_328_;
}
else
{
lean_object* v_v_330_; lean_object* v_msg_331_; lean_object* v___x_332_; lean_object* v_bs_x27_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v_v_330_ = lean_array_uget_borrowed(v_bs_328_, v_i_327_);
v_msg_331_ = lean_ctor_get(v_v_330_, 1);
lean_inc_ref(v_msg_331_);
v___x_332_ = lean_unsigned_to_nat(0u);
v_bs_x27_333_ = lean_array_uset(v_bs_328_, v_i_327_, v___x_332_);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_327_, v___x_334_);
v___x_336_ = lean_array_uset(v_bs_x27_333_, v_i_327_, v_msg_331_);
v_i_327_ = v___x_335_;
v_bs_328_ = v___x_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_bs_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_341_, v_i_boxed_342_, v_bs_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_344_, lean_object* v_data_345_, lean_object* v_ref_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_toCold_353_; lean_object* v_currRecDepth_354_; lean_object* v_ref_355_; uint16_t v_optionFlags_356_; uint8_t v_suppressElabErrors_357_; uint8_t v_isRecordingDeps_358_; lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_traceState_362_; lean_object* v_traces_363_; lean_object* v___x_364_; size_t v_sz_365_; size_t v___x_366_; lean_object* v___x_367_; lean_object* v_msg_368_; lean_object* v___x_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_408_; 
v_toCold_353_ = lean_ctor_get(v___y_350_, 0);
v_currRecDepth_354_ = lean_ctor_get(v___y_350_, 1);
v_ref_355_ = lean_ctor_get(v___y_350_, 2);
v_optionFlags_356_ = lean_ctor_get_uint16(v___y_350_, sizeof(void*)*3);
v_suppressElabErrors_357_ = lean_ctor_get_uint8(v___y_350_, sizeof(void*)*3 + 2);
v_isRecordingDeps_358_ = lean_ctor_get_uint8(v___y_350_, sizeof(void*)*3 + 3);
v_ref_359_ = l_Lean_replaceRef(v_ref_346_, v_ref_355_);
lean_inc(v_currRecDepth_354_);
lean_inc_ref(v_toCold_353_);
v___x_360_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_360_, 0, v_toCold_353_);
lean_ctor_set(v___x_360_, 1, v_currRecDepth_354_);
lean_ctor_set(v___x_360_, 2, v_ref_359_);
lean_ctor_set_uint16(v___x_360_, sizeof(void*)*3, v_optionFlags_356_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*3 + 2, v_suppressElabErrors_357_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*3 + 3, v_isRecordingDeps_358_);
v___x_361_ = lean_st_ref_get(v___y_351_);
v_traceState_362_ = lean_ctor_get(v___x_361_, 4);
lean_inc_ref(v_traceState_362_);
lean_dec(v___x_361_);
v_traces_363_ = lean_ctor_get(v_traceState_362_, 0);
lean_inc_ref(v_traces_363_);
lean_dec_ref(v_traceState_362_);
v___x_364_ = l_Lean_PersistentArray_toArray___redArg(v_traces_363_);
lean_dec_ref(v_traces_363_);
v_sz_365_ = lean_array_size(v___x_364_);
v___x_366_ = ((size_t)0ULL);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_365_, v___x_366_, v___x_364_);
v_msg_368_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_368_, 0, v_data_345_);
lean_ctor_set(v_msg_368_, 1, v_msg_347_);
lean_ctor_set(v_msg_368_, 2, v___x_367_);
v___x_369_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_368_, v___y_348_, v___y_349_, v___x_360_, v___y_351_);
lean_dec_ref_known(v___x_360_, 3);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_408_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_408_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_408_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v_traceState_375_; lean_object* v_env_376_; lean_object* v_nextMacroScope_377_; lean_object* v_ngen_378_; lean_object* v_auxDeclNGen_379_; lean_object* v_cache_380_; lean_object* v_recordedDeps_381_; lean_object* v_messages_382_; lean_object* v_infoState_383_; lean_object* v_snapshotTasks_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_407_; 
v___x_374_ = lean_st_ref_take(v___y_351_);
v_traceState_375_ = lean_ctor_get(v___x_374_, 4);
v_env_376_ = lean_ctor_get(v___x_374_, 0);
v_nextMacroScope_377_ = lean_ctor_get(v___x_374_, 1);
v_ngen_378_ = lean_ctor_get(v___x_374_, 2);
v_auxDeclNGen_379_ = lean_ctor_get(v___x_374_, 3);
v_cache_380_ = lean_ctor_get(v___x_374_, 5);
v_recordedDeps_381_ = lean_ctor_get(v___x_374_, 6);
v_messages_382_ = lean_ctor_get(v___x_374_, 7);
v_infoState_383_ = lean_ctor_get(v___x_374_, 8);
v_snapshotTasks_384_ = lean_ctor_get(v___x_374_, 9);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_407_ == 0)
{
v___x_386_ = v___x_374_;
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snapshotTasks_384_);
lean_inc(v_infoState_383_);
lean_inc(v_messages_382_);
lean_inc(v_recordedDeps_381_);
lean_inc(v_cache_380_);
lean_inc(v_traceState_375_);
lean_inc(v_auxDeclNGen_379_);
lean_inc(v_ngen_378_);
lean_inc(v_nextMacroScope_377_);
lean_inc(v_env_376_);
lean_dec(v___x_374_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint64_t v_tid_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_405_; 
v_tid_388_ = lean_ctor_get_uint64(v_traceState_375_, sizeof(void*)*1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_traceState_375_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v_traceState_375_, 0);
lean_dec(v_unused_406_);
v___x_390_ = v_traceState_375_;
v_isShared_391_ = v_isSharedCheck_405_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_traceState_375_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_405_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_392_ = lean_box(0);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_ref_346_);
lean_ctor_set(v___x_393_, 1, v_a_370_);
v___x_394_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_344_, v___x_393_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_394_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_394_);
lean_ctor_set_uint64(v_reuseFailAlloc_404_, sizeof(void*)*1, v_tid_388_);
v___x_396_ = v_reuseFailAlloc_404_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v___x_396_);
v___x_398_ = v___x_386_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_env_376_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_nextMacroScope_377_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_ngen_378_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_auxDeclNGen_379_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_cache_380_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_recordedDeps_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_messages_382_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v_infoState_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 9, v_snapshotTasks_384_);
v___x_398_ = v_reuseFailAlloc_403_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_st_ref_put(v___y_351_, v___x_398_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_392_);
v___x_401_ = v___x_372_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_392_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_409_, lean_object* v_data_410_, lean_object* v_ref_411_, lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_409_, v_data_410_, v_ref_411_, v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_419_){
_start:
{
if (lean_obj_tag(v_e_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 2;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_422_);
lean_dec_ref(v_e_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_425_, lean_object* v_opt_426_){
_start:
{
lean_object* v_name_427_; lean_object* v_defValue_428_; lean_object* v_map_429_; lean_object* v___x_430_; 
v_name_427_ = lean_ctor_get(v_opt_426_, 0);
v_defValue_428_ = lean_ctor_get(v_opt_426_, 1);
v_map_429_ = lean_ctor_get(v_opts_425_, 0);
v___x_430_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_429_, v_name_427_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_inc(v_defValue_428_);
return v_defValue_428_;
}
else
{
lean_object* v_val_431_; 
v_val_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_431_);
lean_dec_ref_known(v___x_430_, 1);
if (lean_obj_tag(v_val_431_) == 3)
{
lean_object* v_v_432_; 
v_v_432_ = lean_ctor_get(v_val_431_, 0);
lean_inc(v_v_432_);
lean_dec_ref_known(v_val_431_, 1);
return v_v_432_;
}
else
{
lean_dec(v_val_431_);
lean_inc(v_defValue_428_);
return v_defValue_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_433_, lean_object* v_opt_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_433_, v_opt_434_);
lean_dec_ref(v_opt_434_);
lean_dec_ref(v_opts_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_436_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v_x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v_x_436_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 1);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v_x_436_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v_x_436_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v_x_436_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_454_);
return v_res_456_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_457_; double v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_float_of_nat(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_462_; double v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(1000u);
v___x_463_ = lean_float_of_nat(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_464_, uint8_t v_collapsed_465_, lean_object* v_tag_466_, lean_object* v_opts_467_, uint8_t v_clsEnabled_468_, lean_object* v_oldTraces_469_, lean_object* v_msg_470_, lean_object* v_resStartStop_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v_data_482_; lean_object* v_fst_493_; lean_object* v_snd_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___y_498_; lean_object* v_a_499_; uint8_t v___y_514_; double v___y_546_; 
v_fst_477_ = lean_ctor_get(v_resStartStop_471_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v_resStartStop_471_, 1);
lean_inc(v_snd_478_);
lean_dec_ref(v_resStartStop_471_);
v_fst_493_ = lean_ctor_get(v_snd_478_, 0);
lean_inc(v_fst_493_);
v_snd_494_ = lean_ctor_get(v_snd_478_, 1);
lean_inc(v_snd_494_);
lean_dec(v_snd_478_);
v___x_495_ = l_Lean_trace_profiler;
v___x_496_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_467_, v___x_495_);
if (v___x_496_ == 0)
{
v___y_514_ = v___x_496_;
goto v___jp_513_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = l_Lean_trace_profiler_useHeartbeats;
v___x_552_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_467_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; double v___x_555_; double v___x_556_; double v___x_557_; 
v___x_553_ = l_Lean_trace_profiler_threshold;
v___x_554_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_467_, v___x_553_);
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
v___x_559_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_467_, v___x_558_);
v___x_560_ = lean_float_of_nat(v___x_559_);
v___y_546_ = v___x_560_;
goto v___jp_545_;
}
}
v___jp_479_:
{
lean_object* v___x_483_; 
lean_inc(v___y_481_);
v___x_483_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_469_, v_data_482_, v___y_481_, v___y_480_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; 
lean_dec_ref_known(v___x_483_, 1);
v___x_484_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_477_);
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_fst_477_);
v_a_485_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_483_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
v___jp_497_:
{
uint8_t v_result_500_; lean_object* v___x_501_; lean_object* v___x_502_; double v___x_503_; lean_object* v_data_504_; 
v_result_500_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_477_);
v___x_501_ = lean_box(v_result_500_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_466_);
lean_inc_ref(v___x_502_);
lean_inc(v_cls_464_);
v_data_504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_504_, 0, v_cls_464_);
lean_ctor_set(v_data_504_, 1, v___x_502_);
lean_ctor_set(v_data_504_, 2, v_tag_466_);
lean_ctor_set_float(v_data_504_, sizeof(void*)*3, v___x_503_);
lean_ctor_set_float(v_data_504_, sizeof(void*)*3 + 8, v___x_503_);
lean_ctor_set_uint8(v_data_504_, sizeof(void*)*3 + 16, v_collapsed_465_);
if (v___x_496_ == 0)
{
lean_dec_ref_known(v___x_502_, 1);
lean_dec(v_snd_494_);
lean_dec(v_fst_493_);
lean_dec_ref(v_tag_466_);
lean_dec(v_cls_464_);
v___y_480_ = v_a_499_;
v___y_481_ = v___y_498_;
v_data_482_ = v_data_504_;
goto v___jp_479_;
}
else
{
lean_object* v_data_505_; double v___x_506_; double v___x_507_; 
lean_dec_ref_known(v_data_504_, 3);
v_data_505_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_505_, 0, v_cls_464_);
lean_ctor_set(v_data_505_, 1, v___x_502_);
lean_ctor_set(v_data_505_, 2, v_tag_466_);
v___x_506_ = lean_unbox_float(v_fst_493_);
lean_dec(v_fst_493_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3, v___x_506_);
v___x_507_ = lean_unbox_float(v_snd_494_);
lean_dec(v_snd_494_);
lean_ctor_set_float(v_data_505_, sizeof(void*)*3 + 8, v___x_507_);
lean_ctor_set_uint8(v_data_505_, sizeof(void*)*3 + 16, v_collapsed_465_);
v___y_480_ = v_a_499_;
v___y_481_ = v___y_498_;
v_data_482_ = v_data_505_;
goto v___jp_479_;
}
}
v___jp_508_:
{
lean_object* v_ref_509_; lean_object* v___x_510_; 
v_ref_509_ = lean_ctor_get(v___y_474_, 2);
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v_fst_477_);
v___x_510_ = lean_apply_6(v_msg_470_, v_fst_477_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, lean_box(0));
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___y_498_ = v_ref_509_;
v_a_499_ = v_a_511_;
goto v___jp_497_;
}
else
{
lean_object* v___x_512_; 
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_498_ = v_ref_509_;
v_a_499_ = v___x_512_;
goto v___jp_497_;
}
}
v___jp_513_:
{
if (v_clsEnabled_468_ == 0)
{
if (v___y_514_ == 0)
{
lean_object* v___x_515_; lean_object* v_traceState_516_; lean_object* v_env_517_; lean_object* v_nextMacroScope_518_; lean_object* v_ngen_519_; lean_object* v_auxDeclNGen_520_; lean_object* v_cache_521_; lean_object* v_recordedDeps_522_; lean_object* v_messages_523_; lean_object* v_infoState_524_; lean_object* v_snapshotTasks_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_snd_494_);
lean_dec(v_fst_493_);
lean_dec_ref(v_msg_470_);
lean_dec_ref(v_tag_466_);
lean_dec(v_cls_464_);
v___x_515_ = lean_st_ref_take(v___y_475_);
v_traceState_516_ = lean_ctor_get(v___x_515_, 4);
v_env_517_ = lean_ctor_get(v___x_515_, 0);
v_nextMacroScope_518_ = lean_ctor_get(v___x_515_, 1);
v_ngen_519_ = lean_ctor_get(v___x_515_, 2);
v_auxDeclNGen_520_ = lean_ctor_get(v___x_515_, 3);
v_cache_521_ = lean_ctor_get(v___x_515_, 5);
v_recordedDeps_522_ = lean_ctor_get(v___x_515_, 6);
v_messages_523_ = lean_ctor_get(v___x_515_, 7);
v_infoState_524_ = lean_ctor_get(v___x_515_, 8);
v_snapshotTasks_525_ = lean_ctor_get(v___x_515_, 9);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_544_ == 0)
{
v___x_527_ = v___x_515_;
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snapshotTasks_525_);
lean_inc(v_infoState_524_);
lean_inc(v_messages_523_);
lean_inc(v_recordedDeps_522_);
lean_inc(v_cache_521_);
lean_inc(v_traceState_516_);
lean_inc(v_auxDeclNGen_520_);
lean_inc(v_ngen_519_);
lean_inc(v_nextMacroScope_518_);
lean_inc(v_env_517_);
lean_dec(v___x_515_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_544_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint64_t v_tid_529_; lean_object* v_traces_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_543_; 
v_tid_529_ = lean_ctor_get_uint64(v_traceState_516_, sizeof(void*)*1);
v_traces_530_ = lean_ctor_get(v_traceState_516_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_traceState_516_);
if (v_isSharedCheck_543_ == 0)
{
v___x_532_ = v_traceState_516_;
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_traces_530_);
lean_dec(v_traceState_516_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_469_, v_traces_530_);
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
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_env_517_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_nextMacroScope_518_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_ngen_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_auxDeclNGen_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v_cache_521_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v_recordedDeps_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v_messages_523_);
lean_ctor_set(v_reuseFailAlloc_541_, 8, v_infoState_524_);
lean_ctor_set(v_reuseFailAlloc_541_, 9, v_snapshotTasks_525_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_put(v___y_475_, v___x_538_);
v___x_540_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_477_);
return v___x_540_;
}
}
}
}
}
else
{
goto v___jp_508_;
}
}
else
{
goto v___jp_508_;
}
}
v___jp_545_:
{
double v___x_547_; double v___x_548_; double v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unbox_float(v_snd_494_);
v___x_548_ = lean_unbox_float(v_fst_493_);
v___x_549_ = lean_float_sub(v___x_547_, v___x_548_);
v___x_550_ = lean_float_decLt(v___y_546_, v___x_549_);
v___y_514_ = v___x_550_;
goto v___jp_513_;
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
uint8_t v___x_14344__boxed_619_; lean_object* v_res_620_; 
v___x_14344__boxed_619_ = lean_unbox(v___x_611_);
v_res_620_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14344__boxed_619_, v_x_612_, v_x_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
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
uint8_t v___x_14421__boxed_663_; lean_object* v_res_664_; 
v___x_14421__boxed_663_ = lean_unbox(v___x_655_);
v_res_664_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14421__boxed_663_, v_x_656_, v_x_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
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
lean_object* v_toCold_684_; lean_object* v_options_685_; lean_object* v_inheritedTraceOptions_686_; uint8_t v_hasTrace_687_; lean_object* v___y_689_; 
v_toCold_684_ = lean_ctor_get(v___y_681_, 0);
v_options_685_ = lean_ctor_get(v_toCold_684_, 2);
v_inheritedTraceOptions_686_ = lean_ctor_get(v_toCold_684_, 11);
v_hasTrace_687_ = lean_ctor_get_uint8(v_options_685_, sizeof(void*)*1);
if (v_hasTrace_687_ == 0)
{
lean_object* v___x_710_; uint8_t v_transparency_711_; uint8_t v___x_712_; 
lean_dec_ref(v___f_678_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_675_);
v___x_710_ = l_Lean_Meta_Context_config(v___y_679_);
v_transparency_711_ = lean_ctor_get_uint8(v___x_710_, 9);
lean_dec_ref(v___x_710_);
v___x_712_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_711_, v_transparency_670_);
if (v___x_712_ == 0)
{
lean_object* v_keyedConfig_713_; uint8_t v_trackZetaDelta_714_; lean_object* v_zetaDeltaSet_715_; lean_object* v_lctx_716_; lean_object* v_localInstances_717_; lean_object* v_defEqCtx_x3f_718_; lean_object* v_synthPendingDepth_719_; lean_object* v_customCanUnfoldPredicate_x3f_720_; uint8_t v_univApprox_721_; uint8_t v_inTypeClassResolution_722_; uint8_t v_cacheInferType_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_keyedConfig_713_ = lean_ctor_get(v___y_679_, 0);
v_trackZetaDelta_714_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7);
v_zetaDeltaSet_715_ = lean_ctor_get(v___y_679_, 1);
v_lctx_716_ = lean_ctor_get(v___y_679_, 2);
v_localInstances_717_ = lean_ctor_get(v___y_679_, 3);
v_defEqCtx_x3f_718_ = lean_ctor_get(v___y_679_, 4);
v_synthPendingDepth_719_ = lean_ctor_get(v___y_679_, 5);
v_customCanUnfoldPredicate_x3f_720_ = lean_ctor_get(v___y_679_, 6);
v_univApprox_721_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_722_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 2);
v_cacheInferType_723_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_713_);
v___x_724_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_670_, v_keyedConfig_713_);
lean_inc(v_customCanUnfoldPredicate_x3f_720_);
lean_inc(v_synthPendingDepth_719_);
lean_inc(v_defEqCtx_x3f_718_);
lean_inc_ref(v_localInstances_717_);
lean_inc_ref(v_lctx_716_);
lean_inc(v_zetaDeltaSet_715_);
v___x_725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_zetaDeltaSet_715_);
lean_ctor_set(v___x_725_, 2, v_lctx_716_);
lean_ctor_set(v___x_725_, 3, v_localInstances_717_);
lean_ctor_set(v___x_725_, 4, v_defEqCtx_x3f_718_);
lean_ctor_set(v___x_725_, 5, v_synthPendingDepth_719_);
lean_ctor_set(v___x_725_, 6, v_customCanUnfoldPredicate_x3f_720_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*7, v_trackZetaDelta_714_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*7 + 1, v_univApprox_721_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*7 + 2, v_inTypeClassResolution_722_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*7 + 3, v_cacheInferType_723_);
v___x_726_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___x_725_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref_known(v___x_725_, 7);
v___y_689_ = v___x_726_;
goto v___jp_688_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v___y_689_ = v___x_727_;
goto v___jp_688_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v_a_734_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v_a_749_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_a_772_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v_a_784_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v_a_789_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; 
v___x_728_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_675_);
v___x_729_ = l_Lean_Name_append(v___x_728_, v___x_675_);
v___x_730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_686_, v_options_685_, v___x_729_);
lean_dec(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___y_850_; 
v___x_847_ = l_Lean_trace_profiler;
v___x_848_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_685_, v___x_847_);
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
v___x_853_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_848_, v_hasTrace_687_, v_a_851_, v___x_852_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
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
v___x_736_ = lean_float_of_nat(v___y_733_);
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
v___x_745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_675_, v___x_676_, v___x_677_, v_options_685_, v___x_730_, v___y_732_, v___f_678_, v___x_744_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
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
v___x_763_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_757_, v_hasTrace_687_, v_a_761_, v___x_762_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_List_reverse___redArg(v_a_764_);
v___y_752_ = v___y_758_;
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
v___y_752_ = v___y_758_;
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
v___y_747_ = v___y_758_;
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
v___y_747_ = v___y_758_;
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
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_675_, v___x_676_, v___x_677_, v_options_685_, v___x_730_, v___y_771_, v___f_678_, v___x_779_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
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
v___x_808_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_685_, v___x_807_);
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
v___y_757_ = v___x_808_;
v___y_758_ = v_a_806_;
v___y_759_ = v___x_809_;
v___y_760_ = v___x_826_;
goto v___jp_756_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_MVarId_apply(v_g_671_, v_e_672_, v_cfg_673_, v___x_674_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v___y_757_ = v___x_808_;
v___y_758_ = v_a_806_;
v___y_759_ = v___x_809_;
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
v___jp_688_:
{
if (lean_obj_tag(v___y_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_690_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___y_689_, 1);
v___x_691_ = lean_box(0);
v___x_692_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_687_, v_a_690_, v___x_691_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_679_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_List_reverse___redArg(v_a_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
return v___x_692_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v___y_679_);
v_a_702_ = lean_ctor_get(v___y_689_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___y_689_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___y_689_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___y_689_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_889_, lean_object* v_g_890_, lean_object* v_e_891_, lean_object* v_cfg_892_, lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v___f_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v_transparency_boxed_903_; uint8_t v___x_14509__boxed_904_; lean_object* v_res_905_; 
v_transparency_boxed_903_ = lean_unbox(v_transparency_889_);
v___x_14509__boxed_904_ = lean_unbox(v___x_895_);
v_res_905_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_903_, v_g_890_, v_e_891_, v_cfg_892_, v___x_893_, v___x_894_, v___x_14509__boxed_904_, v___x_896_, v___f_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
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
lean_object* v___x_943_; lean_object* v___f_944_; lean_object* v___x_945_; 
v___x_943_ = lean_box(v_transparency_937_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_944_, 0, v___x_943_);
lean_closure_set(v___f_944_, 1, v_g_939_);
lean_closure_set(v___f_944_, 2, v_cfg_936_);
v___x_945_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_938_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_950_, 0, lean_box(0));
lean_closure_set(v___x_950_, 1, lean_box(0));
lean_closure_set(v___x_950_, 2, v___f_944_);
lean_closure_set(v___x_950_, 3, v_a_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
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
lean_dec_ref(v___f_944_);
v_a_955_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_945_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_945_);
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
v___x_1292_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_839__boxed_1396_; size_t v_x_840__boxed_1397_; lean_object* v_res_1398_; 
v_x_839__boxed_1396_ = lean_unbox_usize(v_x_1392_);
lean_dec(v_x_1392_);
v_x_840__boxed_1397_ = lean_unbox_usize(v_x_1393_);
lean_dec(v_x_1393_);
v_res_1398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1391_, v_x_839__boxed_1396_, v_x_840__boxed_1397_, v_x_1394_, v_x_1395_);
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
lean_object* v___x_1410_; lean_object* v_mctx_1411_; lean_object* v_cache_1412_; lean_object* v_zetaDeltaFVarIds_1413_; lean_object* v_postponed_1414_; lean_object* v_diag_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1445_; 
v___x_1410_ = lean_st_ref_take(v___y_1408_);
v_mctx_1411_ = lean_ctor_get(v___x_1410_, 0);
v_cache_1412_ = lean_ctor_get(v___x_1410_, 1);
v_zetaDeltaFVarIds_1413_ = lean_ctor_get(v___x_1410_, 2);
v_postponed_1414_ = lean_ctor_get(v___x_1410_, 3);
v_diag_1415_ = lean_ctor_get(v___x_1410_, 4);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1417_ = v___x_1410_;
v_isShared_1418_ = v_isSharedCheck_1445_;
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
v_isShared_1418_ = v_isSharedCheck_1445_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_depth_1419_; lean_object* v_levelAssignDepth_1420_; lean_object* v_lmvarCounter_1421_; lean_object* v_mvarCounter_1422_; lean_object* v_lDecls_1423_; lean_object* v_decls_1424_; lean_object* v_userNames_1425_; lean_object* v_lAssignment_1426_; lean_object* v_eAssignment_1427_; lean_object* v_dAssignment_1428_; lean_object* v_instanceTypedMVars_1429_; lean_object* v_synthNormMemo_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1444_; 
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
v_synthNormMemo_1430_ = lean_ctor_get(v_mctx_1411_, 11);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_mctx_1411_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1432_ = v_mctx_1411_;
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_synthNormMemo_1430_);
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
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1427_, v_mvarId_1406_, v_val_1407_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 8, v___x_1435_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_depth_1419_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_levelAssignDepth_1420_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_lmvarCounter_1421_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_mvarCounter_1422_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_lDecls_1423_);
lean_ctor_set(v_reuseFailAlloc_1443_, 5, v_decls_1424_);
lean_ctor_set(v_reuseFailAlloc_1443_, 6, v_userNames_1425_);
lean_ctor_set(v_reuseFailAlloc_1443_, 7, v_lAssignment_1426_);
lean_ctor_set(v_reuseFailAlloc_1443_, 8, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1443_, 9, v_dAssignment_1428_);
lean_ctor_set(v_reuseFailAlloc_1443_, 10, v_instanceTypedMVars_1429_);
lean_ctor_set(v_reuseFailAlloc_1443_, 11, v_synthNormMemo_1430_);
v___x_1437_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1437_);
v___x_1439_ = v___x_1417_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_cache_1412_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_zetaDeltaFVarIds_1413_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_postponed_1414_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v_diag_1415_);
v___x_1439_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_st_ref_put(v___y_1408_, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1434_);
return v___x_1441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1446_, lean_object* v_val_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1446_, v_val_1447_, v___y_1448_);
lean_dec(v___y_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
lean_inc(v_g_1451_);
v___x_1457_ = l_Lean_MVarId_getType(v_g_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = lean_box(0);
v___x_1460_ = l_Lean_Meta_synthInstance(v_a_1458_, v___x_1459_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1451_, v_a_1461_, v___y_1453_);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1471_);
v___x_1464_ = v___x_1462_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v___x_1462_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_box(0);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_g_1451_);
v_a_1472_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1460_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1460_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_g_1451_);
v_a_1480_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1457_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1457_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1496_){
_start:
{
lean_object* v___f_1497_; lean_object* v___x_1498_; 
v___f_1497_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1498_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1496_, v___f_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1499_, lean_object* v_val_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1499_, v_val_1500_, v___y_1502_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1507_, lean_object* v_val_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1507_, v_val_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1516_, v_x_1517_, v_x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1520_, lean_object* v_x_1521_, size_t v_x_1522_, size_t v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1521_, v_x_1522_, v_x_1523_, v_x_1524_, v_x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
size_t v_x_1160__boxed_1533_; size_t v_x_1161__boxed_1534_; lean_object* v_res_1535_; 
v_x_1160__boxed_1533_ = lean_unbox_usize(v_x_1529_);
lean_dec(v_x_1529_);
v_x_1161__boxed_1534_ = lean_unbox_usize(v_x_1530_);
lean_dec(v_x_1530_);
v_res_1535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1527_, v_x_1528_, v_x_1160__boxed_1533_, v_x_1161__boxed_1534_, v_x_1531_, v_x_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1536_, lean_object* v_n_1537_, lean_object* v_k_1538_, lean_object* v_v_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1537_, v_k_1538_, v_v_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1541_, size_t v_depth_1542_, lean_object* v_keys_1543_, lean_object* v_vals_1544_, lean_object* v_heq_1545_, lean_object* v_i_1546_, lean_object* v_entries_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1542_, v_keys_1543_, v_vals_1544_, v_i_1546_, v_entries_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1549_, lean_object* v_depth_1550_, lean_object* v_keys_1551_, lean_object* v_vals_1552_, lean_object* v_heq_1553_, lean_object* v_i_1554_, lean_object* v_entries_1555_){
_start:
{
size_t v_depth_boxed_1556_; lean_object* v_res_1557_; 
v_depth_boxed_1556_ = lean_unbox_usize(v_depth_1550_);
lean_dec(v_depth_1550_);
v_res_1557_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1549_, v_depth_boxed_1556_, v_keys_1551_, v_vals_1552_, v_heq_1553_, v_i_1554_, v_entries_1555_);
lean_dec_ref(v_vals_1552_);
lean_dec_ref(v_keys_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1559_, v_x_1560_, v_x_1561_, v_x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1564_, lean_object* v_discharge_1565_, lean_object* v_g_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
lean_inc(v_g_1566_);
v___x_1572_ = lean_apply_6(v_discharge_1564_, v_g_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, lean_box(0));
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec(v_g_1566_);
lean_dec_ref(v_discharge_1565_);
return v___x_1572_;
}
else
{
lean_object* v_a_1573_; uint8_t v___y_1575_; uint8_t v___x_1577_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
v___x_1577_ = l_Lean_Exception_isInterrupt(v_a_1573_);
if (v___x_1577_ == 0)
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Lean_Exception_isRuntime(v_a_1573_);
v___y_1575_ = v___x_1578_;
goto v___jp_1574_;
}
else
{
lean_dec(v_a_1573_);
v___y_1575_ = v___x_1577_;
goto v___jp_1574_;
}
v___jp_1574_:
{
if (v___y_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref_known(v___x_1572_, 1);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1576_ = lean_apply_6(v_discharge_1565_, v_g_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, lean_box(0));
return v___x_1576_;
}
else
{
lean_dec(v_g_1566_);
lean_dec_ref(v_discharge_1565_);
return v___x_1572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1579_, lean_object* v_discharge_1580_, lean_object* v_g_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1579_, v_discharge_1580_, v_g_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1588_, lean_object* v_discharge_1589_){
_start:
{
lean_object* v_toApplyRulesConfig_1590_; lean_object* v_toBacktrackConfig_1591_; uint8_t v_backtracking_1592_; uint8_t v_intro_1593_; uint8_t v_constructor_1594_; uint8_t v_suggestions_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1627_; 
v_toApplyRulesConfig_1590_ = lean_ctor_get(v_cfg_1588_, 0);
lean_inc_ref(v_toApplyRulesConfig_1590_);
v_toBacktrackConfig_1591_ = lean_ctor_get(v_toApplyRulesConfig_1590_, 0);
lean_inc_ref(v_toBacktrackConfig_1591_);
v_backtracking_1592_ = lean_ctor_get_uint8(v_cfg_1588_, sizeof(void*)*1);
v_intro_1593_ = lean_ctor_get_uint8(v_cfg_1588_, sizeof(void*)*1 + 1);
v_constructor_1594_ = lean_ctor_get_uint8(v_cfg_1588_, sizeof(void*)*1 + 2);
v_suggestions_1595_ = lean_ctor_get_uint8(v_cfg_1588_, sizeof(void*)*1 + 3);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_cfg_1588_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v_cfg_1588_, 0);
lean_dec(v_unused_1628_);
v___x_1597_ = v_cfg_1588_;
v_isShared_1598_ = v_isSharedCheck_1627_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v_cfg_1588_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1627_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_toApplyConfig_1599_; uint8_t v_transparency_1600_; uint8_t v_symm_1601_; uint8_t v_exfalso_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1625_; 
v_toApplyConfig_1599_ = lean_ctor_get(v_toApplyRulesConfig_1590_, 1);
v_transparency_1600_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1590_, sizeof(void*)*2);
v_symm_1601_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1590_, sizeof(void*)*2 + 1);
v_exfalso_1602_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1590_, sizeof(void*)*2 + 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_toApplyRulesConfig_1590_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v_toApplyRulesConfig_1590_, 0);
lean_dec(v_unused_1626_);
v___x_1604_ = v_toApplyRulesConfig_1590_;
v_isShared_1605_ = v_isSharedCheck_1625_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_toApplyConfig_1599_);
lean_dec(v_toApplyRulesConfig_1590_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1625_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_maxDepth_1606_; lean_object* v_proc_1607_; lean_object* v_suspend_1608_; lean_object* v_discharge_1609_; uint8_t v_commitIndependentGoals_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1624_; 
v_maxDepth_1606_ = lean_ctor_get(v_toBacktrackConfig_1591_, 0);
v_proc_1607_ = lean_ctor_get(v_toBacktrackConfig_1591_, 1);
v_suspend_1608_ = lean_ctor_get(v_toBacktrackConfig_1591_, 2);
v_discharge_1609_ = lean_ctor_get(v_toBacktrackConfig_1591_, 3);
v_commitIndependentGoals_1610_ = lean_ctor_get_uint8(v_toBacktrackConfig_1591_, sizeof(void*)*4);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_toBacktrackConfig_1591_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1612_ = v_toBacktrackConfig_1591_;
v_isShared_1613_ = v_isSharedCheck_1624_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_discharge_1609_);
lean_inc(v_suspend_1608_);
lean_inc(v_proc_1607_);
lean_inc(v_maxDepth_1606_);
lean_dec(v_toBacktrackConfig_1591_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1624_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___f_1614_; lean_object* v___x_1616_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1614_, 0, v_discharge_1589_);
lean_closure_set(v___f_1614_, 1, v_discharge_1609_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 3, v___f_1614_);
v___x_1616_ = v___x_1612_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_maxDepth_1606_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_proc_1607_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_suspend_1608_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v___f_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1623_, sizeof(void*)*4, v_commitIndependentGoals_1610_);
v___x_1616_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1616_);
v___x_1618_ = v___x_1604_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_toApplyConfig_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1622_, sizeof(void*)*2, v_transparency_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1622_, sizeof(void*)*2 + 1, v_symm_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1622_, sizeof(void*)*2 + 2, v_exfalso_1602_);
v___x_1618_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1620_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1618_);
v___x_1620_ = v___x_1597_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*1, v_backtracking_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*1 + 1, v_intro_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*1 + 2, v_constructor_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*1 + 3, v_suggestions_1595_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = 1;
v___x_1636_ = l_Lean_Meta_intro1Core(v_g_1629_, v___x_1635_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1655_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1655_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1655_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_snd_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1653_; 
v_snd_1641_ = lean_ctor_get(v_a_1637_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_a_1637_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v_a_1637_, 0);
lean_dec(v_unused_1654_);
v___x_1643_ = v_a_1637_;
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snd_1641_);
lean_dec(v_a_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_box(0);
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 1);
lean_ctor_set(v___x_1643_, 1, v___x_1645_);
lean_ctor_set(v___x_1643_, 0, v_snd_1641_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_snd_1641_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1648_);
v___x_1650_ = v___x_1639_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1636_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1636_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1672_){
_start:
{
lean_object* v___f_1673_; lean_object* v___x_1674_; 
v___f_1673_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1674_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1672_, v___f_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1686_ = l_Lean_MVarId_constructor(v_g_1679_, v___x_1685_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
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
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_a_1687_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1686_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1686_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1712_){
_start:
{
lean_object* v___f_1713_; lean_object* v___x_1714_; 
v___f_1713_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1714_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1712_, v___f_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
lean_inc(v_g_1717_);
v___x_1723_ = l_Lean_MVarId_getType(v_g_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_box(0);
v___x_1726_ = l_Lean_Meta_synthInstance(v_a_1724_, v___x_1725_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1736_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1717_, v_a_1727_, v___y_1719_);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1728_, 0);
lean_dec(v_unused_1737_);
v___x_1730_ = v___x_1728_;
v_isShared_1731_ = v_isSharedCheck_1736_;
goto v_resetjp_1729_;
}
else
{
lean_dec(v___x_1728_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1736_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1732_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_g_1717_);
v_a_1738_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1726_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1726_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_g_1717_);
v_a_1746_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1723_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1723_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1762_){
_start:
{
lean_object* v___f_1763_; lean_object* v___x_1764_; 
v___f_1763_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1764_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1762_, v___f_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Lean_Expr_hasMVar(v_e_1765_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_e_1765_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; lean_object* v_mctx_1771_; lean_object* v___x_1772_; lean_object* v_fst_1773_; lean_object* v_snd_1774_; lean_object* v___x_1775_; lean_object* v_cache_1776_; lean_object* v_zetaDeltaFVarIds_1777_; lean_object* v_postponed_1778_; lean_object* v_diag_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1788_; 
v___x_1770_ = lean_st_ref_get(v___y_1766_);
v_mctx_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc_ref(v_mctx_1771_);
lean_dec(v___x_1770_);
v___x_1772_ = l_Lean_instantiateMVarsCore(v_mctx_1771_, v_e_1765_);
v_fst_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_fst_1773_);
v_snd_1774_ = lean_ctor_get(v___x_1772_, 1);
lean_inc(v_snd_1774_);
lean_dec_ref(v___x_1772_);
v___x_1775_ = lean_st_ref_take(v___y_1766_);
v_cache_1776_ = lean_ctor_get(v___x_1775_, 1);
v_zetaDeltaFVarIds_1777_ = lean_ctor_get(v___x_1775_, 2);
v_postponed_1778_ = lean_ctor_get(v___x_1775_, 3);
v_diag_1779_ = lean_ctor_get(v___x_1775_, 4);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1775_, 0);
lean_dec(v_unused_1789_);
v___x_1781_ = v___x_1775_;
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_diag_1779_);
lean_inc(v_postponed_1778_);
lean_inc(v_zetaDeltaFVarIds_1777_);
lean_inc(v_cache_1776_);
lean_dec(v___x_1775_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v_snd_1774_);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_snd_1774_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_cache_1776_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_zetaDeltaFVarIds_1777_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_postponed_1778_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_diag_1779_);
v___x_1784_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_st_ref_put(v___y_1766_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_fst_1773_);
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1790_, v___y_1791_);
lean_dec(v___y_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1794_, v___y_1796_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1808_, v_x_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1815_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1815_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1832_, v_x_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1840_, lean_object* v_mvarId_1841_, lean_object* v_x_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1841_, v_x_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_mvarId_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1849_, v_mvarId_1850_, v_x_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_ref_1864_; lean_object* v___x_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1874_; 
v_ref_1864_ = lean_ctor_get(v___y_1861_, 2);
v___x_1865_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_inc(v_ref_1864_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_ref_1864_);
lean_ctor_set(v___x_1870_, 1, v_a_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 1);
lean_ctor_set(v___x_1868_, 0, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = l_List_reverse___redArg(v_x_1883_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v_head_1891_; lean_object* v_tail_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1912_; 
v_head_1891_ = lean_ctor_get(v_x_1882_, 0);
v_tail_1892_ = lean_ctor_get(v_x_1882_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1894_ = v_x_1882_;
v_isShared_1895_ = v_isSharedCheck_1912_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_tail_1892_);
lean_inc(v_head_1891_);
lean_dec(v_x_1882_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1912_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_inc(v_head_1891_);
v___x_1896_ = l_Lean_Expr_mvar___override(v_head_1891_);
v___x_1897_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1891_, v___x_1897_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v_x_1883_);
lean_ctor_set(v___x_1894_, 0, v_a_1899_);
v___x_1901_ = v___x_1894_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1899_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_x_1883_);
v___x_1901_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v_x_1882_ = v_tail_1892_;
v_x_1883_ = v___x_1901_;
goto _start;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1894_);
lean_dec(v_tail_1892_);
lean_dec(v_x_1883_);
v_a_1904_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1898_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1898_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1913_, v_x_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1920_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1923_ = l_Lean_stringToMessageData(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1924_, lean_object* v_proc_1925_, lean_object* v_orig_1926_, lean_object* v_goals_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_box(0);
lean_inc(v_orig_1926_);
v___x_1934_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1926_, v___x_1933_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
v___x_1936_ = lean_apply_6(v_test_1924_, v_a_1935_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, lean_box(0));
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; uint8_t v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = lean_unbox(v_a_1937_);
lean_dec(v_a_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_goals_1927_);
lean_dec(v_orig_1926_);
lean_dec_ref(v_proc_1925_);
v___x_1939_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1940_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1939_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
else
{
lean_object* v___x_1949_; 
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
v___x_1949_ = lean_apply_7(v_proc_1925_, v_orig_1926_, v_goals_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, lean_box(0));
return v___x_1949_;
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_goals_1927_);
lean_dec(v_orig_1926_);
lean_dec_ref(v_proc_1925_);
v_a_1950_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1936_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1936_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_goals_1927_);
lean_dec(v_orig_1926_);
lean_dec_ref(v_proc_1925_);
lean_dec_ref(v_test_1924_);
v_a_1958_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1934_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1934_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1966_, lean_object* v_proc_1967_, lean_object* v_orig_1968_, lean_object* v_goals_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1966_, v_proc_1967_, v_orig_1968_, v_goals_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1976_, lean_object* v_test_1977_){
_start:
{
lean_object* v_toApplyRulesConfig_1978_; lean_object* v_toBacktrackConfig_1979_; uint8_t v_backtracking_1980_; uint8_t v_intro_1981_; uint8_t v_constructor_1982_; uint8_t v_suggestions_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2015_; 
v_toApplyRulesConfig_1978_ = lean_ctor_get(v_cfg_1976_, 0);
lean_inc_ref(v_toApplyRulesConfig_1978_);
v_toBacktrackConfig_1979_ = lean_ctor_get(v_toApplyRulesConfig_1978_, 0);
lean_inc_ref(v_toBacktrackConfig_1979_);
v_backtracking_1980_ = lean_ctor_get_uint8(v_cfg_1976_, sizeof(void*)*1);
v_intro_1981_ = lean_ctor_get_uint8(v_cfg_1976_, sizeof(void*)*1 + 1);
v_constructor_1982_ = lean_ctor_get_uint8(v_cfg_1976_, sizeof(void*)*1 + 2);
v_suggestions_1983_ = lean_ctor_get_uint8(v_cfg_1976_, sizeof(void*)*1 + 3);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_cfg_1976_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_cfg_1976_, 0);
lean_dec(v_unused_2016_);
v___x_1985_ = v_cfg_1976_;
v_isShared_1986_ = v_isSharedCheck_2015_;
goto v_resetjp_1984_;
}
else
{
lean_dec(v_cfg_1976_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2015_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_toApplyConfig_1987_; uint8_t v_transparency_1988_; uint8_t v_symm_1989_; uint8_t v_exfalso_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2013_; 
v_toApplyConfig_1987_ = lean_ctor_get(v_toApplyRulesConfig_1978_, 1);
v_transparency_1988_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1978_, sizeof(void*)*2);
v_symm_1989_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1978_, sizeof(void*)*2 + 1);
v_exfalso_1990_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1978_, sizeof(void*)*2 + 2);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_toApplyRulesConfig_1978_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v_toApplyRulesConfig_1978_, 0);
lean_dec(v_unused_2014_);
v___x_1992_ = v_toApplyRulesConfig_1978_;
v_isShared_1993_ = v_isSharedCheck_2013_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_toApplyConfig_1987_);
lean_dec(v_toApplyRulesConfig_1978_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2013_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_maxDepth_1994_; lean_object* v_proc_1995_; lean_object* v_suspend_1996_; lean_object* v_discharge_1997_; uint8_t v_commitIndependentGoals_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2012_; 
v_maxDepth_1994_ = lean_ctor_get(v_toBacktrackConfig_1979_, 0);
v_proc_1995_ = lean_ctor_get(v_toBacktrackConfig_1979_, 1);
v_suspend_1996_ = lean_ctor_get(v_toBacktrackConfig_1979_, 2);
v_discharge_1997_ = lean_ctor_get(v_toBacktrackConfig_1979_, 3);
v_commitIndependentGoals_1998_ = lean_ctor_get_uint8(v_toBacktrackConfig_1979_, sizeof(void*)*4);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_toBacktrackConfig_1979_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2000_ = v_toBacktrackConfig_1979_;
v_isShared_2001_ = v_isSharedCheck_2012_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_discharge_1997_);
lean_inc(v_suspend_1996_);
lean_inc(v_proc_1995_);
lean_inc(v_maxDepth_1994_);
lean_dec(v_toBacktrackConfig_1979_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2012_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___f_2002_; lean_object* v___x_2004_; 
v___f_2002_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2002_, 0, v_test_1977_);
lean_closure_set(v___f_2002_, 1, v_proc_1995_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___f_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_maxDepth_1994_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v___f_2002_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_suspend_1996_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_discharge_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2011_, sizeof(void*)*4, v_commitIndependentGoals_1998_);
v___x_2004_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2004_);
v___x_2006_ = v___x_1992_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_toApplyConfig_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2, v_transparency_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 1, v_symm_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*2 + 2, v_exfalso_1990_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2006_);
v___x_2008_ = v___x_1985_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*1, v_backtracking_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*1 + 1, v_intro_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*1 + 2, v_constructor_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2009_, sizeof(void*)*1 + 3, v_suggestions_1983_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2017_, lean_object* v_msg_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_msg_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2025_, v_msg_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
uint8_t v___x_2034_; 
v___x_2034_ = 0;
return v___x_2034_;
}
else
{
lean_object* v_head_2035_; lean_object* v_tail_2036_; uint8_t v___x_2037_; 
v_head_2035_ = lean_ctor_get(v_x_2033_, 0);
v_tail_2036_ = lean_ctor_get(v_x_2033_, 1);
v___x_2037_ = l_Lean_Expr_hasMVar(v_head_2035_);
if (v___x_2037_ == 0)
{
v_x_2033_ = v_tail_2036_;
goto _start;
}
else
{
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2039_){
_start:
{
uint8_t v_res_2040_; lean_object* v_r_2041_; 
v_res_2040_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2039_);
lean_dec(v_x_2039_);
v_r_2041_ = lean_box(v_res_2040_);
return v_r_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2042_, lean_object* v_sols_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2043_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
v___x_2050_ = lean_apply_6(v_test_2042_, v_sols_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, lean_box(0));
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec(v_sols_2043_);
lean_dec_ref(v_test_2042_);
v___x_2051_ = lean_box(v___x_2049_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2053_, lean_object* v_sols_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2053_, v_sols_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2061_, lean_object* v_test_2062_){
_start:
{
lean_object* v___f_2063_; lean_object* v___x_2064_; 
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2063_, 0, v_test_2062_);
v___x_2064_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2061_, v___f_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
uint8_t v___x_2067_; 
lean_dec_ref(v_e_2065_);
v___x_2067_ = 0;
return v___x_2067_;
}
else
{
lean_object* v_head_2068_; lean_object* v_tail_2069_; uint8_t v___x_2070_; 
v_head_2068_ = lean_ctor_get(v_x_2066_, 0);
v_tail_2069_ = lean_ctor_get(v_x_2066_, 1);
lean_inc_ref(v_e_2065_);
v___x_2070_ = l_Lean_Expr_occurs(v_e_2065_, v_head_2068_);
if (v___x_2070_ == 0)
{
v_x_2066_ = v_tail_2069_;
goto _start;
}
else
{
lean_dec_ref(v_e_2065_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2072_, lean_object* v_x_2073_){
_start:
{
uint8_t v_res_2074_; lean_object* v_r_2075_; 
v_res_2074_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2072_, v_x_2073_);
lean_dec(v_x_2073_);
v_r_2075_ = lean_box(v_res_2074_);
return v_r_2075_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2076_, lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
uint8_t v___x_2078_; 
v___x_2078_ = 1;
return v___x_2078_;
}
else
{
lean_object* v_head_2079_; lean_object* v_tail_2080_; uint8_t v___x_2081_; 
v_head_2079_ = lean_ctor_get(v_x_2077_, 0);
lean_inc(v_head_2079_);
v_tail_2080_ = lean_ctor_get(v_x_2077_, 1);
lean_inc(v_tail_2080_);
lean_dec_ref_known(v_x_2077_, 2);
v___x_2081_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2079_, v_sols_2076_);
if (v___x_2081_ == 0)
{
lean_dec(v_tail_2080_);
return v___x_2081_;
}
else
{
v_x_2077_ = v_tail_2080_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2083_, lean_object* v_x_2084_){
_start:
{
uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_res_2085_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2083_, v_x_2084_);
lean_dec(v_sols_2083_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2087_, lean_object* v_sols_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2088_, v_use_2087_);
v___x_2095_ = lean_box(v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2097_, lean_object* v_sols_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2097_, v_sols_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v_sols_2098_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2105_, lean_object* v_use_2106_){
_start:
{
lean_object* v___f_2107_; lean_object* v___x_2108_; 
v___f_2107_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2107_, 0, v_use_2106_);
v___x_2108_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2105_, v___f_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2109_){
_start:
{
lean_object* v___y_2111_; lean_object* v_toApplyRulesConfig_2112_; uint8_t v_backtracking_2113_; uint8_t v_intro_2114_; uint8_t v_constructor_2115_; uint8_t v_suggestions_2116_; uint8_t v_intro_2120_; 
v_intro_2120_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1 + 1);
if (v_intro_2120_ == 0)
{
lean_object* v_toApplyRulesConfig_2121_; uint8_t v_backtracking_2122_; uint8_t v_constructor_2123_; uint8_t v_suggestions_2124_; 
v_toApplyRulesConfig_2121_ = lean_ctor_get(v_cfg_2109_, 0);
lean_inc_ref(v_toApplyRulesConfig_2121_);
v_backtracking_2122_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1);
v_constructor_2123_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1 + 2);
v_suggestions_2124_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1 + 3);
v___y_2111_ = v_cfg_2109_;
v_toApplyRulesConfig_2112_ = v_toApplyRulesConfig_2121_;
v_backtracking_2113_ = v_backtracking_2122_;
v_intro_2114_ = v_intro_2120_;
v_constructor_2115_ = v_constructor_2123_;
v_suggestions_2116_ = v_suggestions_2124_;
goto v___jp_2110_;
}
else
{
lean_object* v_toApplyRulesConfig_2125_; uint8_t v_backtracking_2126_; uint8_t v_constructor_2127_; uint8_t v_suggestions_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2142_; 
v_toApplyRulesConfig_2125_ = lean_ctor_get(v_cfg_2109_, 0);
v_backtracking_2126_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1);
v_constructor_2127_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1 + 2);
v_suggestions_2128_ = lean_ctor_get_uint8(v_cfg_2109_, sizeof(void*)*1 + 3);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_cfg_2109_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2130_ = v_cfg_2109_;
v_isShared_2131_ = v_isSharedCheck_2142_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_toApplyRulesConfig_2125_);
lean_dec(v_cfg_2109_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2142_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
uint8_t v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = 0;
if (v_isShared_2131_ == 0)
{
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_toApplyRulesConfig_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2141_, sizeof(void*)*1, v_backtracking_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2141_, sizeof(void*)*1 + 2, v_constructor_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2141_, sizeof(void*)*1 + 3, v_suggestions_2128_);
v___x_2134_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v_toApplyRulesConfig_2136_; uint8_t v_backtracking_2137_; uint8_t v_intro_2138_; uint8_t v_constructor_2139_; uint8_t v_suggestions_2140_; 
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 1, v___x_2132_);
v___x_2135_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2134_);
v_toApplyRulesConfig_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc_ref(v_toApplyRulesConfig_2136_);
v_backtracking_2137_ = lean_ctor_get_uint8(v___x_2135_, sizeof(void*)*1);
v_intro_2138_ = lean_ctor_get_uint8(v___x_2135_, sizeof(void*)*1 + 1);
v_constructor_2139_ = lean_ctor_get_uint8(v___x_2135_, sizeof(void*)*1 + 2);
v_suggestions_2140_ = lean_ctor_get_uint8(v___x_2135_, sizeof(void*)*1 + 3);
v___y_2111_ = v___x_2135_;
v_toApplyRulesConfig_2112_ = v_toApplyRulesConfig_2136_;
v_backtracking_2113_ = v_backtracking_2137_;
v_intro_2114_ = v_intro_2138_;
v_constructor_2115_ = v_constructor_2139_;
v_suggestions_2116_ = v_suggestions_2140_;
goto v___jp_2110_;
}
}
}
v___jp_2110_:
{
if (v_constructor_2115_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2112_);
return v___y_2111_;
}
else
{
uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v___y_2111_);
v___x_2117_ = 0;
v___x_2118_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2118_, 0, v_toApplyRulesConfig_2112_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1, v_backtracking_2113_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1 + 1, v_intro_2114_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1 + 2, v___x_2117_);
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1 + 3, v_suggestions_2116_);
v___x_2119_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2118_);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2143_, lean_object* v_x_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
if (lean_obj_tag(v_x_2143_) == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = l_List_reverse___redArg(v_x_2144_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
else
{
lean_object* v_head_2154_; lean_object* v_tail_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2173_; 
v_head_2154_ = lean_ctor_get(v_x_2143_, 0);
v_tail_2155_ = lean_ctor_get(v_x_2143_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_x_2143_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2157_ = v_x_2143_;
v_isShared_2158_ = v_isSharedCheck_2173_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_tail_2155_);
lean_inc(v_head_2154_);
lean_dec(v_x_2143_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2173_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; 
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
v___x_2159_ = lean_apply_7(v_head_2154_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, lean_box(0));
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v_x_2144_);
lean_ctor_set(v___x_2157_, 0, v_a_2160_);
v___x_2162_ = v___x_2157_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_x_2144_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_x_2143_ = v_tail_2155_;
v_x_2144_ = v___x_2162_;
goto _start;
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_del_object(v___x_2157_);
lean_dec(v_tail_2155_);
lean_dec(v_x_2144_);
v_a_2165_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2159_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2159_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2174_, v_x_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2184_, lean_object* v_cfg_2185_, lean_object* v_lemmas_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
v___x_2194_ = lean_apply_8(v_ctx_2184_, v_cfg_2185_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = lean_box(0);
v___x_2197_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2186_, v___x_2196_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
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
lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2202_ = l_List_appendTR___redArg(v_a_2195_, v_a_2198_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2202_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
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
lean_dec(v_a_2195_);
return v___x_2197_;
}
}
else
{
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v_lemmas_2186_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2207_, lean_object* v_cfg_2208_, lean_object* v_lemmas_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2207_, v_cfg_2208_, v_lemmas_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2218_){
_start:
{
uint8_t v___x_2219_; 
v___x_2219_ = 0;
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2220_){
_start:
{
uint8_t v_res_2221_; lean_object* v_r_2222_; 
v_res_2221_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2220_);
lean_dec(v_x_2220_);
v_r_2222_ = lean_box(v_res_2221_);
return v_r_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2223_, lean_object* v___x_2224_, lean_object* v___x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2223_, v___x_2224_, v___x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2240_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2240_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2240_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_fst_2236_; lean_object* v___x_2238_; 
v_fst_2236_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_fst_2236_);
lean_dec(v_a_2232_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_fst_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_fst_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2231_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2231_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2249_, lean_object* v___x_2250_, lean_object* v___x_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2249_, v___x_2250_, v___x_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2272_, lean_object* v_g_2273_, lean_object* v_lemmas_2274_, lean_object* v_ctx_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; 
v___f_2281_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2281_, 0, v_ctx_2275_);
lean_closure_set(v___f_2281_, 1, v_cfg_2272_);
lean_closure_set(v___f_2281_, 2, v_lemmas_2274_);
v___x_2282_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2283_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2284_, 0, v___f_2281_);
lean_closure_set(v___f_2284_, 1, v___x_2282_);
lean_closure_set(v___f_2284_, 2, v___x_2283_);
v___x_2285_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2273_, v___f_2284_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2286_, lean_object* v_g_2287_, lean_object* v_lemmas_2288_, lean_object* v_ctx_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2286_, v_g_2287_, v_lemmas_2288_, v_ctx_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2296_, lean_object* v_lemmas_2297_, lean_object* v_ctx_2298_, lean_object* v_g_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; 
lean_inc(v_g_2299_);
lean_inc_ref(v_cfg_2296_);
v___x_2305_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2296_, v_g_2299_, v_lemmas_2297_, v_ctx_2298_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_toApplyRulesConfig_2306_; lean_object* v_a_2307_; lean_object* v_toApplyConfig_2308_; uint8_t v_transparency_2309_; lean_object* v___x_2310_; 
v_toApplyRulesConfig_2306_ = lean_ctor_get(v_cfg_2296_, 0);
lean_inc_ref(v_toApplyRulesConfig_2306_);
lean_dec_ref(v_cfg_2296_);
v_a_2307_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2305_, 1);
v_toApplyConfig_2308_ = lean_ctor_get(v_toApplyRulesConfig_2306_, 1);
lean_inc_ref(v_toApplyConfig_2308_);
v_transparency_2309_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2306_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2306_);
v___x_2310_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2308_, v_transparency_2309_, v_a_2307_, v_g_2299_, v_a_2301_, v_a_2303_);
return v___x_2310_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_g_2299_);
lean_dec_ref(v_cfg_2296_);
v_a_2311_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2305_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2305_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2319_, lean_object* v_lemmas_2320_, lean_object* v_ctx_2321_, lean_object* v_g_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2319_, v_lemmas_2320_, v_ctx_2321_, v_g_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2329_, lean_object* v_lemmas_2330_, lean_object* v_ctx_2331_, lean_object* v_g_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; 
lean_inc(v_g_2332_);
lean_inc_ref(v_cfg_2329_);
v___x_2338_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2329_, v_g_2332_, v_lemmas_2330_, v_ctx_2331_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_toApplyRulesConfig_2339_; lean_object* v_a_2340_; lean_object* v_toApplyConfig_2341_; uint8_t v_transparency_2342_; lean_object* v___x_2343_; 
v_toApplyRulesConfig_2339_ = lean_ctor_get(v_cfg_2329_, 0);
lean_inc_ref(v_toApplyRulesConfig_2339_);
lean_dec_ref(v_cfg_2329_);
v_a_2340_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2338_, 1);
v_toApplyConfig_2341_ = lean_ctor_get(v_toApplyRulesConfig_2339_, 1);
lean_inc_ref(v_toApplyConfig_2341_);
v_transparency_2342_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2339_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2339_);
v___x_2343_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2341_, v_transparency_2342_, v_a_2340_, v_g_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
return v___x_2343_;
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_g_2332_);
lean_dec_ref(v_cfg_2329_);
v_a_2344_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2338_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2338_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2352_, lean_object* v_lemmas_2353_, lean_object* v_ctx_2354_, lean_object* v_g_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2352_, v_lemmas_2353_, v_ctx_2354_, v_g_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2362_, lean_object* v_i_2363_, lean_object* v_k_2364_){
_start:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = lean_array_get_size(v_keys_2362_);
v___x_2366_ = lean_nat_dec_lt(v_i_2363_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_dec(v_i_2363_);
return v___x_2366_;
}
else
{
lean_object* v_k_x27_2367_; uint8_t v___x_2368_; 
v_k_x27_2367_ = lean_array_fget_borrowed(v_keys_2362_, v_i_2363_);
v___x_2368_ = l_Lean_instBEqMVarId_beq(v_k_2364_, v_k_x27_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_i_2363_, v___x_2369_);
lean_dec(v_i_2363_);
v_i_2363_ = v___x_2370_;
goto _start;
}
else
{
lean_dec(v_i_2363_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2372_, lean_object* v_i_2373_, lean_object* v_k_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2372_, v_i_2373_, v_k_2374_);
lean_dec(v_k_2374_);
lean_dec_ref(v_keys_2372_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2377_, size_t v_x_2378_, lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_object* v_es_2380_; lean_object* v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; lean_object* v_j_2384_; lean_object* v___x_2385_; 
v_es_2380_ = lean_ctor_get(v_x_2377_, 0);
v___x_2381_ = lean_box(2);
v___x_2382_ = ((size_t)31ULL);
v___x_2383_ = lean_usize_land(v_x_2378_, v___x_2382_);
v_j_2384_ = lean_usize_to_nat(v___x_2383_);
v___x_2385_ = lean_array_get_borrowed(v___x_2381_, v_es_2380_, v_j_2384_);
lean_dec(v_j_2384_);
switch(lean_obj_tag(v___x_2385_))
{
case 0:
{
lean_object* v_key_2386_; uint8_t v___x_2387_; 
v_key_2386_ = lean_ctor_get(v___x_2385_, 0);
v___x_2387_ = l_Lean_instBEqMVarId_beq(v_x_2379_, v_key_2386_);
return v___x_2387_;
}
case 1:
{
lean_object* v_node_2388_; size_t v___x_2389_; size_t v___x_2390_; 
v_node_2388_ = lean_ctor_get(v___x_2385_, 0);
v___x_2389_ = ((size_t)5ULL);
v___x_2390_ = lean_usize_shift_right(v_x_2378_, v___x_2389_);
v_x_2377_ = v_node_2388_;
v_x_2378_ = v___x_2390_;
goto _start;
}
default: 
{
uint8_t v___x_2392_; 
v___x_2392_ = 0;
return v___x_2392_;
}
}
}
else
{
lean_object* v_ks_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_ks_2393_ = lean_ctor_get(v_x_2377_, 0);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2393_, v___x_2394_, v_x_2379_);
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
size_t v_x_1988__boxed_2399_; uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_x_1988__boxed_2399_ = lean_unbox_usize(v_x_2397_);
lean_dec(v_x_2397_);
v_res_2400_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2396_, v_x_1988__boxed_2399_, v_x_2398_);
lean_dec(v_x_2398_);
lean_dec_ref(v_x_2396_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
uint64_t v___x_2404_; size_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = l_Lean_instHashableMVarId_hash(v_x_2403_);
v___x_2405_ = lean_uint64_to_usize(v___x_2404_);
v___x_2406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2402_, v___x_2405_, v_x_2403_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2407_, v_x_2408_);
lean_dec(v_x_2408_);
lean_dec_ref(v_x_2407_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v_mctx_2415_; lean_object* v_eAssignment_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2414_ = lean_st_ref_get(v___y_2412_);
v_mctx_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_mctx_2415_);
lean_dec(v___x_2414_);
v_eAssignment_2416_ = lean_ctor_get(v_mctx_2415_, 8);
lean_inc_ref(v_eAssignment_2416_);
lean_dec_ref(v_mctx_2415_);
v___x_2417_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2416_, v_mvarId_2411_);
lean_dec_ref(v_eAssignment_2416_);
v___x_2418_ = lean_box(v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec(v_mvarId_2420_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
if (lean_obj_tag(v_x_2425_) == 0)
{
return v_x_2424_;
}
else
{
lean_object* v_head_2426_; lean_object* v_tail_2427_; lean_object* v___x_2428_; 
v_head_2426_ = lean_ctor_get(v_x_2425_, 0);
lean_inc(v_head_2426_);
v_tail_2427_ = lean_ctor_get(v_x_2425_, 1);
lean_inc(v_tail_2427_);
lean_dec_ref_known(v_x_2425_, 2);
v___x_2428_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2424_, v_head_2426_);
v_x_2424_ = v___x_2428_;
v_x_2425_ = v_tail_2427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2430_, lean_object* v_a_2431_, uint8_t v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
if (lean_obj_tag(v_a_2433_) == 0)
{
if (lean_obj_tag(v_a_2434_) == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec(v_a_2431_);
lean_dec_ref(v_f_2430_);
v___x_2441_ = lean_box(v_a_2432_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_a_2435_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
else
{
lean_object* v_head_2444_; lean_object* v_tail_2445_; 
v_head_2444_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_head_2444_);
v_tail_2445_ = lean_ctor_get(v_a_2434_, 1);
lean_inc(v_tail_2445_);
lean_dec_ref_known(v_a_2434_, 2);
v_a_2433_ = v_head_2444_;
v_a_2434_ = v_tail_2445_;
goto _start;
}
}
else
{
lean_object* v_head_2447_; lean_object* v_tail_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2491_; 
v_head_2447_ = lean_ctor_get(v_a_2433_, 0);
v_tail_2448_ = lean_ctor_get(v_a_2433_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_a_2433_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2450_ = v_a_2433_;
v_isShared_2451_ = v_isSharedCheck_2491_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_tail_2448_);
lean_inc(v_head_2447_);
lean_dec(v_a_2433_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2491_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2490_; 
v___x_2452_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2447_, v___y_2437_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2490_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2490_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
uint8_t v___x_2457_; 
v___x_2457_ = lean_unbox(v_a_2453_);
lean_dec(v_a_2453_);
if (v___x_2457_ == 0)
{
lean_object* v_zero_2458_; uint8_t v_isZero_2459_; 
v_zero_2458_ = lean_unsigned_to_nat(0u);
v_isZero_2459_ = lean_nat_dec_eq(v_a_2431_, v_zero_2458_);
if (v_isZero_2459_ == 1)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_del_object(v___x_2450_);
lean_dec(v_a_2431_);
lean_dec_ref(v_f_2430_);
v___x_2460_ = lean_array_push(v_a_2435_, v_head_2447_);
v___x_2461_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2460_, v_tail_2448_);
v___x_2462_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2461_, v_a_2434_);
v___x_2463_ = lean_box(v_a_2432_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2464_);
v___x_2466_ = v___x_2455_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
else
{
lean_object* v_one_2468_; lean_object* v_n_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_del_object(v___x_2455_);
v_one_2468_ = lean_unsigned_to_nat(1u);
v_n_2469_ = lean_nat_sub(v_a_2431_, v_one_2468_);
lean_dec(v_a_2431_);
v___x_2470_ = 1;
lean_inc_ref(v_f_2430_);
lean_inc(v_head_2447_);
v___x_2471_ = lean_apply_1(v_f_2430_, v_head_2447_);
v___x_2472_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2471_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
if (lean_obj_tag(v_a_2473_) == 0)
{
lean_object* v___x_2474_; 
lean_del_object(v___x_2450_);
v___x_2474_ = lean_array_push(v_a_2435_, v_head_2447_);
v_a_2431_ = v_n_2469_;
v_a_2433_ = v_tail_2448_;
v_a_2435_ = v___x_2474_;
goto _start;
}
else
{
lean_object* v_val_2476_; lean_object* v___x_2478_; 
lean_dec(v_head_2447_);
v_val_2476_ = lean_ctor_get(v_a_2473_, 0);
lean_inc(v_val_2476_);
lean_dec_ref_known(v_a_2473_, 1);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v_a_2434_);
lean_ctor_set(v___x_2450_, 0, v_tail_2448_);
v___x_2478_ = v___x_2450_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_tail_2448_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_a_2434_);
v___x_2478_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
v_a_2431_ = v_n_2469_;
v_a_2432_ = v___x_2470_;
v_a_2433_ = v_val_2476_;
v_a_2434_ = v___x_2478_;
goto _start;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_n_2469_);
lean_del_object(v___x_2450_);
lean_dec(v_tail_2448_);
lean_dec(v_head_2447_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_f_2430_);
v_a_2481_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2472_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2472_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
else
{
lean_del_object(v___x_2455_);
lean_del_object(v___x_2450_);
lean_dec(v_head_2447_);
v_a_2433_ = v_tail_2448_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v_a_2067__boxed_2503_; lean_object* v_res_2504_; 
v_a_2067__boxed_2503_ = lean_unbox(v_a_2494_);
v_res_2504_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2492_, v_a_2493_, v_a_2067__boxed_2503_, v_a_2495_, v_a_2496_, v_a_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2505_, size_t v_i_2506_, size_t v_stop_2507_, lean_object* v_b_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_a_2515_; uint8_t v___x_2519_; 
v___x_2519_ = lean_usize_dec_eq(v_i_2506_, v_stop_2507_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2523_; 
v___x_2520_ = lean_array_uget_borrowed(v_as_2505_, v_i_2506_);
v___x_2523_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2520_, v___y_2510_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; uint8_t v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = lean_unbox(v_a_2524_);
lean_dec(v_a_2524_);
if (v___x_2525_ == 0)
{
goto v___jp_2521_;
}
else
{
v_a_2515_ = v_b_2508_;
goto v___jp_2514_;
}
}
else
{
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2527_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
if (v___x_2527_ == 0)
{
v_a_2515_ = v_b_2508_;
goto v___jp_2514_;
}
else
{
goto v___jp_2521_;
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v_b_2508_);
v_a_2528_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2523_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2523_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
v___jp_2521_:
{
lean_object* v___x_2522_; 
lean_inc(v___x_2520_);
v___x_2522_ = lean_array_push(v_b_2508_, v___x_2520_);
v_a_2515_ = v___x_2522_;
goto v___jp_2514_;
}
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_b_2508_);
return v___x_2536_;
}
v___jp_2514_:
{
size_t v___x_2516_; size_t v___x_2517_; 
v___x_2516_ = ((size_t)1ULL);
v___x_2517_ = lean_usize_add(v_i_2506_, v___x_2516_);
v_i_2506_ = v___x_2517_;
v_b_2508_ = v_a_2515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2537_, lean_object* v_i_2538_, lean_object* v_stop_2539_, lean_object* v_b_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
size_t v_i_boxed_2546_; size_t v_stop_boxed_2547_; lean_object* v_res_2548_; 
v_i_boxed_2546_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_stop_boxed_2547_ = lean_unbox_usize(v_stop_2539_);
lean_dec(v_stop_2539_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2537_, v_i_boxed_2546_, v_stop_boxed_2547_, v_b_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec_ref(v_as_2537_);
return v_res_2548_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2552_ = lean_array_to_list(v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2553_, lean_object* v_goals_2554_, lean_object* v_maxIters_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2561_ = 0;
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_unsigned_to_nat(0u);
v___x_2564_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2565_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2553_, v_maxIters_2555_, v___x_2561_, v_goals_2554_, v___x_2562_, v___x_2564_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2608_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2608_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2608_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2607_; 
v_fst_2570_ = lean_ctor_get(v_a_2566_, 0);
v_snd_2571_ = lean_ctor_get(v_a_2566_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_a_2566_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2573_ = v_a_2566_;
v_isShared_2574_ = v_isSharedCheck_2607_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_inc(v_fst_2570_);
lean_dec(v_a_2566_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2607_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = lean_array_get_size(v_snd_2571_);
v___x_2576_ = lean_nat_dec_lt(v___x_2563_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_snd_2571_);
v___x_2577_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 1, v___x_2577_);
v___x_2579_ = v___x_2573_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_fst_2570_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2579_);
v___x_2581_ = v___x_2568_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2568_);
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2575_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2571_, v___x_2584_, v___x_2585_, v___x_2564_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v_snd_2571_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2598_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_array_to_list(v_a_2587_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 1, v___x_2591_);
v___x_2593_ = v___x_2573_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_fst_2570_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2595_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2593_);
v___x_2595_ = v___x_2589_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_del_object(v___x_2573_);
lean_dec(v_fst_2570_);
v_a_2599_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2586_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2586_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2565_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2565_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2617_, lean_object* v_goals_2618_, lean_object* v_maxIters_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2617_, v_goals_2618_, v_maxIters_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2625_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2629_, lean_object* v_goals_2630_, lean_object* v_maxIters_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2629_, v_goals_2630_, v_maxIters_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2650_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2650_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2650_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v_fst_2642_; uint8_t v___x_2643_; 
v_fst_2642_ = lean_ctor_get(v_a_2638_, 0);
v___x_2643_ = lean_unbox(v_fst_2642_);
if (v___x_2643_ == 1)
{
lean_object* v_snd_2644_; lean_object* v___x_2646_; 
v_snd_2644_ = lean_ctor_get(v_a_2638_, 1);
lean_inc(v_snd_2644_);
lean_dec(v_a_2638_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v_snd_2644_);
v___x_2646_ = v___x_2640_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_snd_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_del_object(v___x_2640_);
lean_dec(v_a_2638_);
v___x_2648_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2649_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2648_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2649_;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_a_2651_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2637_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2637_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2659_, lean_object* v_goals_2660_, lean_object* v_maxIters_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2659_, v_goals_2660_, v_maxIters_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2668_, lean_object* v_ctx_2669_, lean_object* v_cfg_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
uint8_t v_backtracking_2677_; 
v_backtracking_2677_ = lean_ctor_get_uint8(v_cfg_2670_, sizeof(void*)*1);
if (v_backtracking_2677_ == 0)
{
lean_object* v_toApplyRulesConfig_2678_; lean_object* v_toBacktrackConfig_2679_; lean_object* v_maxDepth_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_toApplyRulesConfig_2678_ = lean_ctor_get(v_cfg_2670_, 0);
v_toBacktrackConfig_2679_ = lean_ctor_get(v_toApplyRulesConfig_2678_, 0);
v_maxDepth_2680_ = lean_ctor_get(v_toBacktrackConfig_2679_, 0);
lean_inc(v_maxDepth_2680_);
v___x_2681_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2681_, 0, v_cfg_2670_);
lean_closure_set(v___x_2681_, 1, v_lemmas_2668_);
lean_closure_set(v___x_2681_, 2, v_ctx_2669_);
v___x_2682_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2681_, v_a_2671_, v_maxDepth_2680_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2682_;
}
else
{
lean_object* v_toApplyRulesConfig_2683_; lean_object* v_toBacktrackConfig_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_toApplyRulesConfig_2683_ = lean_ctor_get(v_cfg_2670_, 0);
v_toBacktrackConfig_2684_ = lean_ctor_get(v_toApplyRulesConfig_2683_, 0);
lean_inc_ref(v_toBacktrackConfig_2684_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2686_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2686_, 0, v_cfg_2670_);
lean_closure_set(v___x_2686_, 1, v_lemmas_2668_);
lean_closure_set(v___x_2686_, 2, v_ctx_2669_);
v___x_2687_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2684_, v___x_2685_, v___x_2686_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2688_, lean_object* v_ctx_2689_, lean_object* v_cfg_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2688_, v_ctx_2689_, v_cfg_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2698_, v___y_2700_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v_mvarId_2705_);
return v_res_2711_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2713_, v_x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2716_, lean_object* v_x_2717_, lean_object* v_x_2718_){
_start:
{
uint8_t v_res_2719_; lean_object* v_r_2720_; 
v_res_2719_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2716_, v_x_2717_, v_x_2718_);
lean_dec(v_x_2718_);
lean_dec_ref(v_x_2717_);
v_r_2720_ = lean_box(v_res_2719_);
return v_r_2720_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2721_, lean_object* v_x_2722_, size_t v_x_2723_, lean_object* v_x_2724_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2722_, v_x_2723_, v_x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_){
_start:
{
size_t v_x_2513__boxed_2730_; uint8_t v_res_2731_; lean_object* v_r_2732_; 
v_x_2513__boxed_2730_ = lean_unbox_usize(v_x_2728_);
lean_dec(v_x_2728_);
v_res_2731_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2726_, v_x_2727_, v_x_2513__boxed_2730_, v_x_2729_);
lean_dec(v_x_2729_);
lean_dec_ref(v_x_2727_);
v_r_2732_ = lean_box(v_res_2731_);
return v_r_2732_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2733_, lean_object* v_keys_2734_, lean_object* v_vals_2735_, lean_object* v_heq_2736_, lean_object* v_i_2737_, lean_object* v_k_2738_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2734_, v_i_2737_, v_k_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2740_, lean_object* v_keys_2741_, lean_object* v_vals_2742_, lean_object* v_heq_2743_, lean_object* v_i_2744_, lean_object* v_k_2745_){
_start:
{
uint8_t v_res_2746_; lean_object* v_r_2747_; 
v_res_2746_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2740_, v_keys_2741_, v_vals_2742_, v_heq_2743_, v_i_2744_, v_k_2745_);
lean_dec(v_k_2745_);
lean_dec_ref(v_vals_2742_);
lean_dec_ref(v_keys_2741_);
v_r_2747_ = lean_box(v_res_2746_);
return v_r_2747_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_x_2759_);
return v_res_2765_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2768_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2769_ = l_Lean_Name_append(v___x_2768_, v___x_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2770_, lean_object* v_lemmas_2771_, lean_object* v_ctx_2772_, lean_object* v_goals_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v___f_2779_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; lean_object* v___y_2787_; lean_object* v_a_2788_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; uint8_t v___y_2804_; lean_object* v_a_2805_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; uint8_t v___y_2813_; lean_object* v___y_2814_; lean_object* v_a_2815_; uint8_t v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; uint8_t v___y_2834_; lean_object* v_a_2835_; lean_object* v_cfg_2837_; lean_object* v___x_2838_; 
v___f_2779_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v_cfg_2837_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2770_);
lean_inc(v_goals_2773_);
lean_inc_ref(v_cfg_2837_);
lean_inc_ref(v_ctx_2772_);
lean_inc(v_lemmas_2771_);
v___x_2838_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2771_, v_ctx_2772_, v_cfg_2837_, v_goals_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_dec_ref(v_cfg_2837_);
lean_dec(v_goals_2773_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
return v___x_2838_;
}
else
{
lean_object* v_a_2839_; uint8_t v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; uint8_t v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; uint8_t v___y_2883_; uint8_t v___x_2937_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v___x_2937_ = l_Lean_Exception_isInterrupt(v_a_2839_);
if (v___x_2937_ == 0)
{
uint8_t v___x_2938_; 
lean_inc(v_a_2839_);
v___x_2938_ = l_Lean_Exception_isRuntime(v_a_2839_);
v___y_2883_ = v___x_2938_;
goto v___jp_2882_;
}
else
{
v___y_2883_ = v___x_2937_;
goto v___jp_2882_;
}
v___jp_2840_:
{
lean_object* v___x_2848_; lean_object* v_a_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2848_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2777_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v___x_2848_);
v___x_2850_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2851_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2846_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_io_mono_nanos_now();
v___x_2853_ = l_Lean_MVarId_exfalso(v___y_2844_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_a_2854_);
lean_ctor_set(v___x_2855_, 1, v___y_2847_);
v___x_2856_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2771_, v_ctx_2772_, v_cfg_2837_, v___x_2855_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 1);
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
v___y_2808_ = v_a_2849_;
v___y_2809_ = v___y_2842_;
v___y_2810_ = v___y_2841_;
v___y_2811_ = v___y_2843_;
v___y_2812_ = v___x_2852_;
v___y_2813_ = v___y_2845_;
v___y_2814_ = v___y_2846_;
v_a_2815_ = v___x_2862_;
goto v___jp_2807_;
}
}
}
else
{
lean_object* v_a_2865_; 
v_a_2865_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2856_, 1);
v___y_2828_ = v___y_2841_;
v___y_2829_ = v___y_2842_;
v___y_2830_ = v_a_2849_;
v___y_2831_ = v___y_2843_;
v___y_2832_ = v___x_2852_;
v___y_2833_ = v___y_2846_;
v___y_2834_ = v___y_2845_;
v_a_2835_ = v_a_2865_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2866_; 
lean_dec(v___y_2847_);
lean_dec_ref(v_cfg_2837_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
v_a_2866_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2853_, 1);
v___y_2828_ = v___y_2841_;
v___y_2829_ = v___y_2842_;
v___y_2830_ = v_a_2849_;
v___y_2831_ = v___y_2843_;
v___y_2832_ = v___x_2852_;
v___y_2833_ = v___y_2846_;
v___y_2834_ = v___y_2845_;
v_a_2835_ = v_a_2866_;
goto v___jp_2827_;
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_io_get_num_heartbeats();
v___x_2868_ = l_Lean_MVarId_exfalso(v___y_2844_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_a_2869_);
lean_ctor_set(v___x_2870_, 1, v___y_2847_);
v___x_2871_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2771_, v_ctx_2772_, v_cfg_2837_, v___x_2870_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set_tag(v___x_2874_, 1);
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
v___y_2781_ = v___x_2867_;
v___y_2782_ = v_a_2849_;
v___y_2783_ = v___y_2842_;
v___y_2784_ = v___y_2841_;
v___y_2785_ = v___y_2843_;
v___y_2786_ = v___y_2845_;
v___y_2787_ = v___y_2846_;
v_a_2788_ = v___x_2877_;
goto v___jp_2780_;
}
}
}
else
{
lean_object* v_a_2880_; 
v_a_2880_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2871_, 1);
v___y_2798_ = v___x_2867_;
v___y_2799_ = v___y_2841_;
v___y_2800_ = v___y_2842_;
v___y_2801_ = v_a_2849_;
v___y_2802_ = v___y_2843_;
v___y_2803_ = v___y_2846_;
v___y_2804_ = v___y_2845_;
v_a_2805_ = v_a_2880_;
goto v___jp_2797_;
}
}
else
{
lean_object* v_a_2881_; 
lean_dec(v___y_2847_);
lean_dec_ref(v_cfg_2837_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
v_a_2881_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2868_, 1);
v___y_2798_ = v___x_2867_;
v___y_2799_ = v___y_2841_;
v___y_2800_ = v___y_2842_;
v___y_2801_ = v_a_2849_;
v___y_2802_ = v___y_2843_;
v___y_2803_ = v___y_2846_;
v___y_2804_ = v___y_2845_;
v_a_2805_ = v_a_2881_;
goto v___jp_2797_;
}
}
}
v___jp_2882_:
{
if (v___y_2883_ == 0)
{
if (lean_obj_tag(v_goals_2773_) == 1)
{
lean_object* v_tail_2884_; 
v_tail_2884_ = lean_ctor_get(v_goals_2773_, 1);
lean_inc(v_tail_2884_);
if (lean_obj_tag(v_tail_2884_) == 0)
{
lean_object* v_toApplyRulesConfig_2885_; uint8_t v_exfalso_2886_; 
v_toApplyRulesConfig_2885_ = lean_ctor_get(v_cfg_2837_, 0);
v_exfalso_2886_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2885_, sizeof(void*)*2 + 2);
if (v_exfalso_2886_ == 1)
{
lean_object* v_toCold_2887_; lean_object* v_options_2888_; uint8_t v_hasTrace_2889_; 
lean_dec_ref_known(v___x_2838_, 1);
v_toCold_2887_ = lean_ctor_get(v_a_2776_, 0);
v_options_2888_ = lean_ctor_get(v_toCold_2887_, 2);
v_hasTrace_2889_ = lean_ctor_get_uint8(v_options_2888_, sizeof(void*)*1);
if (v_hasTrace_2889_ == 0)
{
lean_object* v_head_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2908_; 
v_head_2890_ = lean_ctor_get(v_goals_2773_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_goals_2773_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v_goals_2773_, 1);
lean_dec(v_unused_2909_);
v___x_2892_ = v_goals_2773_;
v_isShared_2893_ = v_isSharedCheck_2908_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_head_2890_);
lean_dec(v_goals_2773_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2908_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_MVarId_exfalso(v_head_2890_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_a_2895_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2895_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_tail_2884_);
v___x_2897_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2771_, v_ctx_2772_, v_cfg_2837_, v___x_2897_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
return v___x_2898_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_del_object(v___x_2892_);
lean_dec_ref(v_cfg_2837_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
v_a_2900_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2894_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2894_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_object* v_head_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2935_; 
v_head_2910_ = lean_ctor_get(v_goals_2773_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_goals_2773_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; 
v_unused_2936_ = lean_ctor_get(v_goals_2773_, 1);
lean_dec(v_unused_2936_);
v___x_2912_ = v_goals_2773_;
v_isShared_2913_ = v_isSharedCheck_2935_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_head_2910_);
lean_dec(v_goals_2773_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2935_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v_inheritedTraceOptions_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_inheritedTraceOptions_2914_ = lean_ctor_get(v_toCold_2887_, 11);
v___x_2915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2916_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2917_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2914_, v_options_2888_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = l_Lean_trace_profiler;
v___x_2920_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2888_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_MVarId_exfalso(v_head_2910_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2924_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v_a_2922_);
v___x_2924_ = v___x_2912_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2922_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_tail_2884_);
v___x_2924_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2771_, v_ctx_2772_, v_cfg_2837_, v___x_2924_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
return v___x_2925_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_del_object(v___x_2912_);
lean_dec_ref(v_cfg_2837_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
v_a_2927_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2921_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2921_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_del_object(v___x_2912_);
v___y_2841_ = v_exfalso_2886_;
v___y_2842_ = v___x_2916_;
v___y_2843_ = v___x_2915_;
v___y_2844_ = v_head_2910_;
v___y_2845_ = v___x_2918_;
v___y_2846_ = v_options_2888_;
v___y_2847_ = v_tail_2884_;
goto v___jp_2840_;
}
}
else
{
lean_del_object(v___x_2912_);
v___y_2841_ = v_exfalso_2886_;
v___y_2842_ = v___x_2916_;
v___y_2843_ = v___x_2915_;
v___y_2844_ = v_head_2910_;
v___y_2845_ = v___x_2918_;
v___y_2846_ = v_options_2888_;
v___y_2847_ = v_tail_2884_;
goto v___jp_2840_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2773_, 2);
lean_dec_ref(v_cfg_2837_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
return v___x_2838_;
}
}
else
{
lean_dec(v_tail_2884_);
lean_dec_ref_known(v_goals_2773_, 2);
lean_dec_ref(v_cfg_2837_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
return v___x_2838_;
}
}
else
{
lean_dec_ref(v_cfg_2837_);
lean_dec(v_goals_2773_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
return v___x_2838_;
}
}
else
{
lean_dec_ref(v_cfg_2837_);
lean_dec(v_goals_2773_);
lean_dec_ref(v_ctx_2772_);
lean_dec(v_lemmas_2771_);
return v___x_2838_;
}
}
}
v___jp_2780_:
{
lean_object* v___x_2789_; double v___x_2790_; double v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2789_ = lean_io_get_num_heartbeats();
v___x_2790_ = lean_float_of_nat(v___y_2781_);
v___x_2791_ = lean_float_of_nat(v___x_2789_);
v___x_2792_ = lean_box_float(v___x_2790_);
v___x_2793_ = lean_box_float(v___x_2791_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_a_2788_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2785_);
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2785_, v___y_2784_, v___y_2783_, v___y_2787_, v___y_2786_, v___y_2782_, v___f_2779_, v___x_2795_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
return v___x_2796_;
}
v___jp_2797_:
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_a_2805_);
v___y_2781_ = v___y_2798_;
v___y_2782_ = v___y_2801_;
v___y_2783_ = v___y_2800_;
v___y_2784_ = v___y_2799_;
v___y_2785_ = v___y_2802_;
v___y_2786_ = v___y_2804_;
v___y_2787_ = v___y_2803_;
v_a_2788_ = v___x_2806_;
goto v___jp_2780_;
}
v___jp_2807_:
{
lean_object* v___x_2816_; double v___x_2817_; double v___x_2818_; double v___x_2819_; double v___x_2820_; double v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2816_ = lean_io_mono_nanos_now();
v___x_2817_ = lean_float_of_nat(v___y_2812_);
v___x_2818_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2819_ = lean_float_div(v___x_2817_, v___x_2818_);
v___x_2820_ = lean_float_of_nat(v___x_2816_);
v___x_2821_ = lean_float_div(v___x_2820_, v___x_2818_);
v___x_2822_ = lean_box_float(v___x_2819_);
v___x_2823_ = lean_box_float(v___x_2821_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2815_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
lean_inc_ref(v___y_2809_);
lean_inc(v___y_2811_);
v___x_2826_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2811_, v___y_2810_, v___y_2809_, v___y_2814_, v___y_2813_, v___y_2808_, v___f_2779_, v___x_2825_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
return v___x_2826_;
}
v___jp_2827_:
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2835_);
v___y_2808_ = v___y_2830_;
v___y_2809_ = v___y_2829_;
v___y_2810_ = v___y_2828_;
v___y_2811_ = v___y_2831_;
v___y_2812_ = v___y_2832_;
v___y_2813_ = v___y_2834_;
v___y_2814_ = v___y_2833_;
v_a_2815_ = v___x_2836_;
goto v___jp_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2939_, lean_object* v_lemmas_2940_, lean_object* v_ctx_2941_, lean_object* v_goals_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2939_, v_lemmas_2940_, v_ctx_2941_, v_goals_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
if (lean_obj_tag(v_x_2949_) == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = l_List_reverse___redArg(v_x_2950_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
else
{
lean_object* v_head_2958_; lean_object* v_tail_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2982_; 
v_head_2958_ = lean_ctor_get(v_x_2949_, 0);
v_tail_2959_ = lean_ctor_get(v_x_2949_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_x_2949_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2961_ = v_x_2949_;
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_tail_2959_);
lean_inc(v_head_2958_);
lean_dec(v_x_2949_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Expr_applySymm(v_head_2958_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v_x_2950_);
lean_ctor_set(v___x_2961_, 0, v_a_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2964_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_x_2950_);
v___x_2966_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v_x_2949_ = v_tail_2959_;
v_x_2950_ = v___x_2966_;
goto _start;
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2981_; 
lean_del_object(v___x_2961_);
v_a_2969_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2971_ = v___x_2963_;
v_isShared_2972_ = v_isSharedCheck_2981_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2963_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2981_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
uint8_t v___y_2974_; uint8_t v___x_2979_; 
v___x_2979_ = l_Lean_Exception_isInterrupt(v_a_2969_);
if (v___x_2979_ == 0)
{
uint8_t v___x_2980_; 
lean_inc(v_a_2969_);
v___x_2980_ = l_Lean_Exception_isRuntime(v_a_2969_);
v___y_2974_ = v___x_2980_;
goto v___jp_2973_;
}
else
{
v___y_2974_ = v___x_2979_;
goto v___jp_2973_;
}
v___jp_2973_:
{
if (v___y_2974_ == 0)
{
lean_del_object(v___x_2971_);
lean_dec(v_a_2969_);
v_x_2949_ = v_tail_2959_;
goto _start;
}
else
{
lean_object* v___x_2977_; 
lean_dec(v_tail_2959_);
lean_dec(v_x_2950_);
if (v_isShared_2972_ == 0)
{
v___x_2977_ = v___x_2971_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2969_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2983_, v_x_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2991_, lean_object* v_hyps_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
if (v_symm_2991_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_hyps_2992_);
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_box(0);
lean_inc(v_hyps_2992_);
v___x_3000_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2992_, v___x_2999_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3009_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = l_List_appendTR___redArg(v_hyps_2992_, v_a_3001_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3005_);
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
else
{
lean_dec(v_hyps_2992_);
return v___x_3000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3010_, lean_object* v_hyps_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_symm_boxed_3017_; lean_object* v_res_3018_; 
v_symm_boxed_3017_ = lean_unbox(v_symm_3010_);
v_res_3018_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3017_, v_hyps_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3019_, size_t v_sz_3020_, size_t v_i_3021_, lean_object* v_b_3022_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_usize_dec_lt(v_i_3021_, v_sz_3020_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_b_3022_);
return v___x_3025_;
}
else
{
lean_object* v_snd_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3044_; 
v_snd_3026_ = lean_ctor_get(v_b_3022_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_b_3022_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v_b_3022_, 0);
lean_dec(v_unused_3045_);
v___x_3028_ = v_b_3022_;
v_isShared_3029_ = v_isSharedCheck_3044_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_snd_3026_);
lean_dec(v_b_3022_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3044_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v_a_3032_; lean_object* v_a_3039_; 
v___x_3030_ = lean_box(0);
v_a_3039_ = lean_array_uget_borrowed(v_as_3019_, v_i_3021_);
if (lean_obj_tag(v_a_3039_) == 0)
{
v_a_3032_ = v_snd_3026_;
goto v___jp_3031_;
}
else
{
lean_object* v_val_3040_; uint8_t v___x_3041_; 
v_val_3040_ = lean_ctor_get(v_a_3039_, 0);
v___x_3041_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_inc(v_val_3040_);
v___x_3042_ = l_Lean_LocalDecl_toExpr(v_val_3040_);
v___x_3043_ = lean_array_push(v_snd_3026_, v___x_3042_);
v_a_3032_ = v___x_3043_;
goto v___jp_3031_;
}
else
{
v_a_3032_ = v_snd_3026_;
goto v___jp_3031_;
}
}
v___jp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v_a_3032_);
lean_ctor_set(v___x_3028_, 0, v___x_3030_);
v___x_3034_ = v___x_3028_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_a_3032_);
v___x_3034_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
size_t v___x_3035_; size_t v___x_3036_; 
v___x_3035_ = ((size_t)1ULL);
v___x_3036_ = lean_usize_add(v_i_3021_, v___x_3035_);
v_i_3021_ = v___x_3036_;
v_b_3022_ = v___x_3034_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3046_, lean_object* v_sz_3047_, lean_object* v_i_3048_, lean_object* v_b_3049_, lean_object* v___y_3050_){
_start:
{
size_t v_sz_boxed_3051_; size_t v_i_boxed_3052_; lean_object* v_res_3053_; 
v_sz_boxed_3051_ = lean_unbox_usize(v_sz_3047_);
lean_dec(v_sz_3047_);
v_i_boxed_3052_ = lean_unbox_usize(v_i_3048_);
lean_dec(v_i_3048_);
v_res_3053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3046_, v_sz_boxed_3051_, v_i_boxed_3052_, v_b_3049_);
lean_dec_ref(v_as_3046_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3054_, size_t v_sz_3055_, size_t v_i_3056_, lean_object* v_b_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v___x_3065_; 
v___x_3065_ = lean_usize_dec_lt(v_i_3056_, v_sz_3055_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v_b_3057_);
return v___x_3066_;
}
else
{
lean_object* v_snd_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3085_; 
v_snd_3067_ = lean_ctor_get(v_b_3057_, 1);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_b_3057_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v_b_3057_, 0);
lean_dec(v_unused_3086_);
v___x_3069_ = v_b_3057_;
v_isShared_3070_ = v_isSharedCheck_3085_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_snd_3067_);
lean_dec(v_b_3057_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3085_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v_a_3073_; lean_object* v_a_3080_; 
v___x_3071_ = lean_box(0);
v_a_3080_ = lean_array_uget_borrowed(v_as_3054_, v_i_3056_);
if (lean_obj_tag(v_a_3080_) == 0)
{
v_a_3073_ = v_snd_3067_;
goto v___jp_3072_;
}
else
{
lean_object* v_val_3081_; uint8_t v___x_3082_; 
v_val_3081_ = lean_ctor_get(v_a_3080_, 0);
v___x_3082_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
lean_inc(v_val_3081_);
v___x_3083_ = l_Lean_LocalDecl_toExpr(v_val_3081_);
v___x_3084_ = lean_array_push(v_snd_3067_, v___x_3083_);
v_a_3073_ = v___x_3084_;
goto v___jp_3072_;
}
else
{
v_a_3073_ = v_snd_3067_;
goto v___jp_3072_;
}
}
v___jp_3072_:
{
lean_object* v___x_3075_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_a_3073_);
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3075_ = v___x_3069_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_a_3073_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_add(v_i_3056_, v___x_3076_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3054_, v_sz_3055_, v___x_3077_, v___x_3075_);
return v___x_3078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3087_, lean_object* v_sz_3088_, lean_object* v_i_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
size_t v_sz_boxed_3098_; size_t v_i_boxed_3099_; lean_object* v_res_3100_; 
v_sz_boxed_3098_ = lean_unbox_usize(v_sz_3088_);
lean_dec(v_sz_3088_);
v_i_boxed_3099_ = lean_unbox_usize(v_i_3089_);
lean_dec(v_i_3089_);
v_res_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3087_, v_sz_boxed_3098_, v_i_boxed_3099_, v_b_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec_ref(v_as_3087_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3101_, size_t v_sz_3102_, size_t v_i_3103_, lean_object* v_b_3104_){
_start:
{
uint8_t v___x_3106_; 
v___x_3106_ = lean_usize_dec_lt(v_i_3103_, v_sz_3102_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v_b_3104_);
return v___x_3107_;
}
else
{
lean_object* v_snd_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3126_; 
v_snd_3108_ = lean_ctor_get(v_b_3104_, 1);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_b_3104_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v_b_3104_, 0);
lean_dec(v_unused_3127_);
v___x_3110_ = v_b_3104_;
v_isShared_3111_ = v_isSharedCheck_3126_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_snd_3108_);
lean_dec(v_b_3104_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3126_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v_a_3114_; lean_object* v_a_3121_; 
v___x_3112_ = lean_box(0);
v_a_3121_ = lean_array_uget_borrowed(v_as_3101_, v_i_3103_);
if (lean_obj_tag(v_a_3121_) == 0)
{
v_a_3114_ = v_snd_3108_;
goto v___jp_3113_;
}
else
{
lean_object* v_val_3122_; uint8_t v___x_3123_; 
v_val_3122_ = lean_ctor_get(v_a_3121_, 0);
v___x_3123_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_inc(v_val_3122_);
v___x_3124_ = l_Lean_LocalDecl_toExpr(v_val_3122_);
v___x_3125_ = lean_array_push(v_snd_3108_, v___x_3124_);
v_a_3114_ = v___x_3125_;
goto v___jp_3113_;
}
else
{
v_a_3114_ = v_snd_3108_;
goto v___jp_3113_;
}
}
v___jp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v_a_3114_);
lean_ctor_set(v___x_3110_, 0, v___x_3112_);
v___x_3116_ = v___x_3110_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_a_3114_);
v___x_3116_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
size_t v___x_3117_; size_t v___x_3118_; 
v___x_3117_ = ((size_t)1ULL);
v___x_3118_ = lean_usize_add(v_i_3103_, v___x_3117_);
v_i_3103_ = v___x_3118_;
v_b_3104_ = v___x_3116_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3128_, lean_object* v_sz_3129_, lean_object* v_i_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_){
_start:
{
size_t v_sz_boxed_3133_; size_t v_i_boxed_3134_; lean_object* v_res_3135_; 
v_sz_boxed_3133_ = lean_unbox_usize(v_sz_3129_);
lean_dec(v_sz_3129_);
v_i_boxed_3134_ = lean_unbox_usize(v_i_3130_);
lean_dec(v_i_3130_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3128_, v_sz_boxed_3133_, v_i_boxed_3134_, v_b_3131_);
lean_dec_ref(v_as_3128_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3136_, size_t v_sz_3137_, size_t v_i_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_usize_dec_lt(v_i_3138_, v_sz_3137_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_b_3139_);
return v___x_3148_;
}
else
{
lean_object* v_snd_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3167_; 
v_snd_3149_ = lean_ctor_get(v_b_3139_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_b_3139_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_b_3139_, 0);
lean_dec(v_unused_3168_);
v___x_3151_ = v_b_3139_;
v_isShared_3152_ = v_isSharedCheck_3167_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_snd_3149_);
lean_dec(v_b_3139_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3167_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v_a_3155_; lean_object* v_a_3162_; 
v___x_3153_ = lean_box(0);
v_a_3162_ = lean_array_uget_borrowed(v_as_3136_, v_i_3138_);
if (lean_obj_tag(v_a_3162_) == 0)
{
v_a_3155_ = v_snd_3149_;
goto v___jp_3154_;
}
else
{
lean_object* v_val_3163_; uint8_t v___x_3164_; 
v_val_3163_ = lean_ctor_get(v_a_3162_, 0);
v___x_3164_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_inc(v_val_3163_);
v___x_3165_ = l_Lean_LocalDecl_toExpr(v_val_3163_);
v___x_3166_ = lean_array_push(v_snd_3149_, v___x_3165_);
v_a_3155_ = v___x_3166_;
goto v___jp_3154_;
}
else
{
v_a_3155_ = v_snd_3149_;
goto v___jp_3154_;
}
}
v___jp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v_a_3155_);
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3157_ = v___x_3151_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_a_3155_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3138_, v___x_3158_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3136_, v_sz_3137_, v___x_3159_, v___x_3157_);
return v___x_3160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3169_, lean_object* v_sz_3170_, lean_object* v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
size_t v_sz_boxed_3180_; size_t v_i_boxed_3181_; lean_object* v_res_3182_; 
v_sz_boxed_3180_ = lean_unbox_usize(v_sz_3170_);
lean_dec(v_sz_3170_);
v_i_boxed_3181_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_res_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3169_, v_sz_boxed_3180_, v_i_boxed_3181_, v_b_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v_as_3169_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3183_, lean_object* v_n_3184_, lean_object* v_b_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
if (lean_obj_tag(v_n_3184_) == 0)
{
lean_object* v_cs_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; size_t v_sz_3196_; size_t v___x_3197_; lean_object* v___x_3198_; 
v_cs_3193_ = lean_ctor_get(v_n_3184_, 0);
v___x_3194_ = lean_box(0);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v_b_3185_);
v_sz_3196_ = lean_array_size(v_cs_3193_);
v___x_3197_ = ((size_t)0ULL);
v___x_3198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3183_, v_cs_3193_, v_sz_3196_, v___x_3197_, v___x_3195_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3213_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3213_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3213_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_fst_3203_; 
v_fst_3203_ = lean_ctor_get(v_a_3199_, 0);
if (lean_obj_tag(v_fst_3203_) == 0)
{
lean_object* v_snd_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v_snd_3204_ = lean_ctor_get(v_a_3199_, 1);
lean_inc(v_snd_3204_);
lean_dec(v_a_3199_);
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_snd_3204_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3205_);
v___x_3207_ = v___x_3201_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
else
{
lean_object* v_val_3209_; lean_object* v___x_3211_; 
lean_inc_ref(v_fst_3203_);
lean_dec(v_a_3199_);
v_val_3209_ = lean_ctor_get(v_fst_3203_, 0);
lean_inc(v_val_3209_);
lean_dec_ref_known(v_fst_3203_, 1);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v_val_3209_);
v___x_3211_ = v___x_3201_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_val_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
v_a_3214_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3198_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3198_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_vs_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; size_t v_sz_3225_; size_t v___x_3226_; lean_object* v___x_3227_; 
v_vs_3222_ = lean_ctor_get(v_n_3184_, 0);
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v_b_3185_);
v_sz_3225_ = lean_array_size(v_vs_3222_);
v___x_3226_ = ((size_t)0ULL);
v___x_3227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3222_, v_sz_3225_, v___x_3226_, v___x_3224_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3242_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3242_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3242_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_fst_3232_; 
v_fst_3232_ = lean_ctor_get(v_a_3228_, 0);
if (lean_obj_tag(v_fst_3232_) == 0)
{
lean_object* v_snd_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v_snd_3233_ = lean_ctor_get(v_a_3228_, 1);
lean_inc(v_snd_3233_);
lean_dec(v_a_3228_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_snd_3233_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3234_);
v___x_3236_ = v___x_3230_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
else
{
lean_object* v_val_3238_; lean_object* v___x_3240_; 
lean_inc_ref(v_fst_3232_);
lean_dec(v_a_3228_);
v_val_3238_ = lean_ctor_get(v_fst_3232_, 0);
lean_inc(v_val_3238_);
lean_dec_ref_known(v_fst_3232_, 1);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v_val_3238_);
v___x_3240_ = v___x_3230_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_val_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
v_a_3243_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3227_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3227_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3251_, lean_object* v_as_3252_, size_t v_sz_3253_, size_t v_i_3254_, lean_object* v_b_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_usize_dec_lt(v_i_3254_, v_sz_3253_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_b_3255_);
return v___x_3264_;
}
else
{
lean_object* v_snd_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3299_; 
v_snd_3265_ = lean_ctor_get(v_b_3255_, 1);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_b_3255_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; 
v_unused_3300_ = lean_ctor_get(v_b_3255_, 0);
lean_dec(v_unused_3300_);
v___x_3267_ = v_b_3255_;
v_isShared_3268_ = v_isSharedCheck_3299_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snd_3265_);
lean_dec(v_b_3255_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3299_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_box(0);
v_a_3270_ = lean_array_uget_borrowed(v_as_3252_, v_i_3254_);
lean_inc(v_snd_3265_);
v___x_3271_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3251_, v_a_3270_, v_snd_3265_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3290_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3290_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3290_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
if (lean_obj_tag(v_a_3272_) == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3272_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v___x_3276_);
v___x_3278_ = v___x_3267_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_snd_3265_);
v___x_3278_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3280_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3278_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; 
lean_del_object(v___x_3274_);
lean_dec(v_snd_3265_);
v_a_3283_ = lean_ctor_get(v_a_3272_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v_a_3272_, 1);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 1, v_a_3283_);
lean_ctor_set(v___x_3267_, 0, v___x_3269_);
v___x_3285_ = v___x_3267_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_a_3283_);
v___x_3285_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
size_t v___x_3286_; size_t v___x_3287_; 
v___x_3286_ = ((size_t)1ULL);
v___x_3287_ = lean_usize_add(v_i_3254_, v___x_3286_);
v_i_3254_ = v___x_3287_;
v_b_3255_ = v___x_3285_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_del_object(v___x_3267_);
lean_dec(v_snd_3265_);
v_a_3291_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3271_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3271_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3301_, lean_object* v_as_3302_, lean_object* v_sz_3303_, lean_object* v_i_3304_, lean_object* v_b_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
size_t v_sz_boxed_3313_; size_t v_i_boxed_3314_; lean_object* v_res_3315_; 
v_sz_boxed_3313_ = lean_unbox_usize(v_sz_3303_);
lean_dec(v_sz_3303_);
v_i_boxed_3314_ = lean_unbox_usize(v_i_3304_);
lean_dec(v_i_3304_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3301_, v_as_3302_, v_sz_boxed_3313_, v_i_boxed_3314_, v_b_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_as_3302_);
lean_dec_ref(v_init_3301_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3316_, lean_object* v_n_3317_, lean_object* v_b_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3316_, v_n_3317_, v_b_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_n_3317_);
lean_dec_ref(v_init_3316_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3327_, lean_object* v_init_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_root_3336_; lean_object* v_tail_3337_; lean_object* v___x_3338_; 
v_root_3336_ = lean_ctor_get(v_t_3327_, 0);
v_tail_3337_ = lean_ctor_get(v_t_3327_, 1);
lean_inc_ref(v_init_3328_);
v___x_3338_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3328_, v_root_3336_, v_init_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec_ref(v_init_3328_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3375_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3375_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3375_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
if (lean_obj_tag(v_a_3339_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; 
v_a_3343_ = lean_ctor_get(v_a_3339_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v_a_3339_, 1);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v_a_3343_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; size_t v_sz_3350_; size_t v___x_3351_; lean_object* v___x_3352_; 
lean_del_object(v___x_3341_);
v_a_3347_ = lean_ctor_get(v_a_3339_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v_a_3339_, 1);
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v_a_3347_);
v_sz_3350_ = lean_array_size(v_tail_3337_);
v___x_3351_ = ((size_t)0ULL);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3337_, v_sz_3350_, v___x_3351_, v___x_3349_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3366_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3366_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3366_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_fst_3357_; 
v_fst_3357_ = lean_ctor_get(v_a_3353_, 0);
if (lean_obj_tag(v_fst_3357_) == 0)
{
lean_object* v_snd_3358_; lean_object* v___x_3360_; 
v_snd_3358_ = lean_ctor_get(v_a_3353_, 1);
lean_inc(v_snd_3358_);
lean_dec(v_a_3353_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v_snd_3358_);
v___x_3360_ = v___x_3355_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_snd_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
else
{
lean_object* v_val_3362_; lean_object* v___x_3364_; 
lean_inc_ref(v_fst_3357_);
lean_dec(v_a_3353_);
v_val_3362_ = lean_ctor_get(v_fst_3357_, 0);
lean_inc(v_val_3362_);
lean_dec_ref_known(v_fst_3357_, 1);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v_val_3362_);
v___x_3364_ = v___x_3355_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_val_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3352_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3352_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_a_3376_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3338_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3338_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3384_, lean_object* v_init_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3384_, v_init_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec_ref(v_t_3384_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_lctx_3403_; lean_object* v_decls_3404_; lean_object* v_hs_3405_; lean_object* v___x_3406_; 
v_lctx_3403_ = lean_ctor_get(v___y_3398_, 2);
v_decls_3404_ = lean_ctor_get(v_lctx_3403_, 1);
v_hs_3405_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3406_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3404_, v_hs_3405_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3415_, lean_object* v_cfg_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
if (v_only_3415_ == 0)
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_toApplyRulesConfig_3425_; lean_object* v_a_3426_; uint8_t v_symm_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_toApplyRulesConfig_3425_ = lean_ctor_get(v_cfg_3416_, 0);
v_a_3426_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3424_, 1);
v_symm_3427_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3425_, sizeof(void*)*2 + 1);
v___x_3428_ = lean_array_to_list(v_a_3426_);
v___x_3429_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3427_, v___x_3428_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
return v___x_3429_;
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
v_a_3430_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3424_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3424_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3440_, lean_object* v_cfg_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
uint8_t v_only_boxed_3449_; lean_object* v_res_3450_; 
v_only_boxed_3449_ = lean_unbox(v_only_3440_);
v_res_3450_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3449_, v_cfg_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_cfg_3441_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3451_, lean_object* v_lemmas_3452_, uint8_t v_only_3453_, lean_object* v_g_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_toApplyRulesConfig_3460_; uint8_t v_intro_3461_; uint8_t v_constructor_3462_; uint8_t v_suggestions_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3476_; 
v_toApplyRulesConfig_3460_ = lean_ctor_get(v_cfg_3451_, 0);
v_intro_3461_ = lean_ctor_get_uint8(v_cfg_3451_, sizeof(void*)*1 + 1);
v_constructor_3462_ = lean_ctor_get_uint8(v_cfg_3451_, sizeof(void*)*1 + 2);
v_suggestions_3463_ = lean_ctor_get_uint8(v_cfg_3451_, sizeof(void*)*1 + 3);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_cfg_3451_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3465_ = v_cfg_3451_;
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_toApplyRulesConfig_3460_);
lean_dec(v_cfg_3451_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v_ctx_3468_; uint8_t v___x_3469_; lean_object* v___x_3471_; 
v___x_3467_ = lean_box(v_only_3453_);
v_ctx_3468_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3468_, 0, v___x_3467_);
v___x_3469_ = 0;
if (v_isShared_3466_ == 0)
{
v___x_3471_ = v___x_3465_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_toApplyRulesConfig_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*1 + 1, v_intro_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*1 + 2, v_constructor_3462_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*1 + 3, v_suggestions_3463_);
v___x_3471_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_ctor_set_uint8(v___x_3471_, sizeof(void*)*1, v___x_3469_);
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3473_, 0, v_g_3454_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3471_, v_lemmas_3452_, v_ctx_3468_, v___x_3473_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
return v___x_3474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3477_, lean_object* v_lemmas_3478_, lean_object* v_only_3479_, lean_object* v_g_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
uint8_t v_only_boxed_3486_; lean_object* v_res_3487_; 
v_only_boxed_3486_ = lean_unbox(v_only_3479_);
v_res_3487_ = l_Lean_MVarId_applyRules(v_cfg_3477_, v_lemmas_3478_, v_only_boxed_3486_, v_g_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3488_, size_t v_sz_3489_, size_t v_i_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3488_, v_sz_3489_, v_i_3490_, v_b_3491_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3500_, lean_object* v_sz_3501_, lean_object* v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
size_t v_sz_boxed_3511_; size_t v_i_boxed_3512_; lean_object* v_res_3513_; 
v_sz_boxed_3511_ = lean_unbox_usize(v_sz_3501_);
lean_dec(v_sz_3501_);
v_i_boxed_3512_ = lean_unbox_usize(v_i_3502_);
lean_dec(v_i_3502_);
v_res_3513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3500_, v_sz_boxed_3511_, v_i_boxed_3512_, v_b_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_as_3500_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3514_, size_t v_sz_3515_, size_t v_i_3516_, lean_object* v_b_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3514_, v_sz_3515_, v_i_3516_, v_b_3517_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3526_, lean_object* v_sz_3527_, lean_object* v_i_3528_, lean_object* v_b_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
size_t v_sz_boxed_3537_; size_t v_i_boxed_3538_; lean_object* v_res_3539_; 
v_sz_boxed_3537_ = lean_unbox_usize(v_sz_3527_);
lean_dec(v_sz_3527_);
v_i_boxed_3538_ = lean_unbox_usize(v_i_3528_);
lean_dec(v_i_3528_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3526_, v_sz_boxed_3537_, v_i_boxed_3538_, v_b_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v_as_3526_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v___x_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = lean_box(0);
v___x_3549_ = 1;
v___x_3550_ = l_Lean_Elab_Term_elabTerm(v_t_3540_, v___x_3548_, v___x_3549_, v___x_3549_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_ref_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_ref_3565_ = lean_ctor_get(v___y_3562_, 2);
v___x_3566_ = 0;
v___x_3567_ = l_Lean_SourceInfo_fromRef(v_ref_3565_, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
return v_res_3574_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object* v_a_3575_, lean_object* v_x_3576_){
_start:
{
if (lean_obj_tag(v_x_3576_) == 0)
{
uint8_t v___x_3577_; 
v___x_3577_ = 0;
return v___x_3577_;
}
else
{
lean_object* v_head_3578_; lean_object* v_tail_3579_; uint8_t v___x_3580_; 
v_head_3578_ = lean_ctor_get(v_x_3576_, 0);
v_tail_3579_ = lean_ctor_get(v_x_3576_, 1);
v___x_3580_ = lean_expr_eqv(v_a_3575_, v_head_3578_);
if (v___x_3580_ == 0)
{
v_x_3576_ = v_tail_3579_;
goto _start;
}
else
{
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object* v_a_3582_, lean_object* v_x_3583_){
_start:
{
uint8_t v_res_3584_; lean_object* v_r_3585_; 
v_res_3584_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3582_, v_x_3583_);
lean_dec(v_x_3583_);
lean_dec_ref(v_a_3582_);
v_r_3585_ = lean_box(v_res_3584_);
return v_r_3585_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(lean_object* v_ys_3586_, lean_object* v_x_3587_){
_start:
{
uint8_t v___x_3588_; 
v___x_3588_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_x_3587_, v_ys_3586_);
if (v___x_3588_ == 0)
{
uint8_t v___x_3589_; 
v___x_3589_ = 1;
return v___x_3589_;
}
else
{
uint8_t v___x_3590_; 
v___x_3590_ = 0;
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed(lean_object* v_ys_3591_, lean_object* v_x_3592_){
_start:
{
uint8_t v_res_3593_; lean_object* v_r_3594_; 
v_res_3593_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(v_ys_3591_, v_x_3592_);
lean_dec_ref(v_x_3592_);
lean_dec(v_ys_3591_);
v_r_3594_ = lean_box(v_res_3593_);
return v_r_3594_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_xs_3595_, lean_object* v_ys_3596_){
_start:
{
lean_object* v___f_3597_; lean_object* v___x_3598_; 
v___f_3597_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3597_, 0, v_ys_3596_);
v___x_3598_ = l_List_filter___redArg(v___f_3597_, v_xs_3595_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object* v_x_3599_, lean_object* v_x_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
if (lean_obj_tag(v_x_3599_) == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = l_List_reverse___redArg(v_x_3600_);
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
else
{
lean_object* v_head_3610_; lean_object* v_tail_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3629_; 
v_head_3610_ = lean_ctor_get(v_x_3599_, 0);
v_tail_3611_ = lean_ctor_get(v_x_3599_, 1);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_x_3599_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3613_ = v_x_3599_;
v_isShared_3614_ = v_isSharedCheck_3629_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_tail_3611_);
lean_inc(v_head_3610_);
lean_dec(v_x_3599_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3629_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3610_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v_x_3600_);
lean_ctor_set(v___x_3613_, 0, v_a_3616_);
v___x_3618_ = v___x_3613_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3616_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_x_3600_);
v___x_3618_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
v_x_3599_ = v_tail_3611_;
v_x_3600_ = v___x_3618_;
goto _start;
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_del_object(v___x_3613_);
lean_dec(v_tail_3611_);
lean_dec(v_x_3600_);
v_a_3621_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3615_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3615_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3630_, v_x_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3640_, uint8_t v_noDefaults_3641_, uint8_t v_star_3642_, lean_object* v_cfg_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
if (v_noDefaults_3641_ == 0)
{
goto v___jp_3651_;
}
else
{
if (v_star_3642_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec(v_remove_3640_);
v___x_3670_ = lean_box(0);
v___x_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
return v___x_3671_;
}
else
{
goto v___jp_3651_;
}
}
v___jp_3651_:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
v___x_3654_ = lean_box(0);
v___x_3655_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_remove_3640_, v___x_3654_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_toApplyRulesConfig_3656_; lean_object* v_a_3657_; uint8_t v_symm_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_toApplyRulesConfig_3656_ = lean_ctor_get(v_cfg_3643_, 0);
v_a_3657_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3655_, 1);
v_symm_3658_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3656_, sizeof(void*)*2 + 1);
v___x_3659_ = lean_array_to_list(v_a_3653_);
v___x_3660_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v___x_3659_, v_a_3657_);
v___x_3661_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3658_, v___x_3660_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
return v___x_3661_;
}
else
{
lean_dec(v_a_3653_);
return v___x_3655_;
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec(v_remove_3640_);
v_a_3662_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3652_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3652_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3672_, lean_object* v_noDefaults_3673_, lean_object* v_star_3674_, lean_object* v_cfg_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
uint8_t v_noDefaults_boxed_3683_; uint8_t v_star_boxed_3684_; lean_object* v_res_3685_; 
v_noDefaults_boxed_3683_ = lean_unbox(v_noDefaults_3673_);
v_star_boxed_3684_ = lean_unbox(v_star_3674_);
v_res_3685_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3672_, v_noDefaults_boxed_3683_, v_star_boxed_3684_, v_cfg_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v_cfg_3675_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t v_sz_3686_, size_t v_i_3687_, lean_object* v_bs_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v___x_3692_; 
v___x_3692_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v_bs_3688_);
return v___x_3693_;
}
else
{
lean_object* v_v_3694_; lean_object* v___x_3695_; lean_object* v_bs_x27_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_v_3694_ = lean_array_uget(v_bs_3688_, v_i_3687_);
v___x_3695_ = lean_unsigned_to_nat(0u);
v_bs_x27_3696_ = lean_array_uset(v_bs_3688_, v_i_3687_, v___x_3695_);
v___x_3697_ = l_Lean_Syntax_getId(v_v_3694_);
lean_dec(v_v_3694_);
v___x_3698_ = l_Lean_labelled(v___x_3697_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; size_t v___x_3700_; size_t v___x_3701_; lean_object* v___x_3702_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = ((size_t)1ULL);
v___x_3701_ = lean_usize_add(v_i_3687_, v___x_3700_);
v___x_3702_ = lean_array_uset(v_bs_x27_3696_, v_i_3687_, v_a_3699_);
v_i_3687_ = v___x_3701_;
v_bs_3688_ = v___x_3702_;
goto _start;
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_bs_x27_3696_);
v_a_3704_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3698_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3698_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object* v_sz_3712_, lean_object* v_i_3713_, lean_object* v_bs_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
size_t v_sz_boxed_3718_; size_t v_i_boxed_3719_; lean_object* v_res_3720_; 
v_sz_boxed_3718_ = lean_unbox_usize(v_sz_3712_);
lean_dec(v_sz_3712_);
v_i_boxed_3719_ = lean_unbox_usize(v_i_3713_);
lean_dec(v_i_3713_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_boxed_3718_, v_i_boxed_3719_, v_bs_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3721_, size_t v_i_3722_, size_t v_stop_3723_, lean_object* v_b_3724_){
_start:
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_usize_dec_eq(v_i_3722_, v_stop_3723_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; size_t v___x_3728_; size_t v___x_3729_; 
v___x_3726_ = lean_array_uget_borrowed(v_as_3721_, v_i_3722_);
v___x_3727_ = l_Array_append___redArg(v_b_3724_, v___x_3726_);
v___x_3728_ = ((size_t)1ULL);
v___x_3729_ = lean_usize_add(v_i_3722_, v___x_3728_);
v_i_3722_ = v___x_3729_;
v_b_3724_ = v___x_3727_;
goto _start;
}
else
{
return v_b_3724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3731_, lean_object* v_i_3732_, lean_object* v_stop_3733_, lean_object* v_b_3734_){
_start:
{
size_t v_i_boxed_3735_; size_t v_stop_boxed_3736_; lean_object* v_res_3737_; 
v_i_boxed_3735_ = lean_unbox_usize(v_i_3732_);
lean_dec(v_i_3732_);
v_stop_boxed_3736_ = lean_unbox_usize(v_stop_3733_);
lean_dec(v_stop_3733_);
v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3731_, v_i_boxed_3735_, v_stop_boxed_3736_, v_b_3734_);
lean_dec_ref(v_as_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3738_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
if (lean_obj_tag(v_a_3756_) == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = l_List_reverse___redArg(v_a_3757_);
return v___x_3758_;
}
else
{
lean_object* v_head_3759_; lean_object* v_tail_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3769_; 
v_head_3759_ = lean_ctor_get(v_a_3756_, 0);
v_tail_3760_ = lean_ctor_get(v_a_3756_, 1);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_a_3756_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3762_ = v_a_3756_;
v_isShared_3763_ = v_isSharedCheck_3769_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_tail_3760_);
lean_inc(v_head_3759_);
lean_dec(v_a_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3769_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___f_3764_; lean_object* v___x_3766_; 
v___f_3764_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3764_, 0, v_head_3759_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 1, v_a_3757_);
lean_ctor_set(v___x_3762_, 0, v___f_3764_);
v___x_3766_ = v___x_3762_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___f_3764_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_a_3757_);
v___x_3766_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
v_a_3756_ = v_tail_3760_;
v_a_3757_ = v___x_3766_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
if (lean_obj_tag(v_a_3770_) == 0)
{
lean_object* v___x_3772_; 
v___x_3772_ = l_List_reverse___redArg(v_a_3771_);
return v___x_3772_;
}
else
{
lean_object* v_head_3773_; lean_object* v_tail_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3783_; 
v_head_3773_ = lean_ctor_get(v_a_3770_, 0);
v_tail_3774_ = lean_ctor_get(v_a_3770_, 1);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_a_3770_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3776_ = v_a_3770_;
v_isShared_3777_ = v_isSharedCheck_3783_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_tail_3774_);
lean_inc(v_head_3773_);
lean_dec(v_a_3770_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3783_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
v___x_3778_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3778_, 0, v_head_3773_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 1, v_a_3771_);
lean_ctor_set(v___x_3776_, 0, v___x_3778_);
v___x_3780_ = v___x_3776_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_a_3771_);
v___x_3780_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
v_a_3770_ = v_tail_3774_;
v_a_3771_ = v___x_3780_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3789_ = l_String_toRawSubstring_x27(v___x_3788_);
return v___x_3789_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3800_ = l_String_toRawSubstring_x27(v___x_3799_);
return v___x_3800_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12));
v___x_3811_ = l_String_toRawSubstring_x27(v___x_3810_);
return v___x_3811_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18(void){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3822_ = l_String_toRawSubstring_x27(v___x_3821_);
return v___x_3822_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3835_ = l_Lean_stringToMessageData(v___x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3836_, uint8_t v_star_3837_, lean_object* v_add_3838_, lean_object* v_remove_3839_, lean_object* v_use_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___f_3871_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; 
v___x_3869_ = lean_box(v_noDefaults_3836_);
v___x_3870_ = lean_box(v_star_3837_);
lean_inc(v_remove_3839_);
v___f_3871_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3871_, 0, v_remove_3839_);
lean_closure_set(v___f_3871_, 1, v___x_3869_);
lean_closure_set(v___f_3871_, 2, v___x_3870_);
if (v_star_3837_ == 0)
{
v___y_3888_ = v_a_3841_;
v___y_3889_ = v_a_3842_;
v___y_3890_ = v_a_3843_;
v___y_3891_ = v_a_3844_;
goto v___jp_3887_;
}
else
{
if (v_noDefaults_3836_ == 0)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec_ref(v___f_3871_);
lean_dec_ref(v_use_3840_);
lean_dec(v_remove_3839_);
lean_dec(v_add_3838_);
v___x_3948_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3949_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3948_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3949_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
else
{
v___y_3888_ = v_a_3841_;
v___y_3889_ = v_a_3842_;
v___y_3890_ = v_a_3843_;
v___y_3891_ = v_a_3844_;
goto v___jp_3887_;
}
}
v___jp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___y_3848_);
lean_ctor_set(v___x_3849_, 1, v___y_3847_);
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
return v___x_3850_;
}
v___jp_3851_:
{
uint8_t v___x_3858_; 
v___x_3858_ = l_List_isEmpty___redArg(v_remove_3839_);
lean_dec(v_remove_3839_);
if (v___x_3858_ == 0)
{
if (v_noDefaults_3836_ == 0)
{
v___y_3847_ = v___y_3855_;
v___y_3848_ = v___y_3857_;
goto v___jp_3846_;
}
else
{
if (v_star_3837_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3855_);
v___x_3859_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3860_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3859_, v___y_3853_, v___y_3856_, v___y_3852_, v___y_3854_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
else
{
v___y_3847_ = v___y_3855_;
v___y_3848_ = v___y_3857_;
goto v___jp_3846_;
}
}
}
else
{
v___y_3847_ = v___y_3855_;
v___y_3848_ = v___y_3857_;
goto v___jp_3846_;
}
}
v___jp_3872_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_array_to_list(v___y_3879_);
lean_inc(v___y_3875_);
v___x_3881_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3880_, v___y_3875_);
if (v_noDefaults_3836_ == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3838_, v___y_3875_);
v___x_3883_ = l_List_appendTR___redArg(v___x_3882_, v___x_3881_);
v___x_3884_ = l_List_appendTR___redArg(v___x_3883_, v___y_3878_);
v___y_3852_ = v___y_3873_;
v___y_3853_ = v___y_3874_;
v___y_3854_ = v___y_3876_;
v___y_3855_ = v___f_3871_;
v___y_3856_ = v___y_3877_;
v___y_3857_ = v___x_3884_;
goto v___jp_3851_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec(v___y_3878_);
v___x_3885_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3838_, v___y_3875_);
v___x_3886_ = l_List_appendTR___redArg(v___x_3885_, v___x_3881_);
v___y_3852_ = v___y_3873_;
v___y_3853_ = v___y_3874_;
v___y_3854_ = v___y_3876_;
v___y_3855_ = v___f_3871_;
v___y_3856_ = v___y_3877_;
v___y_3857_ = v___x_3886_;
goto v___jp_3851_;
}
}
v___jp_3887_:
{
lean_object* v_toCold_3892_; lean_object* v_ref_3893_; lean_object* v_quotContext_3894_; lean_object* v_currMacroScope_3895_; uint8_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v_a_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v_a_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; size_t v_sz_3930_; size_t v___x_3931_; lean_object* v___x_3932_; 
v_toCold_3892_ = lean_ctor_get(v___y_3890_, 0);
v_ref_3893_ = lean_ctor_get(v___y_3890_, 2);
v_quotContext_3894_ = lean_ctor_get(v_toCold_3892_, 8);
v_currMacroScope_3895_ = lean_ctor_get(v_toCold_3892_, 9);
v___x_3896_ = 0;
v___x_3897_ = l_Lean_SourceInfo_fromRef(v_ref_3893_, v___x_3896_);
v___x_3898_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3895_, 4);
lean_inc_n(v_quotContext_3894_, 4);
v___x_3900_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3899_, v_currMacroScope_3895_);
v___x_3901_ = lean_box(0);
v___x_3902_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6));
v___x_3903_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3897_);
lean_ctor_set(v___x_3903_, 1, v___x_3898_);
lean_ctor_set(v___x_3903_, 2, v___x_3900_);
lean_ctor_set(v___x_3903_, 3, v___x_3902_);
v___x_3904_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref(v___x_3904_);
v___x_3906_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8);
v___x_3907_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9));
v___x_3908_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3907_, v_currMacroScope_3895_);
v___x_3909_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3910_, 0, v_a_3905_);
lean_ctor_set(v___x_3910_, 1, v___x_3906_);
lean_ctor_set(v___x_3910_, 2, v___x_3908_);
lean_ctor_set(v___x_3910_, 3, v___x_3909_);
v___x_3911_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref(v___x_3911_);
v___x_3913_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13);
v___x_3914_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14));
v___x_3915_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3914_, v_currMacroScope_3895_);
v___x_3916_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16));
v___x_3917_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3917_, 0, v_a_3912_);
lean_ctor_set(v___x_3917_, 1, v___x_3913_);
lean_ctor_set(v___x_3917_, 2, v___x_3915_);
lean_ctor_set(v___x_3917_, 3, v___x_3916_);
v___x_3918_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref(v___x_3918_);
v___x_3920_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18);
v___x_3921_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3922_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3921_, v_currMacroScope_3895_);
v___x_3923_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3924_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3924_, 0, v_a_3919_);
lean_ctor_set(v___x_3924_, 1, v___x_3920_);
lean_ctor_set(v___x_3924_, 2, v___x_3922_);
lean_ctor_set(v___x_3924_, 3, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v___x_3901_);
v___x_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3917_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3910_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3903_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3928_, v___x_3901_);
v_sz_3930_ = lean_array_size(v_use_3840_);
v___x_3931_ = ((size_t)0ULL);
v___x_3932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3930_, v___x_3931_, v_use_3840_, v___y_3890_, v___y_3891_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3934_ = lean_unsigned_to_nat(0u);
v___x_3935_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3936_ = lean_array_get_size(v_a_3933_);
v___x_3937_ = lean_nat_dec_lt(v___x_3934_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_dec(v_a_3933_);
v___y_3873_ = v___y_3890_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___x_3901_;
v___y_3876_ = v___y_3891_;
v___y_3877_ = v___y_3889_;
v___y_3878_ = v___x_3929_;
v___y_3879_ = v___x_3935_;
goto v___jp_3872_;
}
else
{
size_t v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_usize_of_nat(v___x_3936_);
v___x_3939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3933_, v___x_3931_, v___x_3938_, v___x_3935_);
lean_dec(v_a_3933_);
v___y_3873_ = v___y_3890_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___x_3901_;
v___y_3876_ = v___y_3891_;
v___y_3877_ = v___y_3889_;
v___y_3878_ = v___x_3929_;
v___y_3879_ = v___x_3939_;
goto v___jp_3872_;
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v___x_3929_);
lean_dec_ref(v___f_3871_);
lean_dec(v_remove_3839_);
lean_dec(v_add_3838_);
v_a_3940_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3932_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3932_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3958_, lean_object* v_star_3959_, lean_object* v_add_3960_, lean_object* v_remove_3961_, lean_object* v_use_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
uint8_t v_noDefaults_boxed_3968_; uint8_t v_star_boxed_3969_; lean_object* v_res_3970_; 
v_noDefaults_boxed_3968_ = lean_unbox(v_noDefaults_3958_);
v_star_boxed_3969_ = lean_unbox(v_star_3959_);
v_res_3970_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3968_, v_star_boxed_3969_, v_add_3960_, v_remove_3961_, v_use_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t v_sz_3971_, size_t v_i_3972_, lean_object* v_bs_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3971_, v_i_3972_, v_bs_3973_, v___y_3976_, v___y_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object* v_sz_3980_, lean_object* v_i_3981_, lean_object* v_bs_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
size_t v_sz_boxed_3988_; size_t v_i_boxed_3989_; lean_object* v_res_3990_; 
v_sz_boxed_3988_ = lean_unbox_usize(v_sz_3980_);
lean_dec(v_sz_3980_);
v_i_boxed_3989_ = lean_unbox_usize(v_i_3981_);
lean_dec(v_i_3981_);
v_res_3990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_boxed_3988_, v_i_boxed_3989_, v_bs_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
return v_res_3990_;
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

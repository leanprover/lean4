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
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_200_; 
v_a_170_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_200_ == 0)
{
v___x_172_ = v___x_160_;
v_isShared_173_ = v_isSharedCheck_200_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_160_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_200_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_Exception_isInterrupt(v_a_170_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; 
lean_inc(v_a_170_);
v___x_175_ = l_Lean_Exception_isRuntime(v_a_170_);
if (v___x_175_ == 0)
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
else
{
lean_object* v___x_198_; 
lean_dec(v_a_159_);
if (v_isShared_173_ == 0)
{
v___x_198_ = v___x_172_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_170_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_x_152_);
v_a_201_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_158_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_158_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_216_, lean_object* v_x_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_224_, lean_object* v_x_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_224_, v_x_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_235_, lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_243_ = l_Lean_MessageData_ofExpr(v_e_235_);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_246_, lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_246_, v_x_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec_ref(v_x_247_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_254_, uint8_t v___x_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_x_257_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_tail_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_290_; 
v_head_264_ = lean_ctor_get(v_x_256_, 0);
v_tail_265_ = lean_ctor_get(v_x_256_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_290_ == 0)
{
v___x_267_ = v_x_256_;
v_isShared_268_ = v_isSharedCheck_290_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_tail_265_);
lean_inc(v_head_264_);
lean_dec(v_x_256_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_290_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
uint8_t v_a_270_; lean_object* v___x_276_; 
lean_inc(v_head_264_);
v___x_276_ = l_Lean_MVarId_inferInstance(v_head_264_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_dec_ref_known(v___x_276_, 1);
v_a_270_ = v___x_254_;
goto v___jp_269_;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_289_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
uint8_t v___x_281_; 
v___x_281_ = l_Lean_Exception_isInterrupt(v_a_277_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; 
lean_inc(v_a_277_);
v___x_282_ = l_Lean_Exception_isRuntime(v_a_277_);
if (v___x_282_ == 0)
{
lean_del_object(v___x_279_);
lean_dec(v_a_277_);
v_a_270_ = v___x_255_;
goto v___jp_269_;
}
else
{
lean_object* v___x_284_; 
lean_del_object(v___x_267_);
lean_dec(v_tail_265_);
lean_dec(v_head_264_);
lean_dec(v_x_257_);
if (v_isShared_280_ == 0)
{
v___x_284_ = v___x_279_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_277_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v___x_287_; 
lean_del_object(v___x_267_);
lean_dec(v_tail_265_);
lean_dec(v_head_264_);
lean_dec(v_x_257_);
if (v_isShared_280_ == 0)
{
v___x_287_ = v___x_279_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_277_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
v___jp_269_:
{
if (v_a_270_ == 0)
{
lean_del_object(v___x_267_);
lean_dec(v_head_264_);
v_x_256_ = v_tail_265_;
goto _start;
}
else
{
lean_object* v___x_273_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_x_257_);
v___x_273_ = v___x_267_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_head_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_x_257_);
v___x_273_ = v_reuseFailAlloc_275_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v_x_256_ = v_tail_265_;
v_x_257_ = v___x_273_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_291_, lean_object* v___x_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v___x_13720__boxed_300_; uint8_t v___x_13721__boxed_301_; lean_object* v_res_302_; 
v___x_13720__boxed_300_ = lean_unbox(v___x_291_);
v___x_13721__boxed_301_ = lean_unbox(v___x_292_);
v_res_302_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13720__boxed_300_, v___x_13721__boxed_301_, v_x_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_env_310_; uint8_t v___x_311_; lean_object* v_env_312_; lean_object* v___x_313_; lean_object* v_toCold_314_; lean_object* v_mctx_315_; lean_object* v_lctx_316_; lean_object* v_options_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
v___x_311_ = 0;
v_env_312_ = l_Lean_Environment_setRecordingDeps(v_env_310_, v___x_311_);
v___x_313_ = lean_st_ref_get(v___y_305_);
v_toCold_314_ = lean_ctor_get(v___y_306_, 0);
v_mctx_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_mctx_315_);
lean_dec(v___x_313_);
v_lctx_316_ = lean_ctor_get(v___y_304_, 2);
v_options_317_ = lean_ctor_get(v_toCold_314_, 2);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_lctx_316_);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v_env_312_);
lean_ctor_set(v___x_318_, 1, v_mctx_315_);
lean_ctor_set(v___x_318_, 2, v_lctx_316_);
lean_ctor_set(v___x_318_, 3, v_options_317_);
v___x_319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_msgData_303_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_328_, size_t v_i_329_, lean_object* v_bs_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_331_ == 0)
{
return v_bs_330_;
}
else
{
lean_object* v_v_332_; lean_object* v_msg_333_; lean_object* v___x_334_; lean_object* v_bs_x27_335_; size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v_v_332_ = lean_array_uget_borrowed(v_bs_330_, v_i_329_);
v_msg_333_ = lean_ctor_get(v_v_332_, 1);
lean_inc_ref(v_msg_333_);
v___x_334_ = lean_unsigned_to_nat(0u);
v_bs_x27_335_ = lean_array_uset(v_bs_330_, v_i_329_, v___x_334_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_329_, v___x_336_);
v___x_338_ = lean_array_uset(v_bs_x27_335_, v_i_329_, v_msg_333_);
v_i_329_ = v___x_337_;
v_bs_330_ = v___x_338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_340_, lean_object* v_i_341_, lean_object* v_bs_342_){
_start:
{
size_t v_sz_boxed_343_; size_t v_i_boxed_344_; lean_object* v_res_345_; 
v_sz_boxed_343_ = lean_unbox_usize(v_sz_340_);
lean_dec(v_sz_340_);
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_343_, v_i_boxed_344_, v_bs_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_346_, lean_object* v_data_347_, lean_object* v_ref_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_toCold_355_; lean_object* v_currRecDepth_356_; lean_object* v_ref_357_; uint16_t v_optionFlags_358_; uint8_t v_suppressElabErrors_359_; uint8_t v_isRecordingDeps_360_; lean_object* v_ref_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_traceState_364_; lean_object* v_traces_365_; lean_object* v___x_366_; size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v_msg_370_; lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_410_; 
v_toCold_355_ = lean_ctor_get(v___y_352_, 0);
v_currRecDepth_356_ = lean_ctor_get(v___y_352_, 1);
v_ref_357_ = lean_ctor_get(v___y_352_, 2);
v_optionFlags_358_ = lean_ctor_get_uint16(v___y_352_, sizeof(void*)*3);
v_suppressElabErrors_359_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 2);
v_isRecordingDeps_360_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 3);
v_ref_361_ = l_Lean_replaceRef(v_ref_348_, v_ref_357_);
lean_inc(v_currRecDepth_356_);
lean_inc_ref(v_toCold_355_);
v___x_362_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_362_, 0, v_toCold_355_);
lean_ctor_set(v___x_362_, 1, v_currRecDepth_356_);
lean_ctor_set(v___x_362_, 2, v_ref_361_);
lean_ctor_set_uint16(v___x_362_, sizeof(void*)*3, v_optionFlags_358_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*3 + 2, v_suppressElabErrors_359_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*3 + 3, v_isRecordingDeps_360_);
v___x_363_ = lean_st_ref_get(v___y_353_);
v_traceState_364_ = lean_ctor_get(v___x_363_, 4);
lean_inc_ref(v_traceState_364_);
lean_dec(v___x_363_);
v_traces_365_ = lean_ctor_get(v_traceState_364_, 0);
lean_inc_ref(v_traces_365_);
lean_dec_ref(v_traceState_364_);
v___x_366_ = l_Lean_PersistentArray_toArray___redArg(v_traces_365_);
lean_dec_ref(v_traces_365_);
v_sz_367_ = lean_array_size(v___x_366_);
v___x_368_ = ((size_t)0ULL);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_367_, v___x_368_, v___x_366_);
v_msg_370_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_370_, 0, v_data_347_);
lean_ctor_set(v_msg_370_, 1, v_msg_349_);
lean_ctor_set(v_msg_370_, 2, v___x_369_);
v___x_371_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_370_, v___y_350_, v___y_351_, v___x_362_, v___y_353_);
lean_dec_ref_known(v___x_362_, 3);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_410_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_410_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_410_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v_traceState_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_cache_382_; lean_object* v_recordedDeps_383_; lean_object* v_messages_384_; lean_object* v_infoState_385_; lean_object* v_snapshotTasks_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_409_; 
v___x_376_ = lean_st_ref_take(v___y_353_);
v_traceState_377_ = lean_ctor_get(v___x_376_, 4);
v_env_378_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_376_, 1);
v_ngen_380_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_376_, 3);
v_cache_382_ = lean_ctor_get(v___x_376_, 5);
v_recordedDeps_383_ = lean_ctor_get(v___x_376_, 6);
v_messages_384_ = lean_ctor_get(v___x_376_, 7);
v_infoState_385_ = lean_ctor_get(v___x_376_, 8);
v_snapshotTasks_386_ = lean_ctor_get(v___x_376_, 9);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_409_ == 0)
{
v___x_388_ = v___x_376_;
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snapshotTasks_386_);
lean_inc(v_infoState_385_);
lean_inc(v_messages_384_);
lean_inc(v_recordedDeps_383_);
lean_inc(v_cache_382_);
lean_inc(v_traceState_377_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_376_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint64_t v_tid_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_407_; 
v_tid_390_ = lean_ctor_get_uint64(v_traceState_377_, sizeof(void*)*1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_traceState_377_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_traceState_377_, 0);
lean_dec(v_unused_408_);
v___x_392_ = v_traceState_377_;
v_isShared_393_ = v_isSharedCheck_407_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_traceState_377_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_407_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_ref_348_);
lean_ctor_set(v___x_395_, 1, v_a_372_);
v___x_396_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_346_, v___x_395_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_396_);
v___x_398_ = v___x_392_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_396_);
lean_ctor_set_uint64(v_reuseFailAlloc_406_, sizeof(void*)*1, v_tid_390_);
v___x_398_ = v_reuseFailAlloc_406_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v___x_398_);
v___x_400_ = v___x_388_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_env_378_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v_cache_382_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_recordedDeps_383_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_messages_384_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_infoState_385_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_snapshotTasks_386_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_st_ref_put(v___y_353_, v___x_400_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_394_);
v___x_403_ = v___x_374_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_394_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_411_, lean_object* v_data_412_, lean_object* v_ref_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_411_, v_data_412_, v_ref_413_, v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_421_){
_start:
{
if (lean_obj_tag(v_e_421_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 2;
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_424_);
lean_dec_ref(v_e_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_427_, lean_object* v_opt_428_){
_start:
{
lean_object* v_name_429_; lean_object* v_defValue_430_; lean_object* v_map_431_; lean_object* v___x_432_; 
v_name_429_ = lean_ctor_get(v_opt_428_, 0);
v_defValue_430_ = lean_ctor_get(v_opt_428_, 1);
v_map_431_ = lean_ctor_get(v_opts_427_, 0);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_431_, v_name_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_inc(v_defValue_430_);
return v_defValue_430_;
}
else
{
lean_object* v_val_433_; 
v_val_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v___x_432_, 1);
if (lean_obj_tag(v_val_433_) == 3)
{
lean_object* v_v_434_; 
v_v_434_ = lean_ctor_get(v_val_433_, 0);
lean_inc(v_v_434_);
lean_dec_ref_known(v_val_433_, 1);
return v_v_434_;
}
else
{
lean_dec(v_val_433_);
lean_inc(v_defValue_430_);
return v_defValue_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_435_, lean_object* v_opt_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_435_, v_opt_436_);
lean_dec_ref(v_opt_436_);
lean_dec_ref(v_opts_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v_x_438_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v_x_438_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v_x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 1);
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v_x_438_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v_x_438_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v_x_438_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_456_);
return v_res_458_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_459_; double v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_float_of_nat(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_464_; double v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1000u);
v___x_465_ = lean_float_of_nat(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_466_, uint8_t v_collapsed_467_, lean_object* v_tag_468_, lean_object* v_opts_469_, uint8_t v_clsEnabled_470_, lean_object* v_oldTraces_471_, lean_object* v_msg_472_, lean_object* v_resStartStop_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v_data_484_; lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___y_500_; lean_object* v_a_501_; uint8_t v___y_516_; double v___y_548_; 
v_fst_479_ = lean_ctor_get(v_resStartStop_473_, 0);
lean_inc(v_fst_479_);
v_snd_480_ = lean_ctor_get(v_resStartStop_473_, 1);
lean_inc(v_snd_480_);
lean_dec_ref(v_resStartStop_473_);
v_fst_495_ = lean_ctor_get(v_snd_480_, 0);
lean_inc(v_fst_495_);
v_snd_496_ = lean_ctor_get(v_snd_480_, 1);
lean_inc(v_snd_496_);
lean_dec(v_snd_480_);
v___x_497_ = l_Lean_trace_profiler;
v___x_498_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_469_, v___x_497_);
if (v___x_498_ == 0)
{
v___y_516_ = v___x_498_;
goto v___jp_515_;
}
else
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = l_Lean_trace_profiler_useHeartbeats;
v___x_554_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_469_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; double v___x_557_; double v___x_558_; double v___x_559_; 
v___x_555_ = l_Lean_trace_profiler_threshold;
v___x_556_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_469_, v___x_555_);
v___x_557_ = lean_float_of_nat(v___x_556_);
v___x_558_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_559_ = lean_float_div(v___x_557_, v___x_558_);
v___y_548_ = v___x_559_;
goto v___jp_547_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; double v___x_562_; 
v___x_560_ = l_Lean_trace_profiler_threshold;
v___x_561_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_469_, v___x_560_);
v___x_562_ = lean_float_of_nat(v___x_561_);
v___y_548_ = v___x_562_;
goto v___jp_547_;
}
}
v___jp_481_:
{
lean_object* v___x_485_; 
lean_inc(v___y_482_);
v___x_485_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_471_, v_data_484_, v___y_482_, v___y_483_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v___x_486_; 
lean_dec_ref_known(v___x_485_, 1);
v___x_486_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_479_);
return v___x_486_;
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_fst_479_);
v_a_487_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_485_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
v___jp_499_:
{
uint8_t v_result_502_; lean_object* v___x_503_; lean_object* v___x_504_; double v___x_505_; lean_object* v_data_506_; 
v_result_502_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_479_);
v___x_503_ = lean_box(v_result_502_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_468_);
lean_inc_ref(v___x_504_);
lean_inc(v_cls_466_);
v_data_506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_506_, 0, v_cls_466_);
lean_ctor_set(v_data_506_, 1, v___x_504_);
lean_ctor_set(v_data_506_, 2, v_tag_468_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3, v___x_505_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3 + 8, v___x_505_);
lean_ctor_set_uint8(v_data_506_, sizeof(void*)*3 + 16, v_collapsed_467_);
if (v___x_498_ == 0)
{
lean_dec_ref_known(v___x_504_, 1);
lean_dec(v_snd_496_);
lean_dec(v_fst_495_);
lean_dec_ref(v_tag_468_);
lean_dec(v_cls_466_);
v___y_482_ = v___y_500_;
v___y_483_ = v_a_501_;
v_data_484_ = v_data_506_;
goto v___jp_481_;
}
else
{
lean_object* v_data_507_; double v___x_508_; double v___x_509_; 
lean_dec_ref_known(v_data_506_, 3);
v_data_507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_507_, 0, v_cls_466_);
lean_ctor_set(v_data_507_, 1, v___x_504_);
lean_ctor_set(v_data_507_, 2, v_tag_468_);
v___x_508_ = lean_unbox_float(v_fst_495_);
lean_dec(v_fst_495_);
lean_ctor_set_float(v_data_507_, sizeof(void*)*3, v___x_508_);
v___x_509_ = lean_unbox_float(v_snd_496_);
lean_dec(v_snd_496_);
lean_ctor_set_float(v_data_507_, sizeof(void*)*3 + 8, v___x_509_);
lean_ctor_set_uint8(v_data_507_, sizeof(void*)*3 + 16, v_collapsed_467_);
v___y_482_ = v___y_500_;
v___y_483_ = v_a_501_;
v_data_484_ = v_data_507_;
goto v___jp_481_;
}
}
v___jp_510_:
{
lean_object* v_ref_511_; lean_object* v___x_512_; 
v_ref_511_ = lean_ctor_get(v___y_476_, 2);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v_fst_479_);
v___x_512_ = lean_apply_6(v_msg_472_, v_fst_479_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, lean_box(0));
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v___y_500_ = v_ref_511_;
v_a_501_ = v_a_513_;
goto v___jp_499_;
}
else
{
lean_object* v___x_514_; 
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_500_ = v_ref_511_;
v_a_501_ = v___x_514_;
goto v___jp_499_;
}
}
v___jp_515_:
{
if (v_clsEnabled_470_ == 0)
{
if (v___y_516_ == 0)
{
lean_object* v___x_517_; lean_object* v_traceState_518_; lean_object* v_env_519_; lean_object* v_nextMacroScope_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_cache_523_; lean_object* v_recordedDeps_524_; lean_object* v_messages_525_; lean_object* v_infoState_526_; lean_object* v_snapshotTasks_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_snd_496_);
lean_dec(v_fst_495_);
lean_dec_ref(v_msg_472_);
lean_dec_ref(v_tag_468_);
lean_dec(v_cls_466_);
v___x_517_ = lean_st_ref_take(v___y_477_);
v_traceState_518_ = lean_ctor_get(v___x_517_, 4);
v_env_519_ = lean_ctor_get(v___x_517_, 0);
v_nextMacroScope_520_ = lean_ctor_get(v___x_517_, 1);
v_ngen_521_ = lean_ctor_get(v___x_517_, 2);
v_auxDeclNGen_522_ = lean_ctor_get(v___x_517_, 3);
v_cache_523_ = lean_ctor_get(v___x_517_, 5);
v_recordedDeps_524_ = lean_ctor_get(v___x_517_, 6);
v_messages_525_ = lean_ctor_get(v___x_517_, 7);
v_infoState_526_ = lean_ctor_get(v___x_517_, 8);
v_snapshotTasks_527_ = lean_ctor_get(v___x_517_, 9);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_546_ == 0)
{
v___x_529_ = v___x_517_;
v_isShared_530_ = v_isSharedCheck_546_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snapshotTasks_527_);
lean_inc(v_infoState_526_);
lean_inc(v_messages_525_);
lean_inc(v_recordedDeps_524_);
lean_inc(v_cache_523_);
lean_inc(v_traceState_518_);
lean_inc(v_auxDeclNGen_522_);
lean_inc(v_ngen_521_);
lean_inc(v_nextMacroScope_520_);
lean_inc(v_env_519_);
lean_dec(v___x_517_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_546_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint64_t v_tid_531_; lean_object* v_traces_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_545_; 
v_tid_531_ = lean_ctor_get_uint64(v_traceState_518_, sizeof(void*)*1);
v_traces_532_ = lean_ctor_get(v_traceState_518_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_traceState_518_);
if (v_isSharedCheck_545_ == 0)
{
v___x_534_ = v_traceState_518_;
v_isShared_535_ = v_isSharedCheck_545_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_traces_532_);
lean_dec(v_traceState_518_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_545_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_471_, v_traces_532_);
lean_dec_ref(v_traces_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_536_);
lean_ctor_set_uint64(v_reuseFailAlloc_544_, sizeof(void*)*1, v_tid_531_);
v___x_538_ = v_reuseFailAlloc_544_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 4, v___x_538_);
v___x_540_ = v___x_529_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_env_519_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_nextMacroScope_520_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_543_, 5, v_cache_523_);
lean_ctor_set(v_reuseFailAlloc_543_, 6, v_recordedDeps_524_);
lean_ctor_set(v_reuseFailAlloc_543_, 7, v_messages_525_);
lean_ctor_set(v_reuseFailAlloc_543_, 8, v_infoState_526_);
lean_ctor_set(v_reuseFailAlloc_543_, 9, v_snapshotTasks_527_);
v___x_540_ = v_reuseFailAlloc_543_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_st_ref_put(v___y_477_, v___x_540_);
v___x_542_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_479_);
return v___x_542_;
}
}
}
}
}
else
{
goto v___jp_510_;
}
}
else
{
goto v___jp_510_;
}
}
v___jp_547_:
{
double v___x_549_; double v___x_550_; double v___x_551_; uint8_t v___x_552_; 
v___x_549_ = lean_unbox_float(v_snd_496_);
v___x_550_ = lean_unbox_float(v_fst_495_);
v___x_551_ = lean_float_sub(v___x_549_, v___x_550_);
v___x_552_ = lean_float_decLt(v___y_548_, v___x_551_);
v___y_516_ = v___x_552_;
goto v___jp_515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_563_, lean_object* v_collapsed_564_, lean_object* v_tag_565_, lean_object* v_opts_566_, lean_object* v_clsEnabled_567_, lean_object* v_oldTraces_568_, lean_object* v_msg_569_, lean_object* v_resStartStop_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v_collapsed_boxed_576_; uint8_t v_clsEnabled_boxed_577_; lean_object* v_res_578_; 
v_collapsed_boxed_576_ = lean_unbox(v_collapsed_564_);
v_clsEnabled_boxed_577_ = lean_unbox(v_clsEnabled_567_);
v_res_578_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_563_, v_collapsed_boxed_576_, v_tag_565_, v_opts_566_, v_clsEnabled_boxed_577_, v_oldTraces_568_, v_msg_569_, v_resStartStop_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_opts_566_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_x_581_);
return v___x_587_;
}
else
{
lean_object* v_head_588_; lean_object* v_tail_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_613_; 
v_head_588_ = lean_ctor_get(v_x_580_, 0);
v_tail_589_ = lean_ctor_get(v_x_580_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_613_ == 0)
{
v___x_591_ = v_x_580_;
v_isShared_592_ = v_isSharedCheck_613_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_tail_589_);
lean_inc(v_head_588_);
lean_dec(v_x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_613_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; 
lean_inc(v_head_588_);
v___x_593_ = l_Lean_MVarId_inferInstance(v_head_588_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_dec_ref_known(v___x_593_, 1);
lean_del_object(v___x_591_);
lean_dec(v_head_588_);
v_x_580_ = v_tail_589_;
goto _start;
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_612_; 
v_a_595_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_612_ == 0)
{
v___x_597_ = v___x_593_;
v_isShared_598_ = v_isSharedCheck_612_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_612_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_Exception_isInterrupt(v_a_595_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
lean_inc(v_a_595_);
v___x_600_ = l_Lean_Exception_isRuntime(v_a_595_);
if (v___x_600_ == 0)
{
lean_del_object(v___x_597_);
lean_dec(v_a_595_);
if (v___x_579_ == 0)
{
lean_del_object(v___x_591_);
lean_dec(v_head_588_);
v_x_580_ = v_tail_589_;
goto _start;
}
else
{
lean_object* v___x_603_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v_x_581_);
v___x_603_ = v___x_591_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_head_588_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_x_581_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
v_x_580_ = v_tail_589_;
v_x_581_ = v___x_603_;
goto _start;
}
}
}
else
{
lean_object* v___x_607_; 
lean_del_object(v___x_591_);
lean_dec(v_tail_589_);
lean_dec(v_head_588_);
lean_dec(v_x_581_);
if (v_isShared_598_ == 0)
{
v___x_607_ = v___x_597_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_595_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v___x_610_; 
lean_del_object(v___x_591_);
lean_dec(v_tail_589_);
lean_dec(v_head_588_);
lean_dec(v_x_581_);
if (v_isShared_598_ == 0)
{
v___x_610_ = v___x_597_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_595_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_14149__boxed_622_; lean_object* v_res_623_; 
v___x_14149__boxed_622_ = lean_unbox(v___x_614_);
v_res_623_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14149__boxed_622_, v_x_615_, v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_x_626_);
return v___x_632_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_658_; 
v_head_633_ = lean_ctor_get(v_x_625_, 0);
v_tail_634_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_658_ == 0)
{
v___x_636_ = v_x_625_;
v_isShared_637_ = v_isSharedCheck_658_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_tail_634_);
lean_inc(v_head_633_);
lean_dec(v_x_625_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_658_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_643_; 
lean_inc(v_head_633_);
v___x_643_ = l_Lean_MVarId_inferInstance(v_head_633_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref_known(v___x_643_, 1);
if (v___x_624_ == 0)
{
lean_del_object(v___x_636_);
lean_dec(v_head_633_);
v_x_625_ = v_tail_634_;
goto _start;
}
else
{
goto v___jp_638_;
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_657_; 
v_a_645_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_657_ == 0)
{
v___x_647_ = v___x_643_;
v_isShared_648_ = v_isSharedCheck_657_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_657_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; 
v___x_649_ = l_Lean_Exception_isInterrupt(v_a_645_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
lean_inc(v_a_645_);
v___x_650_ = l_Lean_Exception_isRuntime(v_a_645_);
if (v___x_650_ == 0)
{
lean_del_object(v___x_647_);
lean_dec(v_a_645_);
goto v___jp_638_;
}
else
{
lean_object* v___x_652_; 
lean_del_object(v___x_636_);
lean_dec(v_tail_634_);
lean_dec(v_head_633_);
lean_dec(v_x_626_);
if (v_isShared_648_ == 0)
{
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_645_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_del_object(v___x_636_);
lean_dec(v_tail_634_);
lean_dec(v_head_633_);
lean_dec(v_x_626_);
if (v_isShared_648_ == 0)
{
v___x_655_ = v___x_647_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_645_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
v___jp_638_:
{
lean_object* v___x_640_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_x_626_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_head_633_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_x_626_);
v___x_640_ = v_reuseFailAlloc_642_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v_x_625_ = v_tail_634_;
v_x_626_ = v___x_640_;
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
uint8_t v___x_14228__boxed_667_; lean_object* v_res_668_; 
v___x_14228__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14228__boxed_667_, v_x_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
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
lean_object* v_toCold_688_; lean_object* v_options_689_; lean_object* v_inheritedTraceOptions_690_; uint8_t v_hasTrace_691_; lean_object* v___y_693_; 
v_toCold_688_ = lean_ctor_get(v___y_685_, 0);
v_options_689_ = lean_ctor_get(v_toCold_688_, 2);
v_inheritedTraceOptions_690_ = lean_ctor_get(v_toCold_688_, 11);
v_hasTrace_691_ = lean_ctor_get_uint8(v_options_689_, sizeof(void*)*1);
if (v_hasTrace_691_ == 0)
{
lean_object* v___x_714_; uint8_t v_transparency_715_; uint8_t v___x_716_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v___x_714_ = l_Lean_Meta_Context_config(v___y_683_);
v_transparency_715_ = lean_ctor_get_uint8(v___x_714_, 9);
lean_dec_ref(v___x_714_);
v___x_716_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_715_, v_transparency_674_);
if (v___x_716_ == 0)
{
lean_object* v_keyedConfig_717_; uint8_t v_trackZetaDelta_718_; lean_object* v_zetaDeltaSet_719_; lean_object* v_lctx_720_; lean_object* v_localInstances_721_; lean_object* v_defEqCtx_x3f_722_; lean_object* v_synthPendingDepth_723_; lean_object* v_customCanUnfoldPredicate_x3f_724_; uint8_t v_univApprox_725_; uint8_t v_inTypeClassResolution_726_; uint8_t v_cacheInferType_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_keyedConfig_717_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_718_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_719_ = lean_ctor_get(v___y_683_, 1);
v_lctx_720_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_721_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_722_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_723_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_724_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_725_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_726_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_727_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_717_);
v___x_728_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_717_);
lean_inc(v_customCanUnfoldPredicate_x3f_724_);
lean_inc(v_synthPendingDepth_723_);
lean_inc(v_defEqCtx_x3f_722_);
lean_inc_ref(v_localInstances_721_);
lean_inc_ref(v_lctx_720_);
lean_inc(v_zetaDeltaSet_719_);
v___x_729_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_zetaDeltaSet_719_);
lean_ctor_set(v___x_729_, 2, v_lctx_720_);
lean_ctor_set(v___x_729_, 3, v_localInstances_721_);
lean_ctor_set(v___x_729_, 4, v_defEqCtx_x3f_722_);
lean_ctor_set(v___x_729_, 5, v_synthPendingDepth_723_);
lean_ctor_set(v___x_729_, 6, v_customCanUnfoldPredicate_x3f_724_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*7, v_trackZetaDelta_718_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*7 + 1, v_univApprox_725_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*7 + 2, v_inTypeClassResolution_726_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*7 + 3, v_cacheInferType_727_);
v___x_730_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_729_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_729_, 7);
v___y_693_ = v___x_730_;
goto v___jp_692_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v___y_693_ = v___x_731_;
goto v___jp_692_;
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v_a_738_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v_a_753_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v_a_777_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v_a_789_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; 
v___x_732_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_679_);
v___x_733_ = l_Lean_Name_append(v___x_732_, v___x_679_);
v___x_734_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_690_, v_options_689_, v___x_733_);
lean_dec(v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___y_856_; 
v___x_853_ = l_Lean_trace_profiler;
v___x_854_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_689_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_877_; uint8_t v_transparency_878_; uint8_t v___x_879_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v___x_877_ = l_Lean_Meta_Context_config(v___y_683_);
v_transparency_878_ = lean_ctor_get_uint8(v___x_877_, 9);
lean_dec_ref(v___x_877_);
v___x_879_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_878_, v_transparency_674_);
if (v___x_879_ == 0)
{
lean_object* v_keyedConfig_880_; uint8_t v_trackZetaDelta_881_; lean_object* v_zetaDeltaSet_882_; lean_object* v_lctx_883_; lean_object* v_localInstances_884_; lean_object* v_defEqCtx_x3f_885_; lean_object* v_synthPendingDepth_886_; lean_object* v_customCanUnfoldPredicate_x3f_887_; uint8_t v_univApprox_888_; uint8_t v_inTypeClassResolution_889_; uint8_t v_cacheInferType_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_keyedConfig_880_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_881_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_882_ = lean_ctor_get(v___y_683_, 1);
v_lctx_883_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_884_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_885_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_886_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_887_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_888_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_889_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_890_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_880_);
v___x_891_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_880_);
lean_inc(v_customCanUnfoldPredicate_x3f_887_);
lean_inc(v_synthPendingDepth_886_);
lean_inc(v_defEqCtx_x3f_885_);
lean_inc_ref(v_localInstances_884_);
lean_inc_ref(v_lctx_883_);
lean_inc(v_zetaDeltaSet_882_);
v___x_892_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v_zetaDeltaSet_882_);
lean_ctor_set(v___x_892_, 2, v_lctx_883_);
lean_ctor_set(v___x_892_, 3, v_localInstances_884_);
lean_ctor_set(v___x_892_, 4, v_defEqCtx_x3f_885_);
lean_ctor_set(v___x_892_, 5, v_synthPendingDepth_886_);
lean_ctor_set(v___x_892_, 6, v_customCanUnfoldPredicate_x3f_887_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*7, v_trackZetaDelta_881_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*7 + 1, v_univApprox_888_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*7 + 2, v_inTypeClassResolution_889_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*7 + 3, v_cacheInferType_890_);
v___x_893_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_892_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_892_, 7);
v___y_856_ = v___x_893_;
goto v___jp_855_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v___y_856_ = v___x_894_;
goto v___jp_855_;
}
}
else
{
goto v___jp_810_;
}
v___jp_855_:
{
if (lean_obj_tag(v___y_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_857_ = lean_ctor_get(v___y_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___y_856_, 1);
v___x_858_ = lean_box(0);
v___x_859_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_854_, v_hasTrace_691_, v_a_857_, v___x_858_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = l_List_reverse___redArg(v_a_860_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
return v___x_859_;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v___y_683_);
v_a_869_ = lean_ctor_get(v___y_856_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___y_856_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___y_856_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___y_856_);
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
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
goto v___jp_810_;
}
v___jp_735_:
{
lean_object* v___x_739_; double v___x_740_; double v___x_741_; double v___x_742_; double v___x_743_; double v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_739_ = lean_io_mono_nanos_now();
v___x_740_ = lean_float_of_nat(v___y_736_);
v___x_741_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_742_ = lean_float_div(v___x_740_, v___x_741_);
v___x_743_ = lean_float_of_nat(v___x_739_);
v___x_744_ = lean_float_div(v___x_743_, v___x_741_);
v___x_745_ = lean_box_float(v___x_742_);
v___x_746_ = lean_box_float(v___x_744_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_a_738_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_689_, v___x_734_, v___y_737_, v___f_682_, v___x_748_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
return v___x_749_;
}
v___jp_750_:
{
lean_object* v___x_754_; 
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_a_753_);
v___y_736_ = v___y_751_;
v___y_737_ = v___y_752_;
v_a_738_ = v___x_754_;
goto v___jp_735_;
}
v___jp_755_:
{
if (lean_obj_tag(v___y_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___y_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___y_759_, 1);
v___x_761_ = lean_box(0);
v___x_762_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_756_, v_hasTrace_691_, v_a_760_, v___x_761_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = l_List_reverse___redArg(v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v_a_738_ = v___x_769_;
goto v___jp_735_;
}
}
}
else
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_762_, 1);
v___y_751_ = v___y_757_;
v___y_752_ = v___y_758_;
v_a_753_ = v_a_772_;
goto v___jp_750_;
}
}
else
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___y_759_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___y_759_, 1);
v___y_751_ = v___y_757_;
v___y_752_ = v___y_758_;
v_a_753_ = v_a_773_;
goto v___jp_750_;
}
}
v___jp_774_:
{
lean_object* v___x_778_; double v___x_779_; double v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_778_ = lean_io_get_num_heartbeats();
v___x_779_ = lean_float_of_nat(v___y_775_);
v___x_780_ = lean_float_of_nat(v___x_778_);
v___x_781_ = lean_box_float(v___x_779_);
v___x_782_ = lean_box_float(v___x_780_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_777_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_689_, v___x_734_, v___y_776_, v___f_682_, v___x_784_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
return v___x_785_;
}
v___jp_786_:
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_a_789_);
v___y_775_ = v___y_787_;
v___y_776_ = v___y_788_;
v_a_777_ = v___x_790_;
goto v___jp_774_;
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
v___x_798_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_792_, v_a_796_, v___x_797_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_807_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = l_List_reverse___redArg(v_a_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v___y_775_ = v___y_793_;
v___y_776_ = v___y_794_;
v_a_777_ = v___x_805_;
goto v___jp_774_;
}
}
}
else
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_798_, 1);
v___y_787_ = v___y_793_;
v___y_788_ = v___y_794_;
v_a_789_ = v_a_808_;
goto v___jp_786_;
}
}
else
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___y_795_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___y_795_, 1);
v___y_787_ = v___y_793_;
v___y_788_ = v___y_794_;
v_a_789_ = v_a_809_;
goto v___jp_786_;
}
}
v___jp_810_:
{
lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_811_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_686_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = l_Lean_trace_profiler_useHeartbeats;
v___x_814_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_689_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v_transparency_817_; uint8_t v___x_818_; 
v___x_815_ = lean_io_mono_nanos_now();
v___x_816_ = l_Lean_Meta_Context_config(v___y_683_);
v_transparency_817_ = lean_ctor_get_uint8(v___x_816_, 9);
lean_dec_ref(v___x_816_);
v___x_818_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_817_, v_transparency_674_);
if (v___x_818_ == 0)
{
lean_object* v_keyedConfig_819_; uint8_t v_trackZetaDelta_820_; lean_object* v_zetaDeltaSet_821_; lean_object* v_lctx_822_; lean_object* v_localInstances_823_; lean_object* v_defEqCtx_x3f_824_; lean_object* v_synthPendingDepth_825_; lean_object* v_customCanUnfoldPredicate_x3f_826_; uint8_t v_univApprox_827_; uint8_t v_inTypeClassResolution_828_; uint8_t v_cacheInferType_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_keyedConfig_819_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_820_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_821_ = lean_ctor_get(v___y_683_, 1);
v_lctx_822_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_823_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_824_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_825_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_826_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_827_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_828_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_829_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_819_);
v___x_830_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_819_);
lean_inc(v_customCanUnfoldPredicate_x3f_826_);
lean_inc(v_synthPendingDepth_825_);
lean_inc(v_defEqCtx_x3f_824_);
lean_inc_ref(v_localInstances_823_);
lean_inc_ref(v_lctx_822_);
lean_inc(v_zetaDeltaSet_821_);
v___x_831_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_zetaDeltaSet_821_);
lean_ctor_set(v___x_831_, 2, v_lctx_822_);
lean_ctor_set(v___x_831_, 3, v_localInstances_823_);
lean_ctor_set(v___x_831_, 4, v_defEqCtx_x3f_824_);
lean_ctor_set(v___x_831_, 5, v_synthPendingDepth_825_);
lean_ctor_set(v___x_831_, 6, v_customCanUnfoldPredicate_x3f_826_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*7, v_trackZetaDelta_820_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*7 + 1, v_univApprox_827_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*7 + 2, v_inTypeClassResolution_828_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*7 + 3, v_cacheInferType_829_);
v___x_832_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_831_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_831_, 7);
v___y_756_ = v___x_814_;
v___y_757_ = v___x_815_;
v___y_758_ = v_a_812_;
v___y_759_ = v___x_832_;
goto v___jp_755_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v___y_756_ = v___x_814_;
v___y_757_ = v___x_815_;
v___y_758_ = v_a_812_;
v___y_759_ = v___x_833_;
goto v___jp_755_;
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v_transparency_836_; uint8_t v___x_837_; 
v___x_834_ = lean_io_get_num_heartbeats();
v___x_835_ = l_Lean_Meta_Context_config(v___y_683_);
v_transparency_836_ = lean_ctor_get_uint8(v___x_835_, 9);
lean_dec_ref(v___x_835_);
v___x_837_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_836_, v_transparency_674_);
if (v___x_837_ == 0)
{
lean_object* v_keyedConfig_838_; uint8_t v_trackZetaDelta_839_; lean_object* v_zetaDeltaSet_840_; lean_object* v_lctx_841_; lean_object* v_localInstances_842_; lean_object* v_defEqCtx_x3f_843_; lean_object* v_synthPendingDepth_844_; lean_object* v_customCanUnfoldPredicate_x3f_845_; uint8_t v_univApprox_846_; uint8_t v_inTypeClassResolution_847_; uint8_t v_cacheInferType_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_keyedConfig_838_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_839_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_840_ = lean_ctor_get(v___y_683_, 1);
v_lctx_841_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_842_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_843_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_844_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_845_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_846_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_847_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_848_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_838_);
v___x_849_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_838_);
lean_inc(v_customCanUnfoldPredicate_x3f_845_);
lean_inc(v_synthPendingDepth_844_);
lean_inc(v_defEqCtx_x3f_843_);
lean_inc_ref(v_localInstances_842_);
lean_inc_ref(v_lctx_841_);
lean_inc(v_zetaDeltaSet_840_);
v___x_850_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v_zetaDeltaSet_840_);
lean_ctor_set(v___x_850_, 2, v_lctx_841_);
lean_ctor_set(v___x_850_, 3, v_localInstances_842_);
lean_ctor_set(v___x_850_, 4, v_defEqCtx_x3f_843_);
lean_ctor_set(v___x_850_, 5, v_synthPendingDepth_844_);
lean_ctor_set(v___x_850_, 6, v_customCanUnfoldPredicate_x3f_845_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*7, v_trackZetaDelta_839_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*7 + 1, v_univApprox_846_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*7 + 2, v_inTypeClassResolution_847_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*7 + 3, v_cacheInferType_848_);
v___x_851_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_850_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_850_, 7);
v___y_792_ = v___x_814_;
v___y_793_ = v___x_834_;
v___y_794_ = v_a_812_;
v___y_795_ = v___x_851_;
goto v___jp_791_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
v___y_792_ = v___x_814_;
v___y_793_ = v___x_834_;
v___y_794_ = v_a_812_;
v___y_795_ = v___x_852_;
goto v___jp_791_;
}
}
}
}
v___jp_692_:
{
if (lean_obj_tag(v___y_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___y_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___y_693_, 1);
v___x_695_ = lean_box(0);
v___x_696_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_691_, v_a_694_, v___x_695_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = l_List_reverse___redArg(v_a_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
return v___x_696_;
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___y_683_);
v_a_706_ = lean_ctor_get(v___y_693_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___y_693_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___y_693_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___y_693_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_895_, lean_object* v_g_896_, lean_object* v_e_897_, lean_object* v_cfg_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___f_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
uint8_t v_transparency_boxed_909_; uint8_t v___x_14318__boxed_910_; lean_object* v_res_911_; 
v_transparency_boxed_909_ = lean_unbox(v_transparency_895_);
v___x_14318__boxed_910_ = lean_unbox(v___x_901_);
v_res_911_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_909_, v_g_896_, v_e_897_, v_cfg_898_, v___x_899_, v___x_900_, v___x_14318__boxed_910_, v___x_902_, v___f_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_913_, lean_object* v_g_914_, lean_object* v_cfg_915_, lean_object* v_e_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___f_929_; lean_object* v___x_930_; 
lean_inc_ref(v_e_916_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_922_, 0, v_e_916_);
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_924_ = lean_box(0);
v___x_925_ = 1;
v___x_926_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_927_ = lean_box(v_transparency_913_);
v___x_928_ = lean_box(v___x_925_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_929_, 0, v___x_927_);
lean_closure_set(v___f_929_, 1, v_g_914_);
lean_closure_set(v___f_929_, 2, v_e_916_);
lean_closure_set(v___f_929_, 3, v_cfg_915_);
lean_closure_set(v___f_929_, 4, v___x_924_);
lean_closure_set(v___f_929_, 5, v___x_923_);
lean_closure_set(v___f_929_, 6, v___x_928_);
lean_closure_set(v___f_929_, 7, v___x_926_);
lean_closure_set(v___f_929_, 8, v___f_922_);
v___x_930_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_929_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_931_, lean_object* v_g_932_, lean_object* v_cfg_933_, lean_object* v_e_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v_transparency_boxed_940_; lean_object* v_res_941_; 
v_transparency_boxed_940_ = lean_unbox(v_transparency_931_);
v_res_941_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_940_, v_g_932_, v_cfg_933_, v_e_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_942_, uint8_t v_transparency_943_, lean_object* v_lemmas_944_, lean_object* v_g_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(v_transparency_943_);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_950_, 0, v___x_949_);
lean_closure_set(v___f_950_, 1, v_g_945_);
lean_closure_set(v___f_950_, 2, v_cfg_942_);
v___x_951_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_944_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_960_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_956_, 0, lean_box(0));
lean_closure_set(v___x_956_, 1, lean_box(0));
lean_closure_set(v___x_956_, 2, v___f_950_);
lean_closure_set(v___x_956_, 3, v_a_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v___f_950_);
v_a_961_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_951_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_951_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_969_, lean_object* v_transparency_970_, lean_object* v_lemmas_971_, lean_object* v_g_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
uint8_t v_transparency_boxed_976_; lean_object* v_res_977_; 
v_transparency_boxed_976_ = lean_unbox(v_transparency_970_);
v_res_977_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_969_, v_transparency_boxed_976_, v_lemmas_971_, v_g_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec(v_a_973_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_978_, uint8_t v_transparency_979_, lean_object* v_lemmas_980_, lean_object* v_g_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_978_, v_transparency_979_, v_lemmas_980_, v_g_981_, v_a_983_, v_a_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_988_, lean_object* v_transparency_989_, lean_object* v_lemmas_990_, lean_object* v_g_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
uint8_t v_transparency_boxed_997_; lean_object* v_res_998_; 
v_transparency_boxed_997_ = lean_unbox(v_transparency_989_);
v_res_998_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_988_, v_transparency_boxed_997_, v_lemmas_990_, v_g_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_1000_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1015_, uint8_t v_transparency_1016_, lean_object* v_lemmas_1017_, lean_object* v_g_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1015_, v_transparency_1016_, v_lemmas_1017_, v_g_1018_, v_a_1020_, v_a_1022_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l_Lean_Meta_Iterator_head___redArg(v_a_1025_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1026_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1024_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1024_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1035_, lean_object* v_transparency_1036_, lean_object* v_lemmas_1037_, lean_object* v_g_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
uint8_t v_transparency_boxed_1044_; lean_object* v_res_1045_; 
v_transparency_boxed_1044_ = lean_unbox(v_transparency_1036_);
v_res_1045_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1035_, v_transparency_boxed_1044_, v_lemmas_1037_, v_g_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1046_){
_start:
{
lean_object* v_toApplyRulesConfig_1047_; lean_object* v_toBacktrackConfig_1048_; 
v_toApplyRulesConfig_1047_ = lean_ctor_get(v_x_1046_, 0);
v_toBacktrackConfig_1048_ = lean_ctor_get(v_toApplyRulesConfig_1047_, 0);
lean_inc_ref(v_toBacktrackConfig_1048_);
return v_toBacktrackConfig_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1049_);
lean_dec_ref(v_x_1049_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1053_, lean_object* v_discharge_1054_, lean_object* v_g_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v_g_1055_);
v___x_1061_ = lean_apply_6(v_test_1053_, v_g_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1072_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1072_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1072_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_unbox(v_a_1062_);
lean_dec(v_a_1062_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_del_object(v___x_1064_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
v___x_1067_ = lean_apply_6(v_discharge_1054_, v_g_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, lean_box(0));
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec(v_g_1055_);
lean_dec_ref(v_discharge_1054_);
v___x_1068_ = lean_box(0);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1068_);
v___x_1070_ = v___x_1064_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
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
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_g_1055_);
lean_dec_ref(v_discharge_1054_);
v_a_1073_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1061_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1061_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1081_, lean_object* v_discharge_1082_, lean_object* v_g_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1081_, v_discharge_1082_, v_g_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1090_, lean_object* v_test_1091_){
_start:
{
lean_object* v_toApplyRulesConfig_1092_; lean_object* v_toBacktrackConfig_1093_; uint8_t v_backtracking_1094_; uint8_t v_intro_1095_; uint8_t v_constructor_1096_; uint8_t v_suggestions_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1129_; 
v_toApplyRulesConfig_1092_ = lean_ctor_get(v_cfg_1090_, 0);
lean_inc_ref(v_toApplyRulesConfig_1092_);
v_toBacktrackConfig_1093_ = lean_ctor_get(v_toApplyRulesConfig_1092_, 0);
lean_inc_ref(v_toBacktrackConfig_1093_);
v_backtracking_1094_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*1);
v_intro_1095_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*1 + 1);
v_constructor_1096_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*1 + 2);
v_suggestions_1097_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*1 + 3);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_cfg_1090_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v_cfg_1090_, 0);
lean_dec(v_unused_1130_);
v___x_1099_ = v_cfg_1090_;
v_isShared_1100_ = v_isSharedCheck_1129_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v_cfg_1090_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1129_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_toApplyConfig_1101_; uint8_t v_transparency_1102_; uint8_t v_symm_1103_; uint8_t v_exfalso_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1127_; 
v_toApplyConfig_1101_ = lean_ctor_get(v_toApplyRulesConfig_1092_, 1);
v_transparency_1102_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1092_, sizeof(void*)*2);
v_symm_1103_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1092_, sizeof(void*)*2 + 1);
v_exfalso_1104_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1092_, sizeof(void*)*2 + 2);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_toApplyRulesConfig_1092_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_toApplyRulesConfig_1092_, 0);
lean_dec(v_unused_1128_);
v___x_1106_ = v_toApplyRulesConfig_1092_;
v_isShared_1107_ = v_isSharedCheck_1127_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_toApplyConfig_1101_);
lean_dec(v_toApplyRulesConfig_1092_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1127_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_maxDepth_1108_; lean_object* v_proc_1109_; lean_object* v_suspend_1110_; lean_object* v_discharge_1111_; uint8_t v_commitIndependentGoals_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1126_; 
v_maxDepth_1108_ = lean_ctor_get(v_toBacktrackConfig_1093_, 0);
v_proc_1109_ = lean_ctor_get(v_toBacktrackConfig_1093_, 1);
v_suspend_1110_ = lean_ctor_get(v_toBacktrackConfig_1093_, 2);
v_discharge_1111_ = lean_ctor_get(v_toBacktrackConfig_1093_, 3);
v_commitIndependentGoals_1112_ = lean_ctor_get_uint8(v_toBacktrackConfig_1093_, sizeof(void*)*4);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_toBacktrackConfig_1093_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1114_ = v_toBacktrackConfig_1093_;
v_isShared_1115_ = v_isSharedCheck_1126_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_discharge_1111_);
lean_inc(v_suspend_1110_);
lean_inc(v_proc_1109_);
lean_inc(v_maxDepth_1108_);
lean_dec(v_toBacktrackConfig_1093_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1126_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___f_1116_; lean_object* v___x_1118_; 
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1116_, 0, v_test_1091_);
lean_closure_set(v___f_1116_, 1, v_discharge_1111_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 3, v___f_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_maxDepth_1108_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_proc_1109_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_suspend_1110_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v___f_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*4, v_commitIndependentGoals_1112_);
v___x_1118_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1118_);
v___x_1120_ = v___x_1106_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_toApplyConfig_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*2, v_transparency_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*2 + 1, v_symm_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*2 + 2, v_exfalso_1104_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1120_);
v___x_1122_ = v___x_1099_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1123_, sizeof(void*)*1, v_backtracking_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1123_, sizeof(void*)*1 + 1, v_intro_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1123_, sizeof(void*)*1 + 2, v_constructor_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1123_, sizeof(void*)*1 + 3, v_suggestions_1097_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1131_, lean_object* v_proc_1132_, lean_object* v_orig_1133_, lean_object* v_goals_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
if (lean_obj_tag(v_goals_1134_) == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v_proc_1132_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
v___x_1140_ = lean_apply_7(v_proc_1131_, v_orig_1133_, v_goals_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1140_;
}
else
{
lean_object* v_head_1141_; lean_object* v_tail_1142_; lean_object* v___x_1143_; 
v_head_1141_ = lean_ctor_get(v_goals_1134_, 0);
v_tail_1142_ = lean_ctor_get(v_goals_1134_, 1);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v_head_1141_);
v___x_1143_ = lean_apply_6(v_proc_1132_, v_head_1141_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1153_; 
lean_inc(v_tail_1142_);
lean_dec_ref_known(v_goals_1134_, 2);
lean_dec(v_orig_1133_);
lean_dec_ref(v_proc_1131_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1153_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1153_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = l_List_appendTR___redArg(v_a_1144_, v_tail_1142_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1167_; 
v_a_1154_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1156_ = v___x_1143_;
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1143_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = l_Lean_Exception_isInterrupt(v_a_1154_);
if (v___x_1158_ == 0)
{
uint8_t v___x_1159_; 
lean_inc(v_a_1154_);
v___x_1159_ = l_Lean_Exception_isRuntime(v_a_1154_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_del_object(v___x_1156_);
lean_dec(v_a_1154_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
v___x_1160_ = lean_apply_7(v_proc_1131_, v_orig_1133_, v_goals_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1160_;
}
else
{
lean_object* v___x_1162_; 
lean_dec_ref_known(v_goals_1134_, 2);
lean_dec(v_orig_1133_);
lean_dec_ref(v_proc_1131_);
if (v_isShared_1157_ == 0)
{
v___x_1162_ = v___x_1156_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1154_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v___x_1165_; 
lean_dec_ref_known(v_goals_1134_, 2);
lean_dec(v_orig_1133_);
lean_dec_ref(v_proc_1131_);
if (v_isShared_1157_ == 0)
{
v___x_1165_ = v___x_1156_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1154_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1168_, lean_object* v_proc_1169_, lean_object* v_orig_1170_, lean_object* v_goals_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1168_, v_proc_1169_, v_orig_1170_, v_goals_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1178_, lean_object* v_proc_1179_){
_start:
{
lean_object* v_toApplyRulesConfig_1180_; lean_object* v_toBacktrackConfig_1181_; uint8_t v_backtracking_1182_; uint8_t v_intro_1183_; uint8_t v_constructor_1184_; uint8_t v_suggestions_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1217_; 
v_toApplyRulesConfig_1180_ = lean_ctor_get(v_cfg_1178_, 0);
lean_inc_ref(v_toApplyRulesConfig_1180_);
v_toBacktrackConfig_1181_ = lean_ctor_get(v_toApplyRulesConfig_1180_, 0);
lean_inc_ref(v_toBacktrackConfig_1181_);
v_backtracking_1182_ = lean_ctor_get_uint8(v_cfg_1178_, sizeof(void*)*1);
v_intro_1183_ = lean_ctor_get_uint8(v_cfg_1178_, sizeof(void*)*1 + 1);
v_constructor_1184_ = lean_ctor_get_uint8(v_cfg_1178_, sizeof(void*)*1 + 2);
v_suggestions_1185_ = lean_ctor_get_uint8(v_cfg_1178_, sizeof(void*)*1 + 3);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_cfg_1178_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_cfg_1178_, 0);
lean_dec(v_unused_1218_);
v___x_1187_ = v_cfg_1178_;
v_isShared_1188_ = v_isSharedCheck_1217_;
goto v_resetjp_1186_;
}
else
{
lean_dec(v_cfg_1178_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1217_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_toApplyConfig_1189_; uint8_t v_transparency_1190_; uint8_t v_symm_1191_; uint8_t v_exfalso_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1215_; 
v_toApplyConfig_1189_ = lean_ctor_get(v_toApplyRulesConfig_1180_, 1);
v_transparency_1190_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1180_, sizeof(void*)*2);
v_symm_1191_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1180_, sizeof(void*)*2 + 1);
v_exfalso_1192_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1180_, sizeof(void*)*2 + 2);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_toApplyRulesConfig_1180_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_toApplyRulesConfig_1180_, 0);
lean_dec(v_unused_1216_);
v___x_1194_ = v_toApplyRulesConfig_1180_;
v_isShared_1195_ = v_isSharedCheck_1215_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_toApplyConfig_1189_);
lean_dec(v_toApplyRulesConfig_1180_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1215_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_maxDepth_1196_; lean_object* v_proc_1197_; lean_object* v_suspend_1198_; lean_object* v_discharge_1199_; uint8_t v_commitIndependentGoals_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1214_; 
v_maxDepth_1196_ = lean_ctor_get(v_toBacktrackConfig_1181_, 0);
v_proc_1197_ = lean_ctor_get(v_toBacktrackConfig_1181_, 1);
v_suspend_1198_ = lean_ctor_get(v_toBacktrackConfig_1181_, 2);
v_discharge_1199_ = lean_ctor_get(v_toBacktrackConfig_1181_, 3);
v_commitIndependentGoals_1200_ = lean_ctor_get_uint8(v_toBacktrackConfig_1181_, sizeof(void*)*4);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_toBacktrackConfig_1181_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1202_ = v_toBacktrackConfig_1181_;
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_discharge_1199_);
lean_inc(v_suspend_1198_);
lean_inc(v_proc_1197_);
lean_inc(v_maxDepth_1196_);
lean_dec(v_toBacktrackConfig_1181_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___f_1204_; lean_object* v___x_1206_; 
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1204_, 0, v_proc_1197_);
lean_closure_set(v___f_1204_, 1, v_proc_1179_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___f_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_maxDepth_1196_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_suspend_1198_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_discharge_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*4, v_commitIndependentGoals_1200_);
v___x_1206_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1206_);
v___x_1208_ = v___x_1194_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_toApplyConfig_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*2, v_transparency_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*2 + 1, v_symm_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*2 + 2, v_exfalso_1192_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1208_);
v___x_1210_ = v___x_1187_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*1, v_backtracking_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*1 + 1, v_intro_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*1 + 2, v_constructor_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*1 + 3, v_suggestions_1185_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = 1;
v___x_1226_ = l_Lean_Meta_intro1Core(v_g_1219_, v___x_1225_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1244_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1244_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1244_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1242_; 
v_snd_1231_ = lean_ctor_get(v_a_1227_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_a_1227_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_a_1227_, 0);
lean_dec(v_unused_1243_);
v___x_1233_ = v_a_1227_;
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_dec(v_a_1227_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_box(0);
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 1);
lean_ctor_set(v___x_1233_, 1, v___x_1235_);
lean_ctor_set(v___x_1233_, 0, v_snd_1231_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_snd_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1237_);
v___x_1239_ = v___x_1229_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1226_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1226_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1261_){
_start:
{
lean_object* v___f_1262_; lean_object* v___x_1263_; 
v___f_1262_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1263_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1261_, v___f_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v_ks_1268_; lean_object* v_vs_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1293_; 
v_ks_1268_ = lean_ctor_get(v_x_1264_, 0);
v_vs_1269_ = lean_ctor_get(v_x_1264_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1271_ = v_x_1264_;
v_isShared_1272_ = v_isSharedCheck_1293_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_vs_1269_);
lean_inc(v_ks_1268_);
lean_dec(v_x_1264_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1293_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_array_get_size(v_ks_1268_);
v___x_1274_ = lean_nat_dec_lt(v_x_1265_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_dec(v_x_1265_);
v___x_1275_ = lean_array_push(v_ks_1268_, v_x_1266_);
v___x_1276_ = lean_array_push(v_vs_1269_, v_x_1267_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1276_);
lean_ctor_set(v___x_1271_, 0, v___x_1275_);
v___x_1278_ = v___x_1271_;
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
else
{
lean_object* v_k_x27_1280_; uint8_t v___x_1281_; 
v_k_x27_1280_ = lean_array_fget_borrowed(v_ks_1268_, v_x_1265_);
v___x_1281_ = l_Lean_instBEqMVarId_beq(v_x_1266_, v_k_x27_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1283_; 
if (v_isShared_1272_ == 0)
{
v___x_1283_ = v___x_1271_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_ks_1268_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_vs_1269_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_nat_add(v_x_1265_, v___x_1284_);
lean_dec(v_x_1265_);
v_x_1264_ = v___x_1283_;
v_x_1265_ = v___x_1285_;
goto _start;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1288_ = lean_array_fset(v_ks_1268_, v_x_1265_, v_x_1266_);
v___x_1289_ = lean_array_fset(v_vs_1269_, v_x_1265_, v_x_1267_);
lean_dec(v_x_1265_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1289_);
lean_ctor_set(v___x_1271_, 0, v___x_1288_);
v___x_1291_ = v___x_1271_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1294_, lean_object* v_k_1295_, lean_object* v_v_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1294_, v___x_1297_, v_k_1295_, v_v_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1300_, size_t v_x_1301_, size_t v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
lean_object* v_es_1305_; size_t v___x_1306_; size_t v___x_1307_; lean_object* v_j_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_es_1305_ = lean_ctor_get(v_x_1300_, 0);
v___x_1306_ = ((size_t)31ULL);
v___x_1307_ = lean_usize_land(v_x_1301_, v___x_1306_);
v_j_1308_ = lean_usize_to_nat(v___x_1307_);
v___x_1309_ = lean_array_get_size(v_es_1305_);
v___x_1310_ = lean_nat_dec_lt(v_j_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec(v_j_1308_);
lean_dec(v_x_1304_);
lean_dec(v_x_1303_);
return v_x_1300_;
}
else
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1349_; 
lean_inc_ref(v_es_1305_);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_x_1300_, 0);
lean_dec(v_unused_1350_);
v___x_1312_ = v_x_1300_;
v_isShared_1313_ = v_isSharedCheck_1349_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_x_1300_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1349_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_v_1314_; lean_object* v___x_1315_; lean_object* v_xs_x27_1316_; lean_object* v___y_1318_; 
v_v_1314_ = lean_array_fget(v_es_1305_, v_j_1308_);
v___x_1315_ = lean_box(0);
v_xs_x27_1316_ = lean_array_fset(v_es_1305_, v_j_1308_, v___x_1315_);
switch(lean_obj_tag(v_v_1314_))
{
case 0:
{
lean_object* v_key_1323_; lean_object* v_val_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1334_; 
v_key_1323_ = lean_ctor_get(v_v_1314_, 0);
v_val_1324_ = lean_ctor_get(v_v_1314_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_v_1314_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1326_ = v_v_1314_;
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_val_1324_);
lean_inc(v_key_1323_);
lean_dec(v_v_1314_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_instBEqMVarId_beq(v_x_1303_, v_key_1323_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_del_object(v___x_1326_);
v___x_1329_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1323_, v_val_1324_, v_x_1303_, v_x_1304_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
v___y_1318_ = v___x_1330_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1332_; 
lean_dec(v_val_1324_);
lean_dec(v_key_1323_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_x_1304_);
lean_ctor_set(v___x_1326_, 0, v_x_1303_);
v___x_1332_ = v___x_1326_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_x_1303_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_x_1304_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
v___y_1318_ = v___x_1332_;
goto v___jp_1317_;
}
}
}
}
case 1:
{
lean_object* v_node_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1347_; 
v_node_1335_ = lean_ctor_get(v_v_1314_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_v_1314_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1337_ = v_v_1314_;
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_node_1335_);
lean_dec(v_v_1314_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1339_ = ((size_t)5ULL);
v___x_1340_ = lean_usize_shift_right(v_x_1301_, v___x_1339_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_x_1302_, v___x_1341_);
v___x_1343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1335_, v___x_1340_, v___x_1342_, v_x_1303_, v_x_1304_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1343_);
v___x_1345_ = v___x_1337_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
v___y_1318_ = v___x_1345_;
goto v___jp_1317_;
}
}
}
default: 
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_x_1303_);
lean_ctor_set(v___x_1348_, 1, v_x_1304_);
v___y_1318_ = v___x_1348_;
goto v___jp_1317_;
}
}
v___jp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_array_fset(v_xs_x27_1316_, v_j_1308_, v___y_1318_);
lean_dec(v_j_1308_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1319_);
v___x_1321_ = v___x_1312_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_ks_1351_; lean_object* v_vs_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1370_; 
v_ks_1351_ = lean_ctor_get(v_x_1300_, 0);
v_vs_1352_ = lean_ctor_get(v_x_1300_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1354_ = v_x_1300_;
v_isShared_1355_ = v_isSharedCheck_1370_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_vs_1352_);
lean_inc(v_ks_1351_);
lean_dec(v_x_1300_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1370_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_ks_1351_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_vs_1352_);
v___x_1357_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v_newNode_1358_; size_t v___x_1359_; uint8_t v___x_1360_; 
v_newNode_1358_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1357_, v_x_1303_, v_x_1304_);
v___x_1359_ = ((size_t)7ULL);
v___x_1360_ = lean_usize_dec_le(v___x_1359_, v_x_1302_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1358_);
v___x_1362_ = lean_unsigned_to_nat(4u);
v___x_1363_ = lean_nat_dec_lt(v___x_1361_, v___x_1362_);
lean_dec(v___x_1361_);
if (v___x_1363_ == 0)
{
lean_object* v_ks_1364_; lean_object* v_vs_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_ks_1364_ = lean_ctor_get(v_newNode_1358_, 0);
lean_inc_ref(v_ks_1364_);
v_vs_1365_ = lean_ctor_get(v_newNode_1358_, 1);
lean_inc_ref(v_vs_1365_);
lean_dec_ref(v_newNode_1358_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1302_, v_ks_1364_, v_vs_1365_, v___x_1366_, v___x_1367_);
lean_dec_ref(v_vs_1365_);
lean_dec_ref(v_ks_1364_);
return v___x_1368_;
}
else
{
return v_newNode_1358_;
}
}
else
{
return v_newNode_1358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_i_1374_, lean_object* v_entries_1375_){
_start:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = lean_array_get_size(v_keys_1372_);
v___x_1377_ = lean_nat_dec_lt(v_i_1374_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec(v_i_1374_);
return v_entries_1375_;
}
else
{
lean_object* v_k_1378_; lean_object* v_v_1379_; uint64_t v___x_1380_; size_t v_h_1381_; size_t v___x_1382_; lean_object* v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v_h_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_k_1378_ = lean_array_fget_borrowed(v_keys_1372_, v_i_1374_);
v_v_1379_ = lean_array_fget_borrowed(v_vals_1373_, v_i_1374_);
v___x_1380_ = l_Lean_instHashableMVarId_hash(v_k_1378_);
v_h_1381_ = lean_uint64_to_usize(v___x_1380_);
v___x_1382_ = ((size_t)5ULL);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_sub(v_depth_1371_, v___x_1384_);
v___x_1386_ = lean_usize_mul(v___x_1382_, v___x_1385_);
v_h_1387_ = lean_usize_shift_right(v_h_1381_, v___x_1386_);
v___x_1388_ = lean_nat_add(v_i_1374_, v___x_1383_);
lean_dec(v_i_1374_);
lean_inc(v_v_1379_);
lean_inc(v_k_1378_);
v___x_1389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1375_, v_h_1387_, v_depth_1371_, v_k_1378_, v_v_1379_);
v_i_1374_ = v___x_1388_;
v_entries_1375_ = v___x_1389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1391_, lean_object* v_keys_1392_, lean_object* v_vals_1393_, lean_object* v_i_1394_, lean_object* v_entries_1395_){
_start:
{
size_t v_depth_boxed_1396_; lean_object* v_res_1397_; 
v_depth_boxed_1396_ = lean_unbox_usize(v_depth_1391_);
lean_dec(v_depth_1391_);
v_res_1397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1396_, v_keys_1392_, v_vals_1393_, v_i_1394_, v_entries_1395_);
lean_dec_ref(v_vals_1393_);
lean_dec_ref(v_keys_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v_x_1402_){
_start:
{
size_t v_x_839__boxed_1403_; size_t v_x_840__boxed_1404_; lean_object* v_res_1405_; 
v_x_839__boxed_1403_ = lean_unbox_usize(v_x_1399_);
lean_dec(v_x_1399_);
v_x_840__boxed_1404_ = lean_unbox_usize(v_x_1400_);
lean_dec(v_x_1400_);
v_res_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1398_, v_x_839__boxed_1403_, v_x_840__boxed_1404_, v_x_1401_, v_x_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
uint64_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = l_Lean_instHashableMVarId_hash(v_x_1407_);
v___x_1410_ = lean_uint64_to_usize(v___x_1409_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1406_, v___x_1410_, v___x_1411_, v_x_1407_, v_x_1408_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1413_, lean_object* v_val_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v_mctx_1418_; lean_object* v_cache_1419_; lean_object* v_zetaDeltaFVarIds_1420_; lean_object* v_postponed_1421_; lean_object* v_diag_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1452_; 
v___x_1417_ = lean_st_ref_take(v___y_1415_);
v_mctx_1418_ = lean_ctor_get(v___x_1417_, 0);
v_cache_1419_ = lean_ctor_get(v___x_1417_, 1);
v_zetaDeltaFVarIds_1420_ = lean_ctor_get(v___x_1417_, 2);
v_postponed_1421_ = lean_ctor_get(v___x_1417_, 3);
v_diag_1422_ = lean_ctor_get(v___x_1417_, 4);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1424_ = v___x_1417_;
v_isShared_1425_ = v_isSharedCheck_1452_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_diag_1422_);
lean_inc(v_postponed_1421_);
lean_inc(v_zetaDeltaFVarIds_1420_);
lean_inc(v_cache_1419_);
lean_inc(v_mctx_1418_);
lean_dec(v___x_1417_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1452_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_depth_1426_; lean_object* v_levelAssignDepth_1427_; lean_object* v_lmvarCounter_1428_; lean_object* v_mvarCounter_1429_; lean_object* v_lDecls_1430_; lean_object* v_decls_1431_; lean_object* v_userNames_1432_; lean_object* v_lAssignment_1433_; lean_object* v_eAssignment_1434_; lean_object* v_dAssignment_1435_; lean_object* v_instanceTypedMVars_1436_; lean_object* v_synthNormMemo_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1451_; 
v_depth_1426_ = lean_ctor_get(v_mctx_1418_, 0);
v_levelAssignDepth_1427_ = lean_ctor_get(v_mctx_1418_, 1);
v_lmvarCounter_1428_ = lean_ctor_get(v_mctx_1418_, 2);
v_mvarCounter_1429_ = lean_ctor_get(v_mctx_1418_, 3);
v_lDecls_1430_ = lean_ctor_get(v_mctx_1418_, 4);
v_decls_1431_ = lean_ctor_get(v_mctx_1418_, 5);
v_userNames_1432_ = lean_ctor_get(v_mctx_1418_, 6);
v_lAssignment_1433_ = lean_ctor_get(v_mctx_1418_, 7);
v_eAssignment_1434_ = lean_ctor_get(v_mctx_1418_, 8);
v_dAssignment_1435_ = lean_ctor_get(v_mctx_1418_, 9);
v_instanceTypedMVars_1436_ = lean_ctor_get(v_mctx_1418_, 10);
v_synthNormMemo_1437_ = lean_ctor_get(v_mctx_1418_, 11);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_mctx_1418_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1439_ = v_mctx_1418_;
v_isShared_1440_ = v_isSharedCheck_1451_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_synthNormMemo_1437_);
lean_inc(v_instanceTypedMVars_1436_);
lean_inc(v_dAssignment_1435_);
lean_inc(v_eAssignment_1434_);
lean_inc(v_lAssignment_1433_);
lean_inc(v_userNames_1432_);
lean_inc(v_decls_1431_);
lean_inc(v_lDecls_1430_);
lean_inc(v_mvarCounter_1429_);
lean_inc(v_lmvarCounter_1428_);
lean_inc(v_levelAssignDepth_1427_);
lean_inc(v_depth_1426_);
lean_dec(v_mctx_1418_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1451_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1441_ = lean_box(0);
v___x_1442_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1434_, v_mvarId_1413_, v_val_1414_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 8, v___x_1442_);
v___x_1444_ = v___x_1439_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_depth_1426_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_levelAssignDepth_1427_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_lmvarCounter_1428_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_mvarCounter_1429_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_lDecls_1430_);
lean_ctor_set(v_reuseFailAlloc_1450_, 5, v_decls_1431_);
lean_ctor_set(v_reuseFailAlloc_1450_, 6, v_userNames_1432_);
lean_ctor_set(v_reuseFailAlloc_1450_, 7, v_lAssignment_1433_);
lean_ctor_set(v_reuseFailAlloc_1450_, 8, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1450_, 9, v_dAssignment_1435_);
lean_ctor_set(v_reuseFailAlloc_1450_, 10, v_instanceTypedMVars_1436_);
lean_ctor_set(v_reuseFailAlloc_1450_, 11, v_synthNormMemo_1437_);
v___x_1444_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1444_);
v___x_1446_ = v___x_1424_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_cache_1419_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_zetaDeltaFVarIds_1420_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_postponed_1421_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_diag_1422_);
v___x_1446_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_st_ref_put(v___y_1415_, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1441_);
return v___x_1448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1453_, lean_object* v_val_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1453_, v_val_1454_, v___y_1455_);
lean_dec(v___y_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
lean_inc(v_g_1458_);
v___x_1464_ = l_Lean_MVarId_getType(v_g_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1466_ = lean_box(0);
v___x_1467_ = l_Lean_Meta_synthInstance(v_a_1465_, v___x_1466_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
v___x_1469_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1458_, v_a_1468_, v___y_1460_);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1478_);
v___x_1471_ = v___x_1469_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v___x_1469_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_box(0);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_g_1458_);
v_a_1479_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1467_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1467_);
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
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_g_1458_);
v_a_1487_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1464_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1464_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1503_){
_start:
{
lean_object* v___f_1504_; lean_object* v___x_1505_; 
v___f_1504_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1505_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1503_, v___f_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1506_, lean_object* v_val_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1506_, v_val_1507_, v___y_1509_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1514_, lean_object* v_val_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1514_, v_val_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1523_, v_x_1524_, v_x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1527_, lean_object* v_x_1528_, size_t v_x_1529_, size_t v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1528_, v_x_1529_, v_x_1530_, v_x_1531_, v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
size_t v_x_1160__boxed_1540_; size_t v_x_1161__boxed_1541_; lean_object* v_res_1542_; 
v_x_1160__boxed_1540_ = lean_unbox_usize(v_x_1536_);
lean_dec(v_x_1536_);
v_x_1161__boxed_1541_ = lean_unbox_usize(v_x_1537_);
lean_dec(v_x_1537_);
v_res_1542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1534_, v_x_1535_, v_x_1160__boxed_1540_, v_x_1161__boxed_1541_, v_x_1538_, v_x_1539_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1543_, lean_object* v_n_1544_, lean_object* v_k_1545_, lean_object* v_v_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1544_, v_k_1545_, v_v_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1548_, size_t v_depth_1549_, lean_object* v_keys_1550_, lean_object* v_vals_1551_, lean_object* v_heq_1552_, lean_object* v_i_1553_, lean_object* v_entries_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1549_, v_keys_1550_, v_vals_1551_, v_i_1553_, v_entries_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1556_, lean_object* v_depth_1557_, lean_object* v_keys_1558_, lean_object* v_vals_1559_, lean_object* v_heq_1560_, lean_object* v_i_1561_, lean_object* v_entries_1562_){
_start:
{
size_t v_depth_boxed_1563_; lean_object* v_res_1564_; 
v_depth_boxed_1563_ = lean_unbox_usize(v_depth_1557_);
lean_dec(v_depth_1557_);
v_res_1564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1556_, v_depth_boxed_1563_, v_keys_1558_, v_vals_1559_, v_heq_1560_, v_i_1561_, v_entries_1562_);
lean_dec_ref(v_vals_1559_);
lean_dec_ref(v_keys_1558_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1566_, v_x_1567_, v_x_1568_, v_x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1571_, lean_object* v_discharge_1572_, lean_object* v_g_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v_g_1573_);
v___x_1579_ = lean_apply_6(v_discharge_1571_, v_g_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, lean_box(0));
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec(v_g_1573_);
lean_dec_ref(v_discharge_1572_);
return v___x_1579_;
}
else
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
v___x_1581_ = l_Lean_Exception_isInterrupt(v_a_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Lean_Exception_isRuntime(v_a_1580_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref_known(v___x_1579_, 1);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
v___x_1583_ = lean_apply_6(v_discharge_1572_, v_g_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, lean_box(0));
return v___x_1583_;
}
else
{
lean_dec(v_g_1573_);
lean_dec_ref(v_discharge_1572_);
return v___x_1579_;
}
}
else
{
lean_dec(v_a_1580_);
lean_dec(v_g_1573_);
lean_dec_ref(v_discharge_1572_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1584_, lean_object* v_discharge_1585_, lean_object* v_g_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1584_, v_discharge_1585_, v_g_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1593_, lean_object* v_discharge_1594_){
_start:
{
lean_object* v_toApplyRulesConfig_1595_; lean_object* v_toBacktrackConfig_1596_; uint8_t v_backtracking_1597_; uint8_t v_intro_1598_; uint8_t v_constructor_1599_; uint8_t v_suggestions_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1632_; 
v_toApplyRulesConfig_1595_ = lean_ctor_get(v_cfg_1593_, 0);
lean_inc_ref(v_toApplyRulesConfig_1595_);
v_toBacktrackConfig_1596_ = lean_ctor_get(v_toApplyRulesConfig_1595_, 0);
lean_inc_ref(v_toBacktrackConfig_1596_);
v_backtracking_1597_ = lean_ctor_get_uint8(v_cfg_1593_, sizeof(void*)*1);
v_intro_1598_ = lean_ctor_get_uint8(v_cfg_1593_, sizeof(void*)*1 + 1);
v_constructor_1599_ = lean_ctor_get_uint8(v_cfg_1593_, sizeof(void*)*1 + 2);
v_suggestions_1600_ = lean_ctor_get_uint8(v_cfg_1593_, sizeof(void*)*1 + 3);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_cfg_1593_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v_cfg_1593_, 0);
lean_dec(v_unused_1633_);
v___x_1602_ = v_cfg_1593_;
v_isShared_1603_ = v_isSharedCheck_1632_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v_cfg_1593_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1632_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_toApplyConfig_1604_; uint8_t v_transparency_1605_; uint8_t v_symm_1606_; uint8_t v_exfalso_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1630_; 
v_toApplyConfig_1604_ = lean_ctor_get(v_toApplyRulesConfig_1595_, 1);
v_transparency_1605_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1595_, sizeof(void*)*2);
v_symm_1606_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1595_, sizeof(void*)*2 + 1);
v_exfalso_1607_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1595_, sizeof(void*)*2 + 2);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_toApplyRulesConfig_1595_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v_toApplyRulesConfig_1595_, 0);
lean_dec(v_unused_1631_);
v___x_1609_ = v_toApplyRulesConfig_1595_;
v_isShared_1610_ = v_isSharedCheck_1630_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_toApplyConfig_1604_);
lean_dec(v_toApplyRulesConfig_1595_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1630_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_maxDepth_1611_; lean_object* v_proc_1612_; lean_object* v_suspend_1613_; lean_object* v_discharge_1614_; uint8_t v_commitIndependentGoals_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1629_; 
v_maxDepth_1611_ = lean_ctor_get(v_toBacktrackConfig_1596_, 0);
v_proc_1612_ = lean_ctor_get(v_toBacktrackConfig_1596_, 1);
v_suspend_1613_ = lean_ctor_get(v_toBacktrackConfig_1596_, 2);
v_discharge_1614_ = lean_ctor_get(v_toBacktrackConfig_1596_, 3);
v_commitIndependentGoals_1615_ = lean_ctor_get_uint8(v_toBacktrackConfig_1596_, sizeof(void*)*4);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_toBacktrackConfig_1596_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1617_ = v_toBacktrackConfig_1596_;
v_isShared_1618_ = v_isSharedCheck_1629_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_discharge_1614_);
lean_inc(v_suspend_1613_);
lean_inc(v_proc_1612_);
lean_inc(v_maxDepth_1611_);
lean_dec(v_toBacktrackConfig_1596_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1629_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___f_1619_; lean_object* v___x_1621_; 
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1619_, 0, v_discharge_1594_);
lean_closure_set(v___f_1619_, 1, v_discharge_1614_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 3, v___f_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_maxDepth_1611_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_proc_1612_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_suspend_1613_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v___f_1619_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*4, v_commitIndependentGoals_1615_);
v___x_1621_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1621_);
v___x_1623_ = v___x_1609_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_toApplyConfig_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*2, v_transparency_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*2 + 1, v_symm_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*2 + 2, v_exfalso_1607_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1623_);
v___x_1625_ = v___x_1602_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*1, v_backtracking_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*1 + 1, v_intro_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*1 + 2, v_constructor_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*1 + 3, v_suggestions_1600_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = 1;
v___x_1641_ = l_Lean_Meta_intro1Core(v_g_1634_, v___x_1640_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1660_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1660_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1660_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_snd_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1658_; 
v_snd_1646_ = lean_ctor_get(v_a_1642_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_a_1642_, 0);
lean_dec(v_unused_1659_);
v___x_1648_ = v_a_1642_;
v_isShared_1649_ = v_isSharedCheck_1658_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snd_1646_);
lean_dec(v_a_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1658_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 1, v___x_1650_);
lean_ctor_set(v___x_1648_, 0, v_snd_1646_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_snd_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1653_);
v___x_1655_ = v___x_1644_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1641_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1641_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1677_){
_start:
{
lean_object* v___f_1678_; lean_object* v___x_1679_; 
v___f_1678_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1679_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1677_, v___f_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1691_ = l_Lean_MVarId_constructor(v_g_1684_, v___x_1690_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1700_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1696_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1691_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1691_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1717_){
_start:
{
lean_object* v___f_1718_; lean_object* v___x_1719_; 
v___f_1718_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1719_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1717_, v___f_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
lean_inc(v_g_1722_);
v___x_1728_ = l_Lean_MVarId_getType(v_g_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = lean_box(0);
v___x_1731_ = l_Lean_Meta_synthInstance(v_a_1729_, v___x_1730_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1741_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1733_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1722_, v_a_1732_, v___y_1724_);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1742_);
v___x_1735_ = v___x_1733_;
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v___x_1733_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v_g_1722_);
v_a_1743_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1731_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1731_);
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
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_g_1722_);
v_a_1751_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1728_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1728_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1767_){
_start:
{
lean_object* v___f_1768_; lean_object* v___x_1769_; 
v___f_1768_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1769_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1767_, v___f_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1770_, lean_object* v___y_1771_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = l_Lean_Expr_hasMVar(v_e_1770_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_e_1770_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v_mctx_1776_; lean_object* v___x_1777_; lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1780_; lean_object* v_cache_1781_; lean_object* v_zetaDeltaFVarIds_1782_; lean_object* v_postponed_1783_; lean_object* v_diag_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1793_; 
v___x_1775_ = lean_st_ref_get(v___y_1771_);
v_mctx_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc_ref(v_mctx_1776_);
lean_dec(v___x_1775_);
v___x_1777_ = l_Lean_instantiateMVarsCore(v_mctx_1776_, v_e_1770_);
v_fst_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_fst_1778_);
v_snd_1779_ = lean_ctor_get(v___x_1777_, 1);
lean_inc(v_snd_1779_);
lean_dec_ref(v___x_1777_);
v___x_1780_ = lean_st_ref_take(v___y_1771_);
v_cache_1781_ = lean_ctor_get(v___x_1780_, 1);
v_zetaDeltaFVarIds_1782_ = lean_ctor_get(v___x_1780_, 2);
v_postponed_1783_ = lean_ctor_get(v___x_1780_, 3);
v_diag_1784_ = lean_ctor_get(v___x_1780_, 4);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v___x_1780_, 0);
lean_dec(v_unused_1794_);
v___x_1786_ = v___x_1780_;
v_isShared_1787_ = v_isSharedCheck_1793_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_diag_1784_);
lean_inc(v_postponed_1783_);
lean_inc(v_zetaDeltaFVarIds_1782_);
lean_inc(v_cache_1781_);
lean_dec(v___x_1780_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1793_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_snd_1779_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_snd_1779_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_cache_1781_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_zetaDeltaFVarIds_1782_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_postponed_1783_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_diag_1784_);
v___x_1789_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_st_ref_put(v___y_1771_, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_fst_1778_);
return v___x_1791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1795_, v___y_1796_);
lean_dec(v___y_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1799_, v___y_1801_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1813_, lean_object* v_x_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1813_, v_x_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
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
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1820_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1820_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1837_, lean_object* v_x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1837_, v_x_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1845_, lean_object* v_mvarId_1846_, lean_object* v_x_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1846_, v_x_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1854_, lean_object* v_mvarId_1855_, lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1854_, v_mvarId_1855_, v_x_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_ref_1869_; lean_object* v___x_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1879_; 
v_ref_1869_ = lean_ctor_get(v___y_1866_, 2);
v___x_1870_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_inc(v_ref_1869_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_ref_1869_);
lean_ctor_set(v___x_1875_, 1, v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 1);
lean_ctor_set(v___x_1873_, 0, v___x_1875_);
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = l_List_reverse___redArg(v_x_1888_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v_head_1896_; lean_object* v_tail_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1917_; 
v_head_1896_ = lean_ctor_get(v_x_1887_, 0);
v_tail_1897_ = lean_ctor_get(v_x_1887_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1899_ = v_x_1887_;
v_isShared_1900_ = v_isSharedCheck_1917_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_tail_1897_);
lean_inc(v_head_1896_);
lean_dec(v_x_1887_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1917_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_inc(v_head_1896_);
v___x_1901_ = l_Lean_Expr_mvar___override(v_head_1896_);
v___x_1902_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1902_, 0, v___x_1901_);
v___x_1903_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1896_, v___x_1902_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v_x_1888_);
lean_ctor_set(v___x_1899_, 0, v_a_1904_);
v___x_1906_ = v___x_1899_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_x_1888_);
v___x_1906_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v_x_1887_ = v_tail_1897_;
v_x_1888_ = v___x_1906_;
goto _start;
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_del_object(v___x_1899_);
lean_dec(v_tail_1897_);
lean_dec(v_x_1888_);
v_a_1909_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1903_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1903_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1918_, v_x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1929_, lean_object* v_proc_1930_, lean_object* v_orig_1931_, lean_object* v_goals_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_box(0);
lean_inc(v_orig_1931_);
v___x_1939_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1931_, v___x_1938_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
v___x_1941_ = lean_apply_6(v_test_1929_, v_a_1940_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, lean_box(0));
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; uint8_t v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1943_ = lean_unbox(v_a_1942_);
lean_dec(v_a_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_goals_1932_);
lean_dec(v_orig_1931_);
lean_dec_ref(v_proc_1930_);
v___x_1944_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1945_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1944_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
lean_object* v___x_1954_; 
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
v___x_1954_ = lean_apply_7(v_proc_1930_, v_orig_1931_, v_goals_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, lean_box(0));
return v___x_1954_;
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_goals_1932_);
lean_dec(v_orig_1931_);
lean_dec_ref(v_proc_1930_);
v_a_1955_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1941_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1941_);
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
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_goals_1932_);
lean_dec(v_orig_1931_);
lean_dec_ref(v_proc_1930_);
lean_dec_ref(v_test_1929_);
v_a_1963_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1939_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1939_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1971_, lean_object* v_proc_1972_, lean_object* v_orig_1973_, lean_object* v_goals_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1971_, v_proc_1972_, v_orig_1973_, v_goals_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1981_, lean_object* v_test_1982_){
_start:
{
lean_object* v_toApplyRulesConfig_1983_; lean_object* v_toBacktrackConfig_1984_; uint8_t v_backtracking_1985_; uint8_t v_intro_1986_; uint8_t v_constructor_1987_; uint8_t v_suggestions_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2020_; 
v_toApplyRulesConfig_1983_ = lean_ctor_get(v_cfg_1981_, 0);
lean_inc_ref(v_toApplyRulesConfig_1983_);
v_toBacktrackConfig_1984_ = lean_ctor_get(v_toApplyRulesConfig_1983_, 0);
lean_inc_ref(v_toBacktrackConfig_1984_);
v_backtracking_1985_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*1);
v_intro_1986_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*1 + 1);
v_constructor_1987_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*1 + 2);
v_suggestions_1988_ = lean_ctor_get_uint8(v_cfg_1981_, sizeof(void*)*1 + 3);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_cfg_1981_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v_cfg_1981_, 0);
lean_dec(v_unused_2021_);
v___x_1990_ = v_cfg_1981_;
v_isShared_1991_ = v_isSharedCheck_2020_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v_cfg_1981_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2020_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_toApplyConfig_1992_; uint8_t v_transparency_1993_; uint8_t v_symm_1994_; uint8_t v_exfalso_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2018_; 
v_toApplyConfig_1992_ = lean_ctor_get(v_toApplyRulesConfig_1983_, 1);
v_transparency_1993_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1983_, sizeof(void*)*2);
v_symm_1994_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1983_, sizeof(void*)*2 + 1);
v_exfalso_1995_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1983_, sizeof(void*)*2 + 2);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_toApplyRulesConfig_1983_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v_toApplyRulesConfig_1983_, 0);
lean_dec(v_unused_2019_);
v___x_1997_ = v_toApplyRulesConfig_1983_;
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_toApplyConfig_1992_);
lean_dec(v_toApplyRulesConfig_1983_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2018_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_maxDepth_1999_; lean_object* v_proc_2000_; lean_object* v_suspend_2001_; lean_object* v_discharge_2002_; uint8_t v_commitIndependentGoals_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2017_; 
v_maxDepth_1999_ = lean_ctor_get(v_toBacktrackConfig_1984_, 0);
v_proc_2000_ = lean_ctor_get(v_toBacktrackConfig_1984_, 1);
v_suspend_2001_ = lean_ctor_get(v_toBacktrackConfig_1984_, 2);
v_discharge_2002_ = lean_ctor_get(v_toBacktrackConfig_1984_, 3);
v_commitIndependentGoals_2003_ = lean_ctor_get_uint8(v_toBacktrackConfig_1984_, sizeof(void*)*4);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_toBacktrackConfig_1984_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2005_ = v_toBacktrackConfig_1984_;
v_isShared_2006_ = v_isSharedCheck_2017_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_discharge_2002_);
lean_inc(v_suspend_2001_);
lean_inc(v_proc_2000_);
lean_inc(v_maxDepth_1999_);
lean_dec(v_toBacktrackConfig_1984_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2017_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___f_2007_; lean_object* v___x_2009_; 
v___f_2007_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2007_, 0, v_test_1982_);
lean_closure_set(v___f_2007_, 1, v_proc_2000_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___f_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_maxDepth_1999_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___f_2007_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_suspend_2001_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_discharge_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*4, v_commitIndependentGoals_2003_);
v___x_2009_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2009_);
v___x_2011_ = v___x_1997_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_toApplyConfig_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*2, v_transparency_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*2 + 1, v_symm_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*2 + 2, v_exfalso_1995_);
v___x_2011_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2011_);
v___x_2013_ = v___x_1990_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*1, v_backtracking_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*1 + 1, v_intro_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*1 + 2, v_constructor_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*1 + 3, v_suggestions_1988_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2022_, lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2030_, v_msg_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2037_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2038_){
_start:
{
if (lean_obj_tag(v_x_2038_) == 0)
{
uint8_t v___x_2039_; 
v___x_2039_ = 0;
return v___x_2039_;
}
else
{
lean_object* v_head_2040_; lean_object* v_tail_2041_; uint8_t v___x_2042_; 
v_head_2040_ = lean_ctor_get(v_x_2038_, 0);
v_tail_2041_ = lean_ctor_get(v_x_2038_, 1);
v___x_2042_ = l_Lean_Expr_hasMVar(v_head_2040_);
if (v___x_2042_ == 0)
{
v_x_2038_ = v_tail_2041_;
goto _start;
}
else
{
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2044_){
_start:
{
uint8_t v_res_2045_; lean_object* v_r_2046_; 
v_res_2045_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2044_);
lean_dec(v_x_2044_);
v_r_2046_ = lean_box(v_res_2045_);
return v_r_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2047_, lean_object* v_sols_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2048_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_inc(v___y_2052_);
lean_inc_ref(v___y_2051_);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
v___x_2055_ = lean_apply_6(v_test_2047_, v_sols_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, lean_box(0));
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec(v_sols_2048_);
lean_dec_ref(v_test_2047_);
v___x_2056_ = lean_box(v___x_2054_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2058_, lean_object* v_sols_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2058_, v_sols_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2066_, lean_object* v_test_2067_){
_start:
{
lean_object* v___f_2068_; lean_object* v___x_2069_; 
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2068_, 0, v_test_2067_);
v___x_2069_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2066_, v___f_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2070_, lean_object* v_x_2071_){
_start:
{
if (lean_obj_tag(v_x_2071_) == 0)
{
uint8_t v___x_2072_; 
lean_dec_ref(v_e_2070_);
v___x_2072_ = 0;
return v___x_2072_;
}
else
{
lean_object* v_head_2073_; lean_object* v_tail_2074_; uint8_t v___x_2075_; 
v_head_2073_ = lean_ctor_get(v_x_2071_, 0);
v_tail_2074_ = lean_ctor_get(v_x_2071_, 1);
lean_inc_ref(v_e_2070_);
v___x_2075_ = l_Lean_Expr_occurs(v_e_2070_, v_head_2073_);
if (v___x_2075_ == 0)
{
v_x_2071_ = v_tail_2074_;
goto _start;
}
else
{
lean_dec_ref(v_e_2070_);
return v___x_2075_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2077_, lean_object* v_x_2078_){
_start:
{
uint8_t v_res_2079_; lean_object* v_r_2080_; 
v_res_2079_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2077_, v_x_2078_);
lean_dec(v_x_2078_);
v_r_2080_ = lean_box(v_res_2079_);
return v_r_2080_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2081_, lean_object* v_x_2082_){
_start:
{
if (lean_obj_tag(v_x_2082_) == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = 1;
return v___x_2083_;
}
else
{
lean_object* v_head_2084_; lean_object* v_tail_2085_; uint8_t v___x_2086_; 
v_head_2084_ = lean_ctor_get(v_x_2082_, 0);
lean_inc(v_head_2084_);
v_tail_2085_ = lean_ctor_get(v_x_2082_, 1);
lean_inc(v_tail_2085_);
lean_dec_ref_known(v_x_2082_, 2);
v___x_2086_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2084_, v_sols_2081_);
if (v___x_2086_ == 0)
{
lean_dec(v_tail_2085_);
return v___x_2086_;
}
else
{
v_x_2082_ = v_tail_2085_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2088_, lean_object* v_x_2089_){
_start:
{
uint8_t v_res_2090_; lean_object* v_r_2091_; 
v_res_2090_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2088_, v_x_2089_);
lean_dec(v_sols_2088_);
v_r_2091_ = lean_box(v_res_2090_);
return v_r_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2092_, lean_object* v_sols_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2093_, v_use_2092_);
v___x_2100_ = lean_box(v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2102_, lean_object* v_sols_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2102_, v_sols_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v_sols_2103_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2110_, lean_object* v_use_2111_){
_start:
{
lean_object* v___f_2112_; lean_object* v___x_2113_; 
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2112_, 0, v_use_2111_);
v___x_2113_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2110_, v___f_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2114_){
_start:
{
lean_object* v___y_2116_; lean_object* v_toApplyRulesConfig_2117_; uint8_t v_backtracking_2118_; uint8_t v_intro_2119_; uint8_t v_constructor_2120_; uint8_t v_suggestions_2121_; uint8_t v_intro_2125_; 
v_intro_2125_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1 + 1);
if (v_intro_2125_ == 0)
{
lean_object* v_toApplyRulesConfig_2126_; uint8_t v_backtracking_2127_; uint8_t v_constructor_2128_; uint8_t v_suggestions_2129_; 
v_toApplyRulesConfig_2126_ = lean_ctor_get(v_cfg_2114_, 0);
lean_inc_ref(v_toApplyRulesConfig_2126_);
v_backtracking_2127_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1);
v_constructor_2128_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1 + 2);
v_suggestions_2129_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1 + 3);
v___y_2116_ = v_cfg_2114_;
v_toApplyRulesConfig_2117_ = v_toApplyRulesConfig_2126_;
v_backtracking_2118_ = v_backtracking_2127_;
v_intro_2119_ = v_intro_2125_;
v_constructor_2120_ = v_constructor_2128_;
v_suggestions_2121_ = v_suggestions_2129_;
goto v___jp_2115_;
}
else
{
lean_object* v_toApplyRulesConfig_2130_; uint8_t v_backtracking_2131_; uint8_t v_constructor_2132_; uint8_t v_suggestions_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_toApplyRulesConfig_2130_ = lean_ctor_get(v_cfg_2114_, 0);
v_backtracking_2131_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1);
v_constructor_2132_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1 + 2);
v_suggestions_2133_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*1 + 3);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_cfg_2114_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2135_ = v_cfg_2114_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_toApplyRulesConfig_2130_);
lean_dec(v_cfg_2114_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint8_t v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = 0;
if (v_isShared_2136_ == 0)
{
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_toApplyRulesConfig_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*1, v_backtracking_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*1 + 2, v_constructor_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*1 + 3, v_suggestions_2133_);
v___x_2139_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v_toApplyRulesConfig_2141_; uint8_t v_backtracking_2142_; uint8_t v_intro_2143_; uint8_t v_constructor_2144_; uint8_t v_suggestions_2145_; 
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*1 + 1, v___x_2137_);
v___x_2140_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2139_);
v_toApplyRulesConfig_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_ref(v_toApplyRulesConfig_2141_);
v_backtracking_2142_ = lean_ctor_get_uint8(v___x_2140_, sizeof(void*)*1);
v_intro_2143_ = lean_ctor_get_uint8(v___x_2140_, sizeof(void*)*1 + 1);
v_constructor_2144_ = lean_ctor_get_uint8(v___x_2140_, sizeof(void*)*1 + 2);
v_suggestions_2145_ = lean_ctor_get_uint8(v___x_2140_, sizeof(void*)*1 + 3);
v___y_2116_ = v___x_2140_;
v_toApplyRulesConfig_2117_ = v_toApplyRulesConfig_2141_;
v_backtracking_2118_ = v_backtracking_2142_;
v_intro_2119_ = v_intro_2143_;
v_constructor_2120_ = v_constructor_2144_;
v_suggestions_2121_ = v_suggestions_2145_;
goto v___jp_2115_;
}
}
}
v___jp_2115_:
{
if (v_constructor_2120_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2117_);
return v___y_2116_;
}
else
{
uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec_ref(v___y_2116_);
v___x_2122_ = 0;
v___x_2123_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2123_, 0, v_toApplyRulesConfig_2117_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*1, v_backtracking_2118_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*1 + 1, v_intro_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*1 + 2, v___x_2122_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*1 + 3, v_suggestions_2121_);
v___x_2124_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2123_);
return v___x_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_List_reverse___redArg(v_x_2149_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2178_; 
v_head_2159_ = lean_ctor_get(v_x_2148_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2148_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_x_2148_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2162_ = v_x_2148_;
v_isShared_2163_ = v_isSharedCheck_2178_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_tail_2160_);
lean_inc(v_head_2159_);
lean_dec(v_x_2148_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2178_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; 
lean_inc(v___y_2155_);
lean_inc_ref(v___y_2154_);
lean_inc(v___y_2153_);
lean_inc_ref(v___y_2152_);
lean_inc(v___y_2151_);
lean_inc_ref(v___y_2150_);
v___x_2164_ = lean_apply_7(v_head_2159_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, lean_box(0));
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v_x_2149_);
lean_ctor_set(v___x_2162_, 0, v_a_2165_);
v___x_2167_ = v___x_2162_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2165_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_x_2149_);
v___x_2167_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
v_x_2148_ = v_tail_2160_;
v_x_2149_ = v___x_2167_;
goto _start;
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_del_object(v___x_2162_);
lean_dec(v_tail_2160_);
lean_dec(v_x_2149_);
v_a_2170_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2164_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2164_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2179_, v_x_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2189_, lean_object* v_cfg_2190_, lean_object* v_lemmas_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
v___x_2199_ = lean_apply_8(v_ctx_2189_, v_cfg_2190_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, lean_box(0));
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = lean_box(0);
v___x_2202_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2191_, v___x_2201_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2211_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = l_List_appendTR___redArg(v_a_2200_, v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_dec(v_a_2200_);
return v___x_2202_;
}
}
else
{
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v_lemmas_2191_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2212_, lean_object* v_cfg_2213_, lean_object* v_lemmas_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2212_, v_cfg_2213_, v_lemmas_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2223_){
_start:
{
uint8_t v___x_2224_; 
v___x_2224_ = 0;
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2225_){
_start:
{
uint8_t v_res_2226_; lean_object* v_r_2227_; 
v_res_2226_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2225_);
lean_dec(v_x_2225_);
v_r_2227_ = lean_box(v_res_2226_);
return v_r_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2228_, lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2228_, v___x_2229_, v___x_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2245_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_fst_2241_; lean_object* v___x_2243_; 
v_fst_2241_ = lean_ctor_get(v_a_2237_, 0);
lean_inc(v_fst_2241_);
lean_dec(v_a_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_fst_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_fst_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
v_a_2246_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2236_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2236_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2254_, lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2254_, v___x_2255_, v___x_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2277_, lean_object* v_g_2278_, lean_object* v_lemmas_2279_, lean_object* v_ctx_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v___f_2286_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2286_, 0, v_ctx_2280_);
lean_closure_set(v___f_2286_, 1, v_cfg_2277_);
lean_closure_set(v___f_2286_, 2, v_lemmas_2279_);
v___x_2287_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2288_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2289_, 0, v___f_2286_);
lean_closure_set(v___f_2289_, 1, v___x_2287_);
lean_closure_set(v___f_2289_, 2, v___x_2288_);
v___x_2290_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2278_, v___f_2289_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2291_, lean_object* v_g_2292_, lean_object* v_lemmas_2293_, lean_object* v_ctx_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2291_, v_g_2292_, v_lemmas_2293_, v_ctx_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2301_, lean_object* v_lemmas_2302_, lean_object* v_ctx_2303_, lean_object* v_g_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
lean_inc(v_g_2304_);
lean_inc_ref(v_cfg_2301_);
v___x_2310_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2301_, v_g_2304_, v_lemmas_2302_, v_ctx_2303_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_toApplyRulesConfig_2311_; lean_object* v_a_2312_; lean_object* v_toApplyConfig_2313_; uint8_t v_transparency_2314_; lean_object* v___x_2315_; 
v_toApplyRulesConfig_2311_ = lean_ctor_get(v_cfg_2301_, 0);
lean_inc_ref(v_toApplyRulesConfig_2311_);
lean_dec_ref(v_cfg_2301_);
v_a_2312_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2310_, 1);
v_toApplyConfig_2313_ = lean_ctor_get(v_toApplyRulesConfig_2311_, 1);
lean_inc_ref(v_toApplyConfig_2313_);
v_transparency_2314_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2311_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2311_);
v___x_2315_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2313_, v_transparency_2314_, v_a_2312_, v_g_2304_, v_a_2306_, v_a_2308_);
return v___x_2315_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_g_2304_);
lean_dec_ref(v_cfg_2301_);
v_a_2316_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2310_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2310_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2324_, lean_object* v_lemmas_2325_, lean_object* v_ctx_2326_, lean_object* v_g_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2324_, v_lemmas_2325_, v_ctx_2326_, v_g_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2334_, lean_object* v_lemmas_2335_, lean_object* v_ctx_2336_, lean_object* v_g_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; 
lean_inc(v_g_2337_);
lean_inc_ref(v_cfg_2334_);
v___x_2343_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2334_, v_g_2337_, v_lemmas_2335_, v_ctx_2336_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_toApplyRulesConfig_2344_; lean_object* v_a_2345_; lean_object* v_toApplyConfig_2346_; uint8_t v_transparency_2347_; lean_object* v___x_2348_; 
v_toApplyRulesConfig_2344_ = lean_ctor_get(v_cfg_2334_, 0);
lean_inc_ref(v_toApplyRulesConfig_2344_);
lean_dec_ref(v_cfg_2334_);
v_a_2345_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2343_, 1);
v_toApplyConfig_2346_ = lean_ctor_get(v_toApplyRulesConfig_2344_, 1);
lean_inc_ref(v_toApplyConfig_2346_);
v_transparency_2347_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2344_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2344_);
v___x_2348_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2346_, v_transparency_2347_, v_a_2345_, v_g_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2348_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_g_2337_);
lean_dec_ref(v_cfg_2334_);
v_a_2349_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2343_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2343_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2357_, lean_object* v_lemmas_2358_, lean_object* v_ctx_2359_, lean_object* v_g_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2357_, v_lemmas_2358_, v_ctx_2359_, v_g_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2367_, lean_object* v_i_2368_, lean_object* v_k_2369_){
_start:
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = lean_array_get_size(v_keys_2367_);
v___x_2371_ = lean_nat_dec_lt(v_i_2368_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec(v_i_2368_);
return v___x_2371_;
}
else
{
lean_object* v_k_x27_2372_; uint8_t v___x_2373_; 
v_k_x27_2372_ = lean_array_fget_borrowed(v_keys_2367_, v_i_2368_);
v___x_2373_ = l_Lean_instBEqMVarId_beq(v_k_2369_, v_k_x27_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = lean_nat_add(v_i_2368_, v___x_2374_);
lean_dec(v_i_2368_);
v_i_2368_ = v___x_2375_;
goto _start;
}
else
{
lean_dec(v_i_2368_);
return v___x_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2377_, lean_object* v_i_2378_, lean_object* v_k_2379_){
_start:
{
uint8_t v_res_2380_; lean_object* v_r_2381_; 
v_res_2380_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2377_, v_i_2378_, v_k_2379_);
lean_dec(v_k_2379_);
lean_dec_ref(v_keys_2377_);
v_r_2381_ = lean_box(v_res_2380_);
return v_r_2381_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2382_, size_t v_x_2383_, lean_object* v_x_2384_){
_start:
{
if (lean_obj_tag(v_x_2382_) == 0)
{
lean_object* v_es_2385_; lean_object* v___x_2386_; size_t v___x_2387_; size_t v___x_2388_; lean_object* v_j_2389_; lean_object* v___x_2390_; 
v_es_2385_ = lean_ctor_get(v_x_2382_, 0);
v___x_2386_ = lean_box(2);
v___x_2387_ = ((size_t)31ULL);
v___x_2388_ = lean_usize_land(v_x_2383_, v___x_2387_);
v_j_2389_ = lean_usize_to_nat(v___x_2388_);
v___x_2390_ = lean_array_get_borrowed(v___x_2386_, v_es_2385_, v_j_2389_);
lean_dec(v_j_2389_);
switch(lean_obj_tag(v___x_2390_))
{
case 0:
{
lean_object* v_key_2391_; uint8_t v___x_2392_; 
v_key_2391_ = lean_ctor_get(v___x_2390_, 0);
v___x_2392_ = l_Lean_instBEqMVarId_beq(v_x_2384_, v_key_2391_);
return v___x_2392_;
}
case 1:
{
lean_object* v_node_2393_; size_t v___x_2394_; size_t v___x_2395_; 
v_node_2393_ = lean_ctor_get(v___x_2390_, 0);
v___x_2394_ = ((size_t)5ULL);
v___x_2395_ = lean_usize_shift_right(v_x_2383_, v___x_2394_);
v_x_2382_ = v_node_2393_;
v_x_2383_ = v___x_2395_;
goto _start;
}
default: 
{
uint8_t v___x_2397_; 
v___x_2397_ = 0;
return v___x_2397_;
}
}
}
else
{
lean_object* v_ks_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v_ks_2398_ = lean_ctor_get(v_x_2382_, 0);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2398_, v___x_2399_, v_x_2384_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
size_t v_x_1980__boxed_2404_; uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_x_1980__boxed_2404_ = lean_unbox_usize(v_x_2402_);
lean_dec(v_x_2402_);
v_res_2405_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2401_, v_x_1980__boxed_2404_, v_x_2403_);
lean_dec(v_x_2403_);
lean_dec_ref(v_x_2401_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
uint64_t v___x_2409_; size_t v___x_2410_; uint8_t v___x_2411_; 
v___x_2409_ = l_Lean_instHashableMVarId_hash(v_x_2408_);
v___x_2410_ = lean_uint64_to_usize(v___x_2409_);
v___x_2411_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2407_, v___x_2410_, v_x_2408_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2412_, v_x_2413_);
lean_dec(v_x_2413_);
lean_dec_ref(v_x_2412_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; lean_object* v_mctx_2420_; lean_object* v_eAssignment_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2419_ = lean_st_ref_get(v___y_2417_);
v_mctx_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc_ref(v_mctx_2420_);
lean_dec(v___x_2419_);
v_eAssignment_2421_ = lean_ctor_get(v_mctx_2420_, 8);
lean_inc_ref(v_eAssignment_2421_);
lean_dec_ref(v_mctx_2420_);
v___x_2422_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2421_, v_mvarId_2416_);
lean_dec_ref(v_eAssignment_2421_);
v___x_2423_ = lean_box(v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec(v_mvarId_2425_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
if (lean_obj_tag(v_x_2430_) == 0)
{
return v_x_2429_;
}
else
{
lean_object* v_head_2431_; lean_object* v_tail_2432_; lean_object* v___x_2433_; 
v_head_2431_ = lean_ctor_get(v_x_2430_, 0);
lean_inc(v_head_2431_);
v_tail_2432_ = lean_ctor_get(v_x_2430_, 1);
lean_inc(v_tail_2432_);
lean_dec_ref_known(v_x_2430_, 2);
v___x_2433_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2429_, v_head_2431_);
v_x_2429_ = v___x_2433_;
v_x_2430_ = v_tail_2432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2435_, lean_object* v_a_2436_, uint8_t v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
if (lean_obj_tag(v_a_2438_) == 0)
{
if (lean_obj_tag(v_a_2439_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_f_2435_);
v___x_2446_ = lean_box(v_a_2437_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v_a_2440_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
else
{
lean_object* v_head_2449_; lean_object* v_tail_2450_; 
v_head_2449_ = lean_ctor_get(v_a_2439_, 0);
lean_inc(v_head_2449_);
v_tail_2450_ = lean_ctor_get(v_a_2439_, 1);
lean_inc(v_tail_2450_);
lean_dec_ref_known(v_a_2439_, 2);
v_a_2438_ = v_head_2449_;
v_a_2439_ = v_tail_2450_;
goto _start;
}
}
else
{
lean_object* v_head_2452_; lean_object* v_tail_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2496_; 
v_head_2452_ = lean_ctor_get(v_a_2438_, 0);
v_tail_2453_ = lean_ctor_get(v_a_2438_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2455_ = v_a_2438_;
v_isShared_2456_ = v_isSharedCheck_2496_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_tail_2453_);
lean_inc(v_head_2452_);
lean_dec(v_a_2438_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2496_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2495_; 
v___x_2457_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2452_, v___y_2442_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2495_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2495_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_unbox(v_a_2458_);
lean_dec(v_a_2458_);
if (v___x_2462_ == 0)
{
lean_object* v_zero_2463_; uint8_t v_isZero_2464_; 
v_zero_2463_ = lean_unsigned_to_nat(0u);
v_isZero_2464_ = lean_nat_dec_eq(v_a_2436_, v_zero_2463_);
if (v_isZero_2464_ == 1)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_del_object(v___x_2455_);
lean_dec(v_a_2436_);
lean_dec_ref(v_f_2435_);
v___x_2465_ = lean_array_push(v_a_2440_, v_head_2452_);
v___x_2466_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2465_, v_tail_2453_);
v___x_2467_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2466_, v_a_2439_);
v___x_2468_ = lean_box(v_a_2437_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___x_2467_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2469_);
v___x_2471_ = v___x_2460_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
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
lean_object* v_one_2473_; lean_object* v_n_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_del_object(v___x_2460_);
v_one_2473_ = lean_unsigned_to_nat(1u);
v_n_2474_ = lean_nat_sub(v_a_2436_, v_one_2473_);
lean_dec(v_a_2436_);
v___x_2475_ = 1;
lean_inc_ref(v_f_2435_);
lean_inc(v_head_2452_);
v___x_2476_ = lean_apply_1(v_f_2435_, v_head_2452_);
v___x_2477_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2476_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
if (lean_obj_tag(v_a_2478_) == 0)
{
lean_object* v___x_2479_; 
lean_del_object(v___x_2455_);
v___x_2479_ = lean_array_push(v_a_2440_, v_head_2452_);
v_a_2436_ = v_n_2474_;
v_a_2438_ = v_tail_2453_;
v_a_2440_ = v___x_2479_;
goto _start;
}
else
{
lean_object* v_val_2481_; lean_object* v___x_2483_; 
lean_dec(v_head_2452_);
v_val_2481_ = lean_ctor_get(v_a_2478_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v_a_2478_, 1);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v_a_2439_);
lean_ctor_set(v___x_2455_, 0, v_tail_2453_);
v___x_2483_ = v___x_2455_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_tail_2453_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_a_2439_);
v___x_2483_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
v_a_2436_ = v_n_2474_;
v_a_2437_ = v___x_2475_;
v_a_2438_ = v_val_2481_;
v_a_2439_ = v___x_2483_;
goto _start;
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_n_2474_);
lean_del_object(v___x_2455_);
lean_dec(v_tail_2453_);
lean_dec(v_head_2452_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_f_2435_);
v_a_2486_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2477_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2477_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_del_object(v___x_2460_);
lean_del_object(v___x_2455_);
lean_dec(v_head_2452_);
v_a_2438_ = v_tail_2453_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v_a_2059__boxed_2508_; lean_object* v_res_2509_; 
v_a_2059__boxed_2508_ = lean_unbox(v_a_2499_);
v_res_2509_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2497_, v_a_2498_, v_a_2059__boxed_2508_, v_a_2500_, v_a_2501_, v_a_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2510_, size_t v_i_2511_, size_t v_stop_2512_, lean_object* v_b_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_a_2520_; uint8_t v___x_2524_; 
v___x_2524_ = lean_usize_dec_eq(v_i_2511_, v_stop_2512_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_array_uget_borrowed(v_as_2510_, v_i_2511_);
v___x_2526_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2525_, v___y_2515_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; uint8_t v___x_2528_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = lean_unbox(v_a_2527_);
lean_dec(v_a_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
lean_inc(v___x_2525_);
v___x_2529_ = lean_array_push(v_b_2513_, v___x_2525_);
v_a_2520_ = v___x_2529_;
goto v___jp_2519_;
}
else
{
v_a_2520_ = v_b_2513_;
goto v___jp_2519_;
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v_b_2513_);
v_a_2530_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2526_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2526_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_b_2513_);
return v___x_2538_;
}
v___jp_2519_:
{
size_t v___x_2521_; size_t v___x_2522_; 
v___x_2521_ = ((size_t)1ULL);
v___x_2522_ = lean_usize_add(v_i_2511_, v___x_2521_);
v_i_2511_ = v___x_2522_;
v_b_2513_ = v_a_2520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2539_, lean_object* v_i_2540_, lean_object* v_stop_2541_, lean_object* v_b_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
size_t v_i_boxed_2548_; size_t v_stop_boxed_2549_; lean_object* v_res_2550_; 
v_i_boxed_2548_ = lean_unbox_usize(v_i_2540_);
lean_dec(v_i_2540_);
v_stop_boxed_2549_ = lean_unbox_usize(v_stop_2541_);
lean_dec(v_stop_2541_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2539_, v_i_boxed_2548_, v_stop_boxed_2549_, v_b_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v_as_2539_);
return v_res_2550_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2554_ = lean_array_to_list(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2555_, lean_object* v_goals_2556_, lean_object* v_maxIters_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2563_ = 0;
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2567_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2555_, v_maxIters_2557_, v___x_2563_, v_goals_2556_, v___x_2564_, v___x_2566_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2610_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2610_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2610_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2609_; 
v_fst_2572_ = lean_ctor_get(v_a_2568_, 0);
v_snd_2573_ = lean_ctor_get(v_a_2568_, 1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_a_2568_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2575_ = v_a_2568_;
v_isShared_2576_ = v_isSharedCheck_2609_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_snd_2573_);
lean_inc(v_fst_2572_);
lean_dec(v_a_2568_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2609_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = lean_array_get_size(v_snd_2573_);
v___x_2578_ = lean_nat_dec_lt(v___x_2565_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
lean_dec(v_snd_2573_);
v___x_2579_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2579_);
v___x_2581_ = v___x_2575_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_fst_2572_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2581_);
v___x_2583_ = v___x_2570_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
lean_del_object(v___x_2570_);
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = lean_usize_of_nat(v___x_2577_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2573_, v___x_2586_, v___x_2587_, v___x_2566_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v_snd_2573_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2600_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2600_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2600_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = lean_array_to_list(v_a_2589_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2593_);
v___x_2595_ = v___x_2575_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_fst_2572_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2595_);
v___x_2597_ = v___x_2591_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
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
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_del_object(v___x_2575_);
lean_dec(v_fst_2572_);
v_a_2601_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2588_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2588_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2567_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2567_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2619_, lean_object* v_goals_2620_, lean_object* v_maxIters_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2619_, v_goals_2620_, v_maxIters_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2627_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2631_, lean_object* v_goals_2632_, lean_object* v_maxIters_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2631_, v_goals_2632_, v_maxIters_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2652_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2652_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2652_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_fst_2644_; uint8_t v___x_2645_; 
v_fst_2644_ = lean_ctor_get(v_a_2640_, 0);
v___x_2645_ = lean_unbox(v_fst_2644_);
if (v___x_2645_ == 1)
{
lean_object* v_snd_2646_; lean_object* v___x_2648_; 
v_snd_2646_ = lean_ctor_get(v_a_2640_, 1);
lean_inc(v_snd_2646_);
lean_dec(v_a_2640_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_snd_2646_);
v___x_2648_ = v___x_2642_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_snd_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
v___x_2650_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2651_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2650_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
v_a_2653_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2639_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2639_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2661_, lean_object* v_goals_2662_, lean_object* v_maxIters_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2661_, v_goals_2662_, v_maxIters_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2670_, lean_object* v_ctx_2671_, lean_object* v_cfg_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
uint8_t v_backtracking_2679_; 
v_backtracking_2679_ = lean_ctor_get_uint8(v_cfg_2672_, sizeof(void*)*1);
if (v_backtracking_2679_ == 0)
{
lean_object* v_toApplyRulesConfig_2680_; lean_object* v_toBacktrackConfig_2681_; lean_object* v_maxDepth_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_toApplyRulesConfig_2680_ = lean_ctor_get(v_cfg_2672_, 0);
v_toBacktrackConfig_2681_ = lean_ctor_get(v_toApplyRulesConfig_2680_, 0);
v_maxDepth_2682_ = lean_ctor_get(v_toBacktrackConfig_2681_, 0);
lean_inc(v_maxDepth_2682_);
v___x_2683_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2683_, 0, v_cfg_2672_);
lean_closure_set(v___x_2683_, 1, v_lemmas_2670_);
lean_closure_set(v___x_2683_, 2, v_ctx_2671_);
v___x_2684_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2683_, v_a_2673_, v_maxDepth_2682_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
return v___x_2684_;
}
else
{
lean_object* v_toApplyRulesConfig_2685_; lean_object* v_toBacktrackConfig_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_toApplyRulesConfig_2685_ = lean_ctor_get(v_cfg_2672_, 0);
v_toBacktrackConfig_2686_ = lean_ctor_get(v_toApplyRulesConfig_2685_, 0);
lean_inc_ref(v_toBacktrackConfig_2686_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2688_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2688_, 0, v_cfg_2672_);
lean_closure_set(v___x_2688_, 1, v_lemmas_2670_);
lean_closure_set(v___x_2688_, 2, v_ctx_2671_);
v___x_2689_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2686_, v___x_2687_, v___x_2688_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
return v___x_2689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2690_, lean_object* v_ctx_2691_, lean_object* v_cfg_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2690_, v_ctx_2691_, v_cfg_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2700_, v___y_2702_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v_mvarId_2707_);
return v_res_2713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2714_, lean_object* v_x_2715_, lean_object* v_x_2716_){
_start:
{
uint8_t v___x_2717_; 
v___x_2717_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2715_, v_x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2718_, lean_object* v_x_2719_, lean_object* v_x_2720_){
_start:
{
uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_res_2721_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2718_, v_x_2719_, v_x_2720_);
lean_dec(v_x_2720_);
lean_dec_ref(v_x_2719_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2723_, lean_object* v_x_2724_, size_t v_x_2725_, lean_object* v_x_2726_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2724_, v_x_2725_, v_x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_){
_start:
{
size_t v_x_2499__boxed_2732_; uint8_t v_res_2733_; lean_object* v_r_2734_; 
v_x_2499__boxed_2732_ = lean_unbox_usize(v_x_2730_);
lean_dec(v_x_2730_);
v_res_2733_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2728_, v_x_2729_, v_x_2499__boxed_2732_, v_x_2731_);
lean_dec(v_x_2731_);
lean_dec_ref(v_x_2729_);
v_r_2734_ = lean_box(v_res_2733_);
return v_r_2734_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2735_, lean_object* v_keys_2736_, lean_object* v_vals_2737_, lean_object* v_heq_2738_, lean_object* v_i_2739_, lean_object* v_k_2740_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2736_, v_i_2739_, v_k_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2742_, lean_object* v_keys_2743_, lean_object* v_vals_2744_, lean_object* v_heq_2745_, lean_object* v_i_2746_, lean_object* v_k_2747_){
_start:
{
uint8_t v_res_2748_; lean_object* v_r_2749_; 
v_res_2748_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2742_, v_keys_2743_, v_vals_2744_, v_heq_2745_, v_i_2746_, v_k_2747_);
lean_dec(v_k_2747_);
lean_dec_ref(v_vals_2744_);
lean_dec_ref(v_keys_2743_);
v_r_2749_ = lean_box(v_res_2748_);
return v_r_2749_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec_ref(v_x_2761_);
return v_res_2767_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2770_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2771_ = l_Lean_Name_append(v___x_2770_, v___x_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2772_, lean_object* v_lemmas_2773_, lean_object* v_ctx_2774_, lean_object* v_goals_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___f_2781_; lean_object* v_cfg_2782_; lean_object* v___x_2783_; 
v___f_2781_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v_cfg_2782_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2772_);
lean_inc(v_goals_2775_);
lean_inc_ref(v_cfg_2782_);
lean_inc_ref(v_ctx_2774_);
lean_inc(v_lemmas_2773_);
v___x_2783_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2773_, v_ctx_2774_, v_cfg_2782_, v_goals_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_dec_ref(v_cfg_2782_);
lean_dec(v_goals_2775_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
return v___x_2783_;
}
else
{
lean_object* v_a_2784_; uint8_t v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v___x_2785_ = l_Lean_Exception_isInterrupt(v_a_2784_);
if (v___x_2785_ == 0)
{
uint8_t v___x_2786_; 
lean_inc(v_a_2784_);
v___x_2786_ = l_Lean_Exception_isRuntime(v_a_2784_);
if (v___x_2786_ == 0)
{
if (lean_obj_tag(v_goals_2775_) == 1)
{
lean_object* v_tail_2787_; 
v_tail_2787_ = lean_ctor_get(v_goals_2775_, 1);
lean_inc(v_tail_2787_);
if (lean_obj_tag(v_tail_2787_) == 0)
{
lean_object* v_toApplyRulesConfig_2788_; uint8_t v_exfalso_2789_; 
v_toApplyRulesConfig_2788_ = lean_ctor_get(v_cfg_2782_, 0);
v_exfalso_2789_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2788_, sizeof(void*)*2 + 2);
if (v_exfalso_2789_ == 1)
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2919_; 
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2783_, 0);
lean_dec(v_unused_2920_);
v___x_2791_ = v___x_2783_;
v_isShared_2792_ = v_isSharedCheck_2919_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v___x_2783_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2919_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v_toCold_2793_; lean_object* v_options_2794_; uint8_t v_hasTrace_2795_; 
v_toCold_2793_ = lean_ctor_get(v_a_2778_, 0);
v_options_2794_ = lean_ctor_get(v_toCold_2793_, 2);
v_hasTrace_2795_ = lean_ctor_get_uint8(v_options_2794_, sizeof(void*)*1);
if (v_hasTrace_2795_ == 0)
{
lean_object* v_head_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2814_; 
lean_del_object(v___x_2791_);
v_head_2796_ = lean_ctor_get(v_goals_2775_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_goals_2775_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v_goals_2775_, 1);
lean_dec(v_unused_2815_);
v___x_2798_ = v_goals_2775_;
v_isShared_2799_ = v_isSharedCheck_2814_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_head_2796_);
lean_dec(v_goals_2775_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2814_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_MVarId_exfalso(v_head_2796_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v_a_2801_);
v___x_2803_ = v___x_2798_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2801_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_tail_2787_);
v___x_2803_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; 
v___x_2804_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2773_, v_ctx_2774_, v_cfg_2782_, v___x_2803_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2804_;
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_del_object(v___x_2798_);
lean_dec_ref(v_cfg_2782_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
v_a_2806_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2800_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2800_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
else
{
lean_object* v_head_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2917_; 
v_head_2816_ = lean_ctor_get(v_goals_2775_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_goals_2775_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v_goals_2775_, 1);
lean_dec(v_unused_2918_);
v___x_2818_ = v_goals_2775_;
v_isShared_2819_ = v_isSharedCheck_2917_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_head_2816_);
lean_dec(v_goals_2775_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2917_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_inheritedTraceOptions_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v_a_2828_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_a_2843_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v_a_2850_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v_a_2862_; 
v_inheritedTraceOptions_2820_ = lean_ctor_get(v_toCold_2793_, 11);
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2822_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2823_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2820_, v_options_2794_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = l_Lean_trace_profiler;
v___x_2904_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2794_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; 
lean_del_object(v___x_2818_);
lean_del_object(v___x_2791_);
v___x_2905_ = l_Lean_MVarId_exfalso(v_head_2816_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2907_, 0, v_a_2906_);
lean_ctor_set(v___x_2907_, 1, v_tail_2787_);
v___x_2908_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2773_, v_ctx_2774_, v_cfg_2782_, v___x_2907_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2908_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_cfg_2782_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
v_a_2909_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2905_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2905_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
goto v___jp_2864_;
}
}
else
{
goto v___jp_2864_;
}
v___jp_2825_:
{
lean_object* v___x_2829_; double v___x_2830_; double v___x_2831_; double v___x_2832_; double v___x_2833_; double v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2829_ = lean_io_mono_nanos_now();
v___x_2830_ = lean_float_of_nat(v___y_2826_);
v___x_2831_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2832_ = lean_float_div(v___x_2830_, v___x_2831_);
v___x_2833_ = lean_float_of_nat(v___x_2829_);
v___x_2834_ = lean_float_div(v___x_2833_, v___x_2831_);
v___x_2835_ = lean_box_float(v___x_2832_);
v___x_2836_ = lean_box_float(v___x_2834_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2828_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_2821_, v_exfalso_2789_, v___x_2822_, v_options_2794_, v___x_2824_, v___y_2827_, v___f_2781_, v___x_2838_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2839_;
}
v___jp_2840_:
{
lean_object* v___x_2845_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2843_);
v___x_2845_ = v___x_2791_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
v___y_2826_ = v___y_2841_;
v___y_2827_ = v___y_2842_;
v_a_2828_ = v___x_2845_;
goto v___jp_2825_;
}
}
v___jp_2847_:
{
lean_object* v___x_2851_; double v___x_2852_; double v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2851_ = lean_io_get_num_heartbeats();
v___x_2852_ = lean_float_of_nat(v___y_2848_);
v___x_2853_ = lean_float_of_nat(v___x_2851_);
v___x_2854_ = lean_box_float(v___x_2852_);
v___x_2855_ = lean_box_float(v___x_2853_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_a_2850_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_2821_, v_exfalso_2789_, v___x_2822_, v_options_2794_, v___x_2824_, v___y_2849_, v___f_2781_, v___x_2857_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2858_;
}
v___jp_2859_:
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v_a_2862_);
v___y_2848_ = v___y_2860_;
v___y_2849_ = v___y_2861_;
v_a_2850_ = v___x_2863_;
goto v___jp_2847_;
}
v___jp_2864_:
{
lean_object* v___x_2865_; lean_object* v_a_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2865_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2779_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2868_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2794_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_io_mono_nanos_now();
v___x_2870_ = l_Lean_MVarId_exfalso(v_head_2816_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_a_2871_);
v___x_2873_ = v___x_2818_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2871_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_tail_2787_);
v___x_2873_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2773_, v_ctx_2774_, v_cfg_2782_, v___x_2873_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_del_object(v___x_2791_);
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 1);
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v___y_2826_ = v___x_2869_;
v___y_2827_ = v_a_2866_;
v_a_2828_ = v___x_2880_;
goto v___jp_2825_;
}
}
}
else
{
lean_object* v_a_2883_; 
v_a_2883_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2874_, 1);
v___y_2841_ = v___x_2869_;
v___y_2842_ = v_a_2866_;
v_a_2843_ = v_a_2883_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v_a_2885_; 
lean_del_object(v___x_2818_);
lean_dec_ref(v_cfg_2782_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
v_a_2885_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2870_, 1);
v___y_2841_ = v___x_2869_;
v___y_2842_ = v_a_2866_;
v_a_2843_ = v_a_2885_;
goto v___jp_2840_;
}
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_del_object(v___x_2791_);
v___x_2886_ = lean_io_get_num_heartbeats();
v___x_2887_ = l_Lean_MVarId_exfalso(v_head_2816_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_a_2888_);
v___x_2890_ = v___x_2818_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2888_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_tail_2787_);
v___x_2890_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2773_, v_ctx_2774_, v_cfg_2782_, v___x_2890_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 1);
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
v___y_2848_ = v___x_2886_;
v___y_2849_ = v_a_2866_;
v_a_2850_ = v___x_2897_;
goto v___jp_2847_;
}
}
}
else
{
lean_object* v_a_2900_; 
v_a_2900_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2891_, 1);
v___y_2860_ = v___x_2886_;
v___y_2861_ = v_a_2866_;
v_a_2862_ = v_a_2900_;
goto v___jp_2859_;
}
}
}
else
{
lean_object* v_a_2902_; 
lean_del_object(v___x_2818_);
lean_dec_ref(v_cfg_2782_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
v_a_2902_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2887_, 1);
v___y_2860_ = v___x_2886_;
v___y_2861_ = v_a_2866_;
v_a_2862_ = v_a_2902_;
goto v___jp_2859_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2775_, 2);
lean_dec_ref(v_cfg_2782_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
return v___x_2783_;
}
}
else
{
lean_dec_ref_known(v_goals_2775_, 2);
lean_dec(v_tail_2787_);
lean_dec_ref(v_cfg_2782_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
return v___x_2783_;
}
}
else
{
lean_dec_ref(v_cfg_2782_);
lean_dec(v_goals_2775_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
return v___x_2783_;
}
}
else
{
lean_dec_ref(v_cfg_2782_);
lean_dec(v_goals_2775_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
return v___x_2783_;
}
}
else
{
lean_dec_ref(v_cfg_2782_);
lean_dec(v_goals_2775_);
lean_dec_ref(v_ctx_2774_);
lean_dec(v_lemmas_2773_);
return v___x_2783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2921_, lean_object* v_lemmas_2922_, lean_object* v_ctx_2923_, lean_object* v_goals_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2921_, v_lemmas_2922_, v_ctx_2923_, v_goals_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2931_, lean_object* v_x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
if (lean_obj_tag(v_x_2931_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = l_List_reverse___redArg(v_x_2932_);
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
return v___x_2939_;
}
else
{
lean_object* v_head_2940_; lean_object* v_tail_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2965_; 
v_head_2940_ = lean_ctor_get(v_x_2931_, 0);
v_tail_2941_ = lean_ctor_get(v_x_2931_, 1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_x_2931_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2943_ = v_x_2931_;
v_isShared_2944_ = v_isSharedCheck_2965_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_tail_2941_);
lean_inc(v_head_2940_);
lean_dec(v_x_2931_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2965_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Expr_applySymm(v_head_2940_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v_x_2932_);
lean_ctor_set(v___x_2943_, 0, v_a_2946_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2946_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_x_2932_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
v_x_2931_ = v_tail_2941_;
v_x_2932_ = v___x_2948_;
goto _start;
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2964_; 
lean_del_object(v___x_2943_);
v_a_2951_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2953_ = v___x_2945_;
v_isShared_2954_ = v_isSharedCheck_2964_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2945_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2964_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
uint8_t v___x_2955_; 
v___x_2955_ = l_Lean_Exception_isInterrupt(v_a_2951_);
if (v___x_2955_ == 0)
{
uint8_t v___x_2956_; 
lean_inc(v_a_2951_);
v___x_2956_ = l_Lean_Exception_isRuntime(v_a_2951_);
if (v___x_2956_ == 0)
{
lean_del_object(v___x_2953_);
lean_dec(v_a_2951_);
v_x_2931_ = v_tail_2941_;
goto _start;
}
else
{
lean_object* v___x_2959_; 
lean_dec(v_tail_2941_);
lean_dec(v_x_2932_);
if (v_isShared_2954_ == 0)
{
v___x_2959_ = v___x_2953_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2951_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_object* v___x_2962_; 
lean_dec(v_tail_2941_);
lean_dec(v_x_2932_);
if (v_isShared_2954_ == 0)
{
v___x_2962_ = v___x_2953_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2951_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2966_, v_x_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2974_, lean_object* v_hyps_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
if (v_symm_2974_ == 0)
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_hyps_2975_);
return v___x_2981_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_box(0);
lean_inc(v_hyps_2975_);
v___x_2983_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2975_, v___x_2982_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2992_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = l_List_appendTR___redArg(v_hyps_2975_, v_a_2984_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_2988_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_dec(v_hyps_2975_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_2993_, lean_object* v_hyps_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
uint8_t v_symm_boxed_3000_; lean_object* v_res_3001_; 
v_symm_boxed_3000_ = lean_unbox(v_symm_2993_);
v_res_3001_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3000_, v_hyps_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3002_, size_t v_sz_3003_, size_t v_i_3004_, lean_object* v_b_3005_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_lt(v_i_3004_, v_sz_3003_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_b_3005_);
return v___x_3008_;
}
else
{
lean_object* v_snd_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3027_; 
v_snd_3009_ = lean_ctor_get(v_b_3005_, 1);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_b_3005_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v_b_3005_, 0);
lean_dec(v_unused_3028_);
v___x_3011_ = v_b_3005_;
v_isShared_3012_ = v_isSharedCheck_3027_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snd_3009_);
lean_dec(v_b_3005_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3027_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v_a_3015_; lean_object* v_a_3022_; 
v___x_3013_ = lean_box(0);
v_a_3022_ = lean_array_uget_borrowed(v_as_3002_, v_i_3004_);
if (lean_obj_tag(v_a_3022_) == 0)
{
v_a_3015_ = v_snd_3009_;
goto v___jp_3014_;
}
else
{
lean_object* v_val_3023_; uint8_t v___x_3024_; 
v_val_3023_ = lean_ctor_get(v_a_3022_, 0);
v___x_3024_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_inc(v_val_3023_);
v___x_3025_ = l_Lean_LocalDecl_toExpr(v_val_3023_);
v___x_3026_ = lean_array_push(v_snd_3009_, v___x_3025_);
v_a_3015_ = v___x_3026_;
goto v___jp_3014_;
}
else
{
v_a_3015_ = v_snd_3009_;
goto v___jp_3014_;
}
}
v___jp_3014_:
{
lean_object* v___x_3017_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v_a_3015_);
lean_ctor_set(v___x_3011_, 0, v___x_3013_);
v___x_3017_ = v___x_3011_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_a_3015_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
size_t v___x_3018_; size_t v___x_3019_; 
v___x_3018_ = ((size_t)1ULL);
v___x_3019_ = lean_usize_add(v_i_3004_, v___x_3018_);
v_i_3004_ = v___x_3019_;
v_b_3005_ = v___x_3017_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3029_, lean_object* v_sz_3030_, lean_object* v_i_3031_, lean_object* v_b_3032_, lean_object* v___y_3033_){
_start:
{
size_t v_sz_boxed_3034_; size_t v_i_boxed_3035_; lean_object* v_res_3036_; 
v_sz_boxed_3034_ = lean_unbox_usize(v_sz_3030_);
lean_dec(v_sz_3030_);
v_i_boxed_3035_ = lean_unbox_usize(v_i_3031_);
lean_dec(v_i_3031_);
v_res_3036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3029_, v_sz_boxed_3034_, v_i_boxed_3035_, v_b_3032_);
lean_dec_ref(v_as_3029_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3037_, size_t v_sz_3038_, size_t v_i_3039_, lean_object* v_b_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_usize_dec_lt(v_i_3039_, v_sz_3038_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_b_3040_);
return v___x_3049_;
}
else
{
lean_object* v_snd_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3068_; 
v_snd_3050_ = lean_ctor_get(v_b_3040_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_b_3040_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_b_3040_, 0);
lean_dec(v_unused_3069_);
v___x_3052_ = v_b_3040_;
v_isShared_3053_ = v_isSharedCheck_3068_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_snd_3050_);
lean_dec(v_b_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3068_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v_a_3056_; lean_object* v_a_3063_; 
v___x_3054_ = lean_box(0);
v_a_3063_ = lean_array_uget_borrowed(v_as_3037_, v_i_3039_);
if (lean_obj_tag(v_a_3063_) == 0)
{
v_a_3056_ = v_snd_3050_;
goto v___jp_3055_;
}
else
{
lean_object* v_val_3064_; uint8_t v___x_3065_; 
v_val_3064_ = lean_ctor_get(v_a_3063_, 0);
v___x_3065_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_inc(v_val_3064_);
v___x_3066_ = l_Lean_LocalDecl_toExpr(v_val_3064_);
v___x_3067_ = lean_array_push(v_snd_3050_, v___x_3066_);
v_a_3056_ = v___x_3067_;
goto v___jp_3055_;
}
else
{
v_a_3056_ = v_snd_3050_;
goto v___jp_3055_;
}
}
v___jp_3055_:
{
lean_object* v___x_3058_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 1, v_a_3056_);
lean_ctor_set(v___x_3052_, 0, v___x_3054_);
v___x_3058_ = v___x_3052_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_a_3056_);
v___x_3058_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
size_t v___x_3059_; size_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = ((size_t)1ULL);
v___x_3060_ = lean_usize_add(v_i_3039_, v___x_3059_);
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3037_, v_sz_3038_, v___x_3060_, v___x_3058_);
return v___x_3061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3070_, lean_object* v_sz_3071_, lean_object* v_i_3072_, lean_object* v_b_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
size_t v_sz_boxed_3081_; size_t v_i_boxed_3082_; lean_object* v_res_3083_; 
v_sz_boxed_3081_ = lean_unbox_usize(v_sz_3071_);
lean_dec(v_sz_3071_);
v_i_boxed_3082_ = lean_unbox_usize(v_i_3072_);
lean_dec(v_i_3072_);
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3070_, v_sz_boxed_3081_, v_i_boxed_3082_, v_b_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v_as_3070_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3084_, size_t v_sz_3085_, size_t v_i_3086_, lean_object* v_b_3087_){
_start:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_usize_dec_lt(v_i_3086_, v_sz_3085_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_b_3087_);
return v___x_3090_;
}
else
{
lean_object* v_snd_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3109_; 
v_snd_3091_ = lean_ctor_get(v_b_3087_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_b_3087_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v_b_3087_, 0);
lean_dec(v_unused_3110_);
v___x_3093_ = v_b_3087_;
v_isShared_3094_ = v_isSharedCheck_3109_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_snd_3091_);
lean_dec(v_b_3087_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3109_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v_a_3097_; lean_object* v_a_3104_; 
v___x_3095_ = lean_box(0);
v_a_3104_ = lean_array_uget_borrowed(v_as_3084_, v_i_3086_);
if (lean_obj_tag(v_a_3104_) == 0)
{
v_a_3097_ = v_snd_3091_;
goto v___jp_3096_;
}
else
{
lean_object* v_val_3105_; uint8_t v___x_3106_; 
v_val_3105_ = lean_ctor_get(v_a_3104_, 0);
v___x_3106_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_inc(v_val_3105_);
v___x_3107_ = l_Lean_LocalDecl_toExpr(v_val_3105_);
v___x_3108_ = lean_array_push(v_snd_3091_, v___x_3107_);
v_a_3097_ = v___x_3108_;
goto v___jp_3096_;
}
else
{
v_a_3097_ = v_snd_3091_;
goto v___jp_3096_;
}
}
v___jp_3096_:
{
lean_object* v___x_3099_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 1, v_a_3097_);
lean_ctor_set(v___x_3093_, 0, v___x_3095_);
v___x_3099_ = v___x_3093_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_a_3097_);
v___x_3099_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
size_t v___x_3100_; size_t v___x_3101_; 
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_i_3086_, v___x_3100_);
v_i_3086_ = v___x_3101_;
v_b_3087_ = v___x_3099_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3111_, lean_object* v_sz_3112_, lean_object* v_i_3113_, lean_object* v_b_3114_, lean_object* v___y_3115_){
_start:
{
size_t v_sz_boxed_3116_; size_t v_i_boxed_3117_; lean_object* v_res_3118_; 
v_sz_boxed_3116_ = lean_unbox_usize(v_sz_3112_);
lean_dec(v_sz_3112_);
v_i_boxed_3117_ = lean_unbox_usize(v_i_3113_);
lean_dec(v_i_3113_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3111_, v_sz_boxed_3116_, v_i_boxed_3117_, v_b_3114_);
lean_dec_ref(v_as_3111_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3119_, size_t v_sz_3120_, size_t v_i_3121_, lean_object* v_b_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_3130_; 
v___x_3130_ = lean_usize_dec_lt(v_i_3121_, v_sz_3120_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; 
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_b_3122_);
return v___x_3131_;
}
else
{
lean_object* v_snd_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3150_; 
v_snd_3132_ = lean_ctor_get(v_b_3122_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_b_3122_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_b_3122_, 0);
lean_dec(v_unused_3151_);
v___x_3134_ = v_b_3122_;
v_isShared_3135_ = v_isSharedCheck_3150_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_snd_3132_);
lean_dec(v_b_3122_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3150_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v_a_3138_; lean_object* v_a_3145_; 
v___x_3136_ = lean_box(0);
v_a_3145_ = lean_array_uget_borrowed(v_as_3119_, v_i_3121_);
if (lean_obj_tag(v_a_3145_) == 0)
{
v_a_3138_ = v_snd_3132_;
goto v___jp_3137_;
}
else
{
lean_object* v_val_3146_; uint8_t v___x_3147_; 
v_val_3146_ = lean_ctor_get(v_a_3145_, 0);
v___x_3147_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_inc(v_val_3146_);
v___x_3148_ = l_Lean_LocalDecl_toExpr(v_val_3146_);
v___x_3149_ = lean_array_push(v_snd_3132_, v___x_3148_);
v_a_3138_ = v___x_3149_;
goto v___jp_3137_;
}
else
{
v_a_3138_ = v_snd_3132_;
goto v___jp_3137_;
}
}
v___jp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 1, v_a_3138_);
lean_ctor_set(v___x_3134_, 0, v___x_3136_);
v___x_3140_ = v___x_3134_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_a_3138_);
v___x_3140_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
size_t v___x_3141_; size_t v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = ((size_t)1ULL);
v___x_3142_ = lean_usize_add(v_i_3121_, v___x_3141_);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3119_, v_sz_3120_, v___x_3142_, v___x_3140_);
return v___x_3143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3152_, lean_object* v_sz_3153_, lean_object* v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
size_t v_sz_boxed_3163_; size_t v_i_boxed_3164_; lean_object* v_res_3165_; 
v_sz_boxed_3163_ = lean_unbox_usize(v_sz_3153_);
lean_dec(v_sz_3153_);
v_i_boxed_3164_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3152_, v_sz_boxed_3163_, v_i_boxed_3164_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v_as_3152_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3166_, lean_object* v_n_3167_, lean_object* v_b_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
if (lean_obj_tag(v_n_3167_) == 0)
{
lean_object* v_cs_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; size_t v_sz_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
v_cs_3176_ = lean_ctor_get(v_n_3167_, 0);
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v_b_3168_);
v_sz_3179_ = lean_array_size(v_cs_3176_);
v___x_3180_ = ((size_t)0ULL);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3166_, v_cs_3176_, v_sz_3179_, v___x_3180_, v___x_3178_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3196_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3196_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3196_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_fst_3186_; 
v_fst_3186_ = lean_ctor_get(v_a_3182_, 0);
if (lean_obj_tag(v_fst_3186_) == 0)
{
lean_object* v_snd_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_snd_3187_ = lean_ctor_get(v_a_3182_, 1);
lean_inc(v_snd_3187_);
lean_dec(v_a_3182_);
v___x_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_snd_3187_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3188_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
else
{
lean_object* v_val_3192_; lean_object* v___x_3194_; 
lean_inc_ref(v_fst_3186_);
lean_dec(v_a_3182_);
v_val_3192_ = lean_ctor_get(v_fst_3186_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v_fst_3186_, 1);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v_val_3192_);
v___x_3194_ = v___x_3184_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_val_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_a_3197_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3181_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3181_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_vs_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; size_t v_sz_3208_; size_t v___x_3209_; lean_object* v___x_3210_; 
v_vs_3205_ = lean_ctor_get(v_n_3167_, 0);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
lean_ctor_set(v___x_3207_, 1, v_b_3168_);
v_sz_3208_ = lean_array_size(v_vs_3205_);
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3205_, v_sz_3208_, v___x_3209_, v___x_3207_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3225_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v_fst_3215_; 
v_fst_3215_ = lean_ctor_get(v_a_3211_, 0);
if (lean_obj_tag(v_fst_3215_) == 0)
{
lean_object* v_snd_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v_snd_3216_ = lean_ctor_get(v_a_3211_, 1);
lean_inc(v_snd_3216_);
lean_dec(v_a_3211_);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v_snd_3216_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3217_);
v___x_3219_ = v___x_3213_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
else
{
lean_object* v_val_3221_; lean_object* v___x_3223_; 
lean_inc_ref(v_fst_3215_);
lean_dec(v_a_3211_);
v_val_3221_ = lean_ctor_get(v_fst_3215_, 0);
lean_inc(v_val_3221_);
lean_dec_ref_known(v_fst_3215_, 1);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v_val_3221_);
v___x_3223_ = v___x_3213_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_val_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_a_3226_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3210_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3210_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3234_, lean_object* v_as_3235_, size_t v_sz_3236_, size_t v_i_3237_, lean_object* v_b_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_usize_dec_lt(v_i_3237_, v_sz_3236_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_b_3238_);
return v___x_3247_;
}
else
{
lean_object* v_snd_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3282_; 
v_snd_3248_ = lean_ctor_get(v_b_3238_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_b_3238_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; 
v_unused_3283_ = lean_ctor_get(v_b_3238_, 0);
lean_dec(v_unused_3283_);
v___x_3250_ = v_b_3238_;
v_isShared_3251_ = v_isSharedCheck_3282_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_snd_3248_);
lean_dec(v_b_3238_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3282_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v_a_3253_; lean_object* v___x_3254_; 
v___x_3252_ = lean_box(0);
v_a_3253_ = lean_array_uget_borrowed(v_as_3235_, v_i_3237_);
lean_inc(v_snd_3248_);
v___x_3254_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3234_, v_a_3253_, v_snd_3248_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3273_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3273_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3273_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
if (lean_obj_tag(v_a_3255_) == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_a_3255_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3259_);
v___x_3261_ = v___x_3250_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_snd_3248_);
v___x_3261_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3261_);
v___x_3263_ = v___x_3257_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; 
lean_del_object(v___x_3257_);
lean_dec(v_snd_3248_);
v_a_3266_ = lean_ctor_get(v_a_3255_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v_a_3255_, 1);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 1, v_a_3266_);
lean_ctor_set(v___x_3250_, 0, v___x_3252_);
v___x_3268_ = v___x_3250_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_a_3266_);
v___x_3268_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
size_t v___x_3269_; size_t v___x_3270_; 
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_add(v_i_3237_, v___x_3269_);
v_i_3237_ = v___x_3270_;
v_b_3238_ = v___x_3268_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_del_object(v___x_3250_);
lean_dec(v_snd_3248_);
v_a_3274_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3254_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3254_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3284_, lean_object* v_as_3285_, lean_object* v_sz_3286_, lean_object* v_i_3287_, lean_object* v_b_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
size_t v_sz_boxed_3296_; size_t v_i_boxed_3297_; lean_object* v_res_3298_; 
v_sz_boxed_3296_ = lean_unbox_usize(v_sz_3286_);
lean_dec(v_sz_3286_);
v_i_boxed_3297_ = lean_unbox_usize(v_i_3287_);
lean_dec(v_i_3287_);
v_res_3298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3284_, v_as_3285_, v_sz_boxed_3296_, v_i_boxed_3297_, v_b_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec_ref(v_as_3285_);
lean_dec_ref(v_init_3284_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3299_, lean_object* v_n_3300_, lean_object* v_b_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3299_, v_n_3300_, v_b_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec_ref(v_n_3300_);
lean_dec_ref(v_init_3299_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3310_, lean_object* v_init_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v_root_3319_; lean_object* v_tail_3320_; lean_object* v___x_3321_; 
v_root_3319_ = lean_ctor_get(v_t_3310_, 0);
v_tail_3320_ = lean_ctor_get(v_t_3310_, 1);
lean_inc_ref(v_init_3311_);
v___x_3321_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3311_, v_root_3319_, v_init_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec_ref(v_init_3311_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3358_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3358_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3358_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
if (lean_obj_tag(v_a_3322_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; 
v_a_3326_ = lean_ctor_get(v_a_3322_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v_a_3322_, 1);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v_a_3326_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; size_t v_sz_3333_; size_t v___x_3334_; lean_object* v___x_3335_; 
lean_del_object(v___x_3324_);
v_a_3330_ = lean_ctor_get(v_a_3322_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v_a_3322_, 1);
v___x_3331_ = lean_box(0);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v_a_3330_);
v_sz_3333_ = lean_array_size(v_tail_3320_);
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3320_, v_sz_3333_, v___x_3334_, v___x_3332_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3349_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3349_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3349_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_fst_3340_; 
v_fst_3340_ = lean_ctor_get(v_a_3336_, 0);
if (lean_obj_tag(v_fst_3340_) == 0)
{
lean_object* v_snd_3341_; lean_object* v___x_3343_; 
v_snd_3341_ = lean_ctor_get(v_a_3336_, 1);
lean_inc(v_snd_3341_);
lean_dec(v_a_3336_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_snd_3341_);
v___x_3343_ = v___x_3338_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_snd_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3347_; 
lean_inc_ref(v_fst_3340_);
lean_dec(v_a_3336_);
v_val_3345_ = lean_ctor_get(v_fst_3340_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v_fst_3340_, 1);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_val_3345_);
v___x_3347_ = v___x_3338_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_val_3345_);
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
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3335_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3335_);
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
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
v_a_3359_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3321_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3321_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3367_, lean_object* v_init_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3367_, v_init_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec_ref(v_t_3367_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_lctx_3386_; lean_object* v_decls_3387_; lean_object* v_hs_3388_; lean_object* v___x_3389_; 
v_lctx_3386_ = lean_ctor_get(v___y_3381_, 2);
v_decls_3387_ = lean_ctor_get(v_lctx_3386_, 1);
v_hs_3388_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3389_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3387_, v_hs_3388_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3398_, lean_object* v_cfg_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
if (v_only_3398_ == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_toApplyRulesConfig_3408_; lean_object* v_a_3409_; uint8_t v_symm_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_toApplyRulesConfig_3408_ = lean_ctor_get(v_cfg_3399_, 0);
v_a_3409_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3407_, 1);
v_symm_3410_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3408_, sizeof(void*)*2 + 1);
v___x_3411_ = lean_array_to_list(v_a_3409_);
v___x_3412_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3410_, v___x_3411_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v___x_3412_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
v_a_3413_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3407_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3407_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_box(0);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3423_, lean_object* v_cfg_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v_only_boxed_3432_; lean_object* v_res_3433_; 
v_only_boxed_3432_ = lean_unbox(v_only_3423_);
v_res_3433_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3432_, v_cfg_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_cfg_3424_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3434_, lean_object* v_lemmas_3435_, uint8_t v_only_3436_, lean_object* v_g_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_toApplyRulesConfig_3443_; uint8_t v_intro_3444_; uint8_t v_constructor_3445_; uint8_t v_suggestions_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3459_; 
v_toApplyRulesConfig_3443_ = lean_ctor_get(v_cfg_3434_, 0);
v_intro_3444_ = lean_ctor_get_uint8(v_cfg_3434_, sizeof(void*)*1 + 1);
v_constructor_3445_ = lean_ctor_get_uint8(v_cfg_3434_, sizeof(void*)*1 + 2);
v_suggestions_3446_ = lean_ctor_get_uint8(v_cfg_3434_, sizeof(void*)*1 + 3);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_cfg_3434_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3448_ = v_cfg_3434_;
v_isShared_3449_ = v_isSharedCheck_3459_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_toApplyRulesConfig_3443_);
lean_dec(v_cfg_3434_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3459_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v_ctx_3451_; uint8_t v___x_3452_; lean_object* v___x_3454_; 
v___x_3450_ = lean_box(v_only_3436_);
v_ctx_3451_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3451_, 0, v___x_3450_);
v___x_3452_ = 0;
if (v_isShared_3449_ == 0)
{
v___x_3454_ = v___x_3448_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_toApplyRulesConfig_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3458_, sizeof(void*)*1 + 1, v_intro_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3458_, sizeof(void*)*1 + 2, v_constructor_3445_);
lean_ctor_set_uint8(v_reuseFailAlloc_3458_, sizeof(void*)*1 + 3, v_suggestions_3446_);
v___x_3454_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*1, v___x_3452_);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_g_3437_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3454_, v_lemmas_3435_, v_ctx_3451_, v___x_3456_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3460_, lean_object* v_lemmas_3461_, lean_object* v_only_3462_, lean_object* v_g_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
uint8_t v_only_boxed_3469_; lean_object* v_res_3470_; 
v_only_boxed_3469_ = lean_unbox(v_only_3462_);
v_res_3470_ = l_Lean_MVarId_applyRules(v_cfg_3460_, v_lemmas_3461_, v_only_boxed_3469_, v_g_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3471_, size_t v_sz_3472_, size_t v_i_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3471_, v_sz_3472_, v_i_3473_, v_b_3474_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3483_, lean_object* v_sz_3484_, lean_object* v_i_3485_, lean_object* v_b_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
size_t v_sz_boxed_3494_; size_t v_i_boxed_3495_; lean_object* v_res_3496_; 
v_sz_boxed_3494_ = lean_unbox_usize(v_sz_3484_);
lean_dec(v_sz_3484_);
v_i_boxed_3495_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_res_3496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3483_, v_sz_boxed_3494_, v_i_boxed_3495_, v_b_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v_as_3483_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3497_, size_t v_sz_3498_, size_t v_i_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3497_, v_sz_3498_, v_i_3499_, v_b_3500_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3509_, lean_object* v_sz_3510_, lean_object* v_i_3511_, lean_object* v_b_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
size_t v_sz_boxed_3520_; size_t v_i_boxed_3521_; lean_object* v_res_3522_; 
v_sz_boxed_3520_ = lean_unbox_usize(v_sz_3510_);
lean_dec(v_sz_3510_);
v_i_boxed_3521_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_res_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3509_, v_sz_boxed_3520_, v_i_boxed_3521_, v_b_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v_as_3509_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = lean_box(0);
v___x_3532_ = 1;
v___x_3533_ = l_Lean_Elab_Term_elabTerm(v_t_3523_, v___x_3531_, v___x_3532_, v___x_3532_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_ref_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_ref_3548_ = lean_ctor_get(v___y_3545_, 2);
v___x_3549_ = 0;
v___x_3550_ = l_Lean_SourceInfo_fromRef(v_ref_3548_, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3557_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object* v_a_3558_, lean_object* v_x_3559_){
_start:
{
if (lean_obj_tag(v_x_3559_) == 0)
{
uint8_t v___x_3560_; 
v___x_3560_ = 0;
return v___x_3560_;
}
else
{
lean_object* v_head_3561_; lean_object* v_tail_3562_; uint8_t v___x_3563_; 
v_head_3561_ = lean_ctor_get(v_x_3559_, 0);
v_tail_3562_ = lean_ctor_get(v_x_3559_, 1);
v___x_3563_ = lean_expr_eqv(v_a_3558_, v_head_3561_);
if (v___x_3563_ == 0)
{
v_x_3559_ = v_tail_3562_;
goto _start;
}
else
{
return v___x_3563_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
uint8_t v_res_3567_; lean_object* v_r_3568_; 
v_res_3567_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3565_, v_x_3566_);
lean_dec(v_x_3566_);
lean_dec_ref(v_a_3565_);
v_r_3568_ = lean_box(v_res_3567_);
return v_r_3568_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(lean_object* v_ys_3569_, lean_object* v_x_3570_){
_start:
{
uint8_t v___x_3571_; 
v___x_3571_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_x_3570_, v_ys_3569_);
if (v___x_3571_ == 0)
{
uint8_t v___x_3572_; 
v___x_3572_ = 1;
return v___x_3572_;
}
else
{
uint8_t v___x_3573_; 
v___x_3573_ = 0;
return v___x_3573_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed(lean_object* v_ys_3574_, lean_object* v_x_3575_){
_start:
{
uint8_t v_res_3576_; lean_object* v_r_3577_; 
v_res_3576_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(v_ys_3574_, v_x_3575_);
lean_dec_ref(v_x_3575_);
lean_dec(v_ys_3574_);
v_r_3577_ = lean_box(v_res_3576_);
return v_r_3577_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_xs_3578_, lean_object* v_ys_3579_){
_start:
{
lean_object* v___f_3580_; lean_object* v___x_3581_; 
v___f_3580_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3580_, 0, v_ys_3579_);
v___x_3581_ = l_List_filter___redArg(v___f_3580_, v_xs_3578_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object* v_x_3582_, lean_object* v_x_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
if (lean_obj_tag(v_x_3582_) == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = l_List_reverse___redArg(v_x_3583_);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
else
{
lean_object* v_head_3593_; lean_object* v_tail_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3612_; 
v_head_3593_ = lean_ctor_get(v_x_3582_, 0);
v_tail_3594_ = lean_ctor_get(v_x_3582_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_x_3582_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3596_ = v_x_3582_;
v_isShared_3597_ = v_isSharedCheck_3612_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_tail_3594_);
lean_inc(v_head_3593_);
lean_dec(v_x_3582_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3612_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3593_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v_x_3583_);
lean_ctor_set(v___x_3596_, 0, v_a_3599_);
v___x_3601_ = v___x_3596_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3599_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_x_3583_);
v___x_3601_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_x_3582_ = v_tail_3594_;
v_x_3583_ = v___x_3601_;
goto _start;
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_del_object(v___x_3596_);
lean_dec(v_tail_3594_);
lean_dec(v_x_3583_);
v_a_3604_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3598_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3598_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_x_3613_, lean_object* v_x_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3613_, v_x_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3623_, uint8_t v_noDefaults_3624_, uint8_t v_star_3625_, lean_object* v_cfg_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
if (v_noDefaults_3624_ == 0)
{
goto v___jp_3634_;
}
else
{
if (v_star_3625_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec(v_remove_3623_);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
else
{
goto v___jp_3634_;
}
}
v___jp_3634_:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref_known(v___x_3635_, 1);
v___x_3637_ = lean_box(0);
v___x_3638_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_remove_3623_, v___x_3637_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_toApplyRulesConfig_3639_; lean_object* v_a_3640_; uint8_t v_symm_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v_toApplyRulesConfig_3639_ = lean_ctor_get(v_cfg_3626_, 0);
v_a_3640_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3638_, 1);
v_symm_3641_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3639_, sizeof(void*)*2 + 1);
v___x_3642_ = lean_array_to_list(v_a_3636_);
v___x_3643_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v___x_3642_, v_a_3640_);
v___x_3644_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3641_, v___x_3643_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v___x_3644_;
}
else
{
lean_dec(v_a_3636_);
return v___x_3638_;
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_remove_3623_);
v_a_3645_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3635_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3635_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3655_, lean_object* v_noDefaults_3656_, lean_object* v_star_3657_, lean_object* v_cfg_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
uint8_t v_noDefaults_boxed_3666_; uint8_t v_star_boxed_3667_; lean_object* v_res_3668_; 
v_noDefaults_boxed_3666_ = lean_unbox(v_noDefaults_3656_);
v_star_boxed_3667_ = lean_unbox(v_star_3657_);
v_res_3668_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3655_, v_noDefaults_boxed_3666_, v_star_boxed_3667_, v_cfg_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v_cfg_3658_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t v_sz_3669_, size_t v_i_3670_, lean_object* v_bs_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_usize_dec_lt(v_i_3670_, v_sz_3669_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3676_, 0, v_bs_3671_);
return v___x_3676_;
}
else
{
lean_object* v_v_3677_; lean_object* v___x_3678_; lean_object* v_bs_x27_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_v_3677_ = lean_array_uget(v_bs_3671_, v_i_3670_);
v___x_3678_ = lean_unsigned_to_nat(0u);
v_bs_x27_3679_ = lean_array_uset(v_bs_3671_, v_i_3670_, v___x_3678_);
v___x_3680_ = l_Lean_Syntax_getId(v_v_3677_);
lean_dec(v_v_3677_);
v___x_3681_ = l_Lean_labelled(v___x_3680_, v___y_3672_, v___y_3673_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3681_, 1);
v___x_3683_ = ((size_t)1ULL);
v___x_3684_ = lean_usize_add(v_i_3670_, v___x_3683_);
v___x_3685_ = lean_array_uset(v_bs_x27_3679_, v_i_3670_, v_a_3682_);
v_i_3670_ = v___x_3684_;
v_bs_3671_ = v___x_3685_;
goto _start;
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec_ref(v_bs_x27_3679_);
v_a_3687_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3681_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3681_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object* v_sz_3695_, lean_object* v_i_3696_, lean_object* v_bs_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3695_);
lean_dec(v_sz_3695_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3696_);
lean_dec(v_i_3696_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_boxed_3701_, v_i_boxed_3702_, v_bs_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3704_, size_t v_i_3705_, size_t v_stop_3706_, lean_object* v_b_3707_){
_start:
{
uint8_t v___x_3708_; 
v___x_3708_ = lean_usize_dec_eq(v_i_3705_, v_stop_3706_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; size_t v___x_3711_; size_t v___x_3712_; 
v___x_3709_ = lean_array_uget_borrowed(v_as_3704_, v_i_3705_);
v___x_3710_ = l_Array_append___redArg(v_b_3707_, v___x_3709_);
v___x_3711_ = ((size_t)1ULL);
v___x_3712_ = lean_usize_add(v_i_3705_, v___x_3711_);
v_i_3705_ = v___x_3712_;
v_b_3707_ = v___x_3710_;
goto _start;
}
else
{
return v_b_3707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3714_, lean_object* v_i_3715_, lean_object* v_stop_3716_, lean_object* v_b_3717_){
_start:
{
size_t v_i_boxed_3718_; size_t v_stop_boxed_3719_; lean_object* v_res_3720_; 
v_i_boxed_3718_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_stop_boxed_3719_ = lean_unbox_usize(v_stop_3716_);
lean_dec(v_stop_3716_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3714_, v_i_boxed_3718_, v_stop_boxed_3719_, v_b_3717_);
lean_dec_ref(v_as_3714_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3721_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
if (lean_obj_tag(v_a_3739_) == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = l_List_reverse___redArg(v_a_3740_);
return v___x_3741_;
}
else
{
lean_object* v_head_3742_; lean_object* v_tail_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3752_; 
v_head_3742_ = lean_ctor_get(v_a_3739_, 0);
v_tail_3743_ = lean_ctor_get(v_a_3739_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_a_3739_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3745_ = v_a_3739_;
v_isShared_3746_ = v_isSharedCheck_3752_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_tail_3743_);
lean_inc(v_head_3742_);
lean_dec(v_a_3739_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3752_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___f_3747_; lean_object* v___x_3749_; 
v___f_3747_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3747_, 0, v_head_3742_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 1, v_a_3740_);
lean_ctor_set(v___x_3745_, 0, v___f_3747_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___f_3747_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_a_3740_);
v___x_3749_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
v_a_3739_ = v_tail_3743_;
v_a_3740_ = v___x_3749_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_a_3753_, lean_object* v_a_3754_){
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
lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3761_, 0, v_head_3756_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v_a_3754_);
lean_ctor_set(v___x_3759_, 0, v___x_3761_);
v___x_3763_ = v___x_3759_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3761_);
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
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3769_ = l_Lean_stringToMessageData(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3772_ = l_String_toRawSubstring_x27(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8(void){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3783_ = l_String_toRawSubstring_x27(v___x_3782_);
return v___x_3783_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13(void){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12));
v___x_3794_ = l_String_toRawSubstring_x27(v___x_3793_);
return v___x_3794_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3805_ = l_String_toRawSubstring_x27(v___x_3804_);
return v___x_3805_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3818_ = l_Lean_stringToMessageData(v___x_3817_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3819_, uint8_t v_star_3820_, lean_object* v_add_3821_, lean_object* v_remove_3822_, lean_object* v_use_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___f_3854_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; 
v___x_3852_ = lean_box(v_noDefaults_3819_);
v___x_3853_ = lean_box(v_star_3820_);
lean_inc(v_remove_3822_);
v___f_3854_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3854_, 0, v_remove_3822_);
lean_closure_set(v___f_3854_, 1, v___x_3852_);
lean_closure_set(v___f_3854_, 2, v___x_3853_);
if (v_star_3820_ == 0)
{
v___y_3871_ = v_a_3824_;
v___y_3872_ = v_a_3825_;
v___y_3873_ = v_a_3826_;
v___y_3874_ = v_a_3827_;
goto v___jp_3870_;
}
else
{
if (v_noDefaults_3819_ == 0)
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v___f_3854_);
lean_dec_ref(v_use_3823_);
lean_dec(v_remove_3822_);
lean_dec(v_add_3821_);
v___x_3931_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3932_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3931_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
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
else
{
v___y_3871_ = v_a_3824_;
v___y_3872_ = v_a_3825_;
v___y_3873_ = v_a_3826_;
v___y_3874_ = v_a_3827_;
goto v___jp_3870_;
}
}
v___jp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___y_3830_);
lean_ctor_set(v___x_3832_, 1, v___y_3831_);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
v___jp_3834_:
{
uint8_t v___x_3841_; 
v___x_3841_ = l_List_isEmpty___redArg(v_remove_3822_);
lean_dec(v_remove_3822_);
if (v___x_3841_ == 0)
{
if (v_noDefaults_3819_ == 0)
{
v___y_3830_ = v___y_3840_;
v___y_3831_ = v___y_3837_;
goto v___jp_3829_;
}
else
{
if (v_star_3820_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3837_);
v___x_3842_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3843_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3842_, v___y_3836_, v___y_3838_, v___y_3835_, v___y_3839_);
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3843_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
else
{
v___y_3830_ = v___y_3840_;
v___y_3831_ = v___y_3837_;
goto v___jp_3829_;
}
}
}
else
{
v___y_3830_ = v___y_3840_;
v___y_3831_ = v___y_3837_;
goto v___jp_3829_;
}
}
v___jp_3855_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_array_to_list(v___y_3862_);
lean_inc(v___y_3861_);
v___x_3864_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3863_, v___y_3861_);
if (v_noDefaults_3819_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3821_, v___y_3861_);
v___x_3866_ = l_List_appendTR___redArg(v___x_3865_, v___x_3864_);
v___x_3867_ = l_List_appendTR___redArg(v___x_3866_, v___y_3858_);
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3856_;
v___y_3837_ = v___f_3854_;
v___y_3838_ = v___y_3859_;
v___y_3839_ = v___y_3860_;
v___y_3840_ = v___x_3867_;
goto v___jp_3834_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec(v___y_3858_);
v___x_3868_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3821_, v___y_3861_);
v___x_3869_ = l_List_appendTR___redArg(v___x_3868_, v___x_3864_);
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3856_;
v___y_3837_ = v___f_3854_;
v___y_3838_ = v___y_3859_;
v___y_3839_ = v___y_3860_;
v___y_3840_ = v___x_3869_;
goto v___jp_3834_;
}
}
v___jp_3870_:
{
lean_object* v_toCold_3875_; lean_object* v_ref_3876_; lean_object* v_quotContext_3877_; lean_object* v_currMacroScope_3878_; uint8_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v_a_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v_a_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v_a_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; size_t v_sz_3913_; size_t v___x_3914_; lean_object* v___x_3915_; 
v_toCold_3875_ = lean_ctor_get(v___y_3873_, 0);
v_ref_3876_ = lean_ctor_get(v___y_3873_, 2);
v_quotContext_3877_ = lean_ctor_get(v_toCold_3875_, 8);
v_currMacroScope_3878_ = lean_ctor_get(v_toCold_3875_, 9);
v___x_3879_ = 0;
v___x_3880_ = l_Lean_SourceInfo_fromRef(v_ref_3876_, v___x_3879_);
v___x_3881_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3882_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3878_, 4);
lean_inc_n(v_quotContext_3877_, 4);
v___x_3883_ = l_Lean_addMacroScope(v_quotContext_3877_, v___x_3882_, v_currMacroScope_3878_);
v___x_3884_ = lean_box(0);
v___x_3885_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6));
v___x_3886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3880_);
lean_ctor_set(v___x_3886_, 1, v___x_3881_);
lean_ctor_set(v___x_3886_, 2, v___x_3883_);
lean_ctor_set(v___x_3886_, 3, v___x_3885_);
v___x_3887_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref(v___x_3887_);
v___x_3889_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8);
v___x_3890_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9));
v___x_3891_ = l_Lean_addMacroScope(v_quotContext_3877_, v___x_3890_, v_currMacroScope_3878_);
v___x_3892_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3893_, 0, v_a_3888_);
lean_ctor_set(v___x_3893_, 1, v___x_3889_);
lean_ctor_set(v___x_3893_, 2, v___x_3891_);
lean_ctor_set(v___x_3893_, 3, v___x_3892_);
v___x_3894_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v___x_3894_);
v___x_3896_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13);
v___x_3897_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14));
v___x_3898_ = l_Lean_addMacroScope(v_quotContext_3877_, v___x_3897_, v_currMacroScope_3878_);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16));
v___x_3900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3900_, 0, v_a_3895_);
lean_ctor_set(v___x_3900_, 1, v___x_3896_);
lean_ctor_set(v___x_3900_, 2, v___x_3898_);
lean_ctor_set(v___x_3900_, 3, v___x_3899_);
v___x_3901_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref(v___x_3901_);
v___x_3903_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18);
v___x_3904_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3905_ = l_Lean_addMacroScope(v_quotContext_3877_, v___x_3904_, v_currMacroScope_3878_);
v___x_3906_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3907_, 0, v_a_3902_);
lean_ctor_set(v___x_3907_, 1, v___x_3903_);
lean_ctor_set(v___x_3907_, 2, v___x_3905_);
lean_ctor_set(v___x_3907_, 3, v___x_3906_);
v___x_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___x_3884_);
v___x_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3900_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3893_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3886_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3911_, v___x_3884_);
v_sz_3913_ = lean_array_size(v_use_3823_);
v___x_3914_ = ((size_t)0ULL);
v___x_3915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3913_, v___x_3914_, v_use_3823_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3919_ = lean_array_get_size(v_a_3916_);
v___x_3920_ = lean_nat_dec_lt(v___x_3917_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_dec(v_a_3916_);
v___y_3856_ = v___y_3871_;
v___y_3857_ = v___y_3873_;
v___y_3858_ = v___x_3912_;
v___y_3859_ = v___y_3872_;
v___y_3860_ = v___y_3874_;
v___y_3861_ = v___x_3884_;
v___y_3862_ = v___x_3918_;
goto v___jp_3855_;
}
else
{
size_t v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_usize_of_nat(v___x_3919_);
v___x_3922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3916_, v___x_3914_, v___x_3921_, v___x_3918_);
lean_dec(v_a_3916_);
v___y_3856_ = v___y_3871_;
v___y_3857_ = v___y_3873_;
v___y_3858_ = v___x_3912_;
v___y_3859_ = v___y_3872_;
v___y_3860_ = v___y_3874_;
v___y_3861_ = v___x_3884_;
v___y_3862_ = v___x_3922_;
goto v___jp_3855_;
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v___x_3912_);
lean_dec_ref(v___f_3854_);
lean_dec(v_remove_3822_);
lean_dec(v_add_3821_);
v_a_3923_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3915_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3915_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3941_, lean_object* v_star_3942_, lean_object* v_add_3943_, lean_object* v_remove_3944_, lean_object* v_use_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
uint8_t v_noDefaults_boxed_3951_; uint8_t v_star_boxed_3952_; lean_object* v_res_3953_; 
v_noDefaults_boxed_3951_ = lean_unbox(v_noDefaults_3941_);
v_star_boxed_3952_ = lean_unbox(v_star_3942_);
v_res_3953_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3951_, v_star_boxed_3952_, v_add_3943_, v_remove_3944_, v_use_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t v_sz_3954_, size_t v_i_3955_, lean_object* v_bs_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3954_, v_i_3955_, v_bs_3956_, v___y_3959_, v___y_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object* v_sz_3963_, lean_object* v_i_3964_, lean_object* v_bs_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
size_t v_sz_boxed_3971_; size_t v_i_boxed_3972_; lean_object* v_res_3973_; 
v_sz_boxed_3971_ = lean_unbox_usize(v_sz_3963_);
lean_dec(v_sz_3963_);
v_i_boxed_3972_ = lean_unbox_usize(v_i_3964_);
lean_dec(v_i_3964_);
v_res_3973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_boxed_3971_, v_i_boxed_3972_, v_bs_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
return v_res_3973_;
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

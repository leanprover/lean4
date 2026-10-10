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
lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_77_;
v_res_77_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
return v_res_79_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(32u);
v___x_81_ = lean_mk_empty_array_with_capacity(v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_83_ = ((size_t)5ULL);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_unsigned_to_nat(32u);
v___x_86_ = lean_mk_empty_array_with_capacity(v___x_85_);
v___x_87_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0);
v___x_88_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_84_);
lean_ctor_set(v___x_88_, 3, v___x_84_);
lean_ctor_set_usize(v___x_88_, 4, v___x_83_);
return v___x_88_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_traceState_92_; lean_object* v_traces_93_; lean_object* v___x_94_; lean_object* v_traceState_95_; lean_object* v_env_96_; lean_object* v_nextMacroScope_97_; lean_object* v_ngen_98_; lean_object* v_auxDeclNGen_99_; lean_object* v_cache_100_; lean_object* v_recordedDeps_101_; lean_object* v_messages_102_; lean_object* v_infoState_103_; lean_object* v_snapshotTasks_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_123_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_traceState_92_ = lean_ctor_get(v___x_91_, 4);
lean_inc_ref(v_traceState_92_);
lean_dec(v___x_91_);
v_traces_93_ = lean_ctor_get(v_traceState_92_, 0);
lean_inc_ref(v_traces_93_);
lean_dec_ref(v_traceState_92_);
v___x_94_ = lean_st_ref_take(v___y_89_);
v_traceState_95_ = lean_ctor_get(v___x_94_, 4);
v_env_96_ = lean_ctor_get(v___x_94_, 0);
v_nextMacroScope_97_ = lean_ctor_get(v___x_94_, 1);
v_ngen_98_ = lean_ctor_get(v___x_94_, 2);
v_auxDeclNGen_99_ = lean_ctor_get(v___x_94_, 3);
v_cache_100_ = lean_ctor_get(v___x_94_, 5);
v_recordedDeps_101_ = lean_ctor_get(v___x_94_, 6);
v_messages_102_ = lean_ctor_get(v___x_94_, 7);
v_infoState_103_ = lean_ctor_get(v___x_94_, 8);
v_snapshotTasks_104_ = lean_ctor_get(v___x_94_, 9);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_123_ == 0)
{
v___x_106_ = v___x_94_;
v_isShared_107_ = v_isSharedCheck_123_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snapshotTasks_104_);
lean_inc(v_infoState_103_);
lean_inc(v_messages_102_);
lean_inc(v_recordedDeps_101_);
lean_inc(v_cache_100_);
lean_inc(v_traceState_95_);
lean_inc(v_auxDeclNGen_99_);
lean_inc(v_ngen_98_);
lean_inc(v_nextMacroScope_97_);
lean_inc(v_env_96_);
lean_dec(v___x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_123_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint64_t v_tid_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_121_; 
v_tid_108_ = lean_ctor_get_uint64(v_traceState_95_, sizeof(void*)*1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_traceState_95_);
if (v_isSharedCheck_121_ == 0)
{
lean_object* v_unused_122_; 
v_unused_122_ = lean_ctor_get(v_traceState_95_, 0);
lean_dec(v_unused_122_);
v___x_110_ = v_traceState_95_;
v_isShared_111_ = v_isSharedCheck_121_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_traceState_95_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_121_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_112_);
lean_ctor_set_uint64(v_reuseFailAlloc_120_, sizeof(void*)*1, v_tid_108_);
v___x_114_ = v_reuseFailAlloc_120_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_116_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 4, v___x_114_);
v___x_116_ = v___x_106_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_env_96_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_nextMacroScope_97_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_ngen_98_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_auxDeclNGen_99_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_119_, 5, v_cache_100_);
lean_ctor_set(v_reuseFailAlloc_119_, 6, v_recordedDeps_101_);
lean_ctor_set(v_reuseFailAlloc_119_, 7, v_messages_102_);
lean_ctor_set(v_reuseFailAlloc_119_, 8, v_infoState_103_);
lean_ctor_set(v_reuseFailAlloc_119_, 9, v_snapshotTasks_104_);
v___x_116_ = v_reuseFailAlloc_119_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_st_ref_put(v___y_89_, v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v_traces_93_);
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_89_ = stack[0].m_obj;
lean_object* v_res_124_;
v_res_124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_89_);
stack->m_obj
 = v_res_124_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_125_);
lean_dec(v___y_125_);
return v_res_127_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_128_ = stack[0].m_obj;
lean_object* v___y_129_ = stack[1].m_obj;
lean_object* v___y_130_ = stack[2].m_obj;
lean_object* v___y_131_ = stack[3].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_128_, v___y_129_, v___y_130_, v___y_131_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_140_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_141_, lean_object* v_opt_142_){
_start:
{
lean_object* v_name_143_; lean_object* v_defValue_144_; lean_object* v_map_145_; lean_object* v___x_146_; 
v_name_143_ = lean_ctor_get(v_opt_142_, 0);
v_defValue_144_ = lean_ctor_get(v_opt_142_, 1);
v_map_145_ = lean_ctor_get(v_opts_141_, 0);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_145_, v_name_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = lean_unbox(v_defValue_144_);
return v___x_147_;
}
else
{
lean_object* v_val_148_; 
v_val_148_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_146_, 1);
if (lean_obj_tag(v_val_148_) == 1)
{
uint8_t v_v_149_; 
v_v_149_ = lean_ctor_get_uint8(v_val_148_, 0);
lean_dec_ref_known(v_val_148_, 0);
return v_v_149_;
}
else
{
uint8_t v___x_150_; 
lean_dec(v_val_148_);
v___x_150_ = lean_unbox(v_defValue_144_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_141_ = stack[0].m_obj;
lean_object* v_opt_142_ = stack[1].m_obj;
uint8_t v_res_151_;
v_res_151_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_141_, v_opt_142_);
stack->m_num = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_152_, lean_object* v_opt_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_152_, v_opt_153_);
lean_dec_ref(v_opt_153_);
lean_dec_ref(v_opts_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_saveState___redArg(v___y_158_, v___y_160_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_164_ = lean_apply_5(v_x_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, lean_box(0));
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
lean_dec(v_a_163_);
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v_a_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_203_; 
v_a_174_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_203_ == 0)
{
v___x_176_ = v___x_164_;
v_isShared_177_ = v_isSharedCheck_203_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_203_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
uint8_t v___y_179_; uint8_t v___x_201_; 
v___x_201_ = l_Lean_Exception_isInterrupt(v_a_174_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
lean_inc(v_a_174_);
v___x_202_ = l_Lean_Exception_isRuntime(v_a_174_);
v___y_179_ = v___x_202_;
goto v___jp_178_;
}
else
{
v___y_179_ = v___x_201_;
goto v___jp_178_;
}
v___jp_178_:
{
if (v___y_179_ == 0)
{
lean_object* v___x_180_; 
lean_del_object(v___x_176_);
lean_dec(v_a_174_);
v___x_180_ = l_Lean_Meta_SavedState_restore___redArg(v_a_163_, v___y_158_, v___y_160_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_188_; 
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v___x_180_, 0);
lean_dec(v_unused_189_);
v___x_182_ = v___x_180_;
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
else
{
lean_dec(v___x_180_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_box(0);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_180_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_180_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
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
else
{
lean_object* v___x_199_; 
lean_dec(v_a_163_);
if (v_isShared_177_ == 0)
{
v___x_199_ = v___x_176_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_174_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_x_156_);
v_a_204_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_162_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_162_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_156_ = stack[0].m_obj;
lean_object* v___y_157_ = stack[1].m_obj;
lean_object* v___y_158_ = stack[2].m_obj;
lean_object* v___y_159_ = stack[3].m_obj;
lean_object* v___y_160_ = stack[4].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_220_, lean_object* v_x_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
return v___x_227_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_221_ = stack[1].m_obj;
lean_object* v___y_222_ = stack[2].m_obj;
lean_object* v___y_223_ = stack[3].m_obj;
lean_object* v___y_224_ = stack[4].m_obj;
lean_object* v___y_225_ = stack[5].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_box(0), v_x_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_229_, lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_229_, v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_236_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_240_, lean_object* v_x_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_248_ = l_Lean_MessageData_ofExpr(v_e_240_);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_240_ = stack[0].m_obj;
lean_object* v_x_241_ = stack[1].m_obj;
lean_object* v___y_242_ = stack[2].m_obj;
lean_object* v___y_243_ = stack[3].m_obj;
lean_object* v___y_244_ = stack[4].m_obj;
lean_object* v___y_245_ = stack[5].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_240_, v_x_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_252_, lean_object* v_x_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_252_, v_x_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec_ref(v_x_253_);
return v_res_259_;
}
}
lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_260_, uint8_t v___x_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_x_263_);
return v___x_269_;
}
else
{
lean_object* v_head_270_; lean_object* v_tail_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_295_; 
v_head_270_ = lean_ctor_get(v_x_262_, 0);
v_tail_271_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_295_ == 0)
{
v___x_273_ = v_x_262_;
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_tail_271_);
lean_inc(v_head_270_);
lean_dec(v_x_262_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v_a_276_; lean_object* v___x_282_; 
lean_inc(v_head_270_);
v___x_282_ = l_Lean_MVarId_inferInstance(v_head_270_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_dec_ref_known(v___x_282_, 1);
v_a_276_ = v___x_260_;
goto v___jp_275_;
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_294_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_294_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_294_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_294_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
uint8_t v___y_288_; uint8_t v___x_292_; 
v___x_292_ = l_Lean_Exception_isInterrupt(v_a_283_);
if (v___x_292_ == 0)
{
uint8_t v___x_293_; 
lean_inc(v_a_283_);
v___x_293_ = l_Lean_Exception_isRuntime(v_a_283_);
v___y_288_ = v___x_293_;
goto v___jp_287_;
}
else
{
v___y_288_ = v___x_292_;
goto v___jp_287_;
}
v___jp_287_:
{
if (v___y_288_ == 0)
{
lean_del_object(v___x_285_);
lean_dec(v_a_283_);
v_a_276_ = v___x_261_;
goto v___jp_275_;
}
else
{
lean_object* v___x_290_; 
lean_del_object(v___x_273_);
lean_dec(v_tail_271_);
lean_dec(v_head_270_);
lean_dec(v_x_263_);
if (v_isShared_286_ == 0)
{
v___x_290_ = v___x_285_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_283_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
v___jp_275_:
{
if (v_a_276_ == 0)
{
lean_del_object(v___x_273_);
lean_dec(v_head_270_);
v_x_262_ = v_tail_271_;
goto _start;
}
else
{
lean_object* v___x_279_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v_x_263_);
v___x_279_ = v___x_273_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_head_270_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_x_263_);
v___x_279_ = v_reuseFailAlloc_281_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
v_x_262_ = v_tail_271_;
v_x_263_ = v___x_279_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_260_ = stack[0].m_num;
uint8_t v___x_261_ = stack[1].m_num;
lean_object* v_x_262_ = stack[2].m_obj;
lean_object* v_x_263_ = stack[3].m_obj;
lean_object* v___y_264_ = stack[4].m_obj;
lean_object* v___y_265_ = stack[5].m_obj;
lean_object* v___y_266_ = stack[6].m_obj;
lean_object* v___y_267_ = stack[7].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_260_, v___x_261_, v_x_262_, v_x_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_297_, lean_object* v___x_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
uint8_t v___x_14056__boxed_306_; uint8_t v___x_14057__boxed_307_; lean_object* v_res_308_; 
v___x_14056__boxed_306_ = lean_unbox(v___x_297_);
v___x_14057__boxed_307_ = lean_unbox(v___x_298_);
v_res_308_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_14056__boxed_306_, v___x_14057__boxed_307_, v_x_299_, v_x_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_308_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v_env_316_; uint8_t v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v_toCold_320_; lean_object* v_mctx_321_; lean_object* v_lctx_322_; lean_object* v_options_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_315_ = lean_st_ref_get(v___y_313_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_env_316_);
lean_dec(v___x_315_);
v___x_317_ = 0;
v_env_318_ = l_Lean_Environment_setRecordingDeps(v_env_316_, v___x_317_);
v___x_319_ = lean_st_ref_get(v___y_311_);
v_toCold_320_ = lean_ctor_get(v___y_312_, 0);
v_mctx_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_mctx_321_);
lean_dec(v___x_319_);
v_lctx_322_ = lean_ctor_get(v___y_310_, 2);
v_options_323_ = lean_ctor_get(v_toCold_320_, 2);
lean_inc_ref(v_options_323_);
lean_inc_ref(v_lctx_322_);
v___x_324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_324_, 0, v_env_318_);
lean_ctor_set(v___x_324_, 1, v_mctx_321_);
lean_ctor_set(v___x_324_, 2, v_lctx_322_);
lean_ctor_set(v___x_324_, 3, v_options_323_);
v___x_325_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_msgData_309_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_309_ = stack[0].m_obj;
lean_object* v___y_310_ = stack[1].m_obj;
lean_object* v___y_311_ = stack[2].m_obj;
lean_object* v___y_312_ = stack[3].m_obj;
lean_object* v___y_313_ = stack[4].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_335_, size_t v_i_336_, lean_object* v_bs_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_336_, v_sz_335_);
if (v___x_338_ == 0)
{
return v_bs_337_;
}
else
{
lean_object* v_v_339_; lean_object* v_msg_340_; lean_object* v___x_341_; lean_object* v_bs_x27_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_v_339_ = lean_array_uget_borrowed(v_bs_337_, v_i_336_);
v_msg_340_ = lean_ctor_get(v_v_339_, 1);
lean_inc_ref(v_msg_340_);
v___x_341_ = lean_unsigned_to_nat(0u);
v_bs_x27_342_ = lean_array_uset(v_bs_337_, v_i_336_, v___x_341_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_336_, v___x_343_);
v___x_345_ = lean_array_uset(v_bs_x27_342_, v_i_336_, v_msg_340_);
v_i_336_ = v___x_344_;
v_bs_337_ = v___x_345_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_335_ = stack[0].m_num;
size_t v_i_336_ = stack[1].m_num;
lean_object* v_bs_337_ = stack[2].m_obj;
lean_object* v_res_347_;
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_335_, v_i_336_, v_bs_337_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_348_, lean_object* v_i_349_, lean_object* v_bs_350_){
_start:
{
size_t v_sz_boxed_351_; size_t v_i_boxed_352_; lean_object* v_res_353_; 
v_sz_boxed_351_ = lean_unbox_usize(v_sz_348_);
lean_dec(v_sz_348_);
v_i_boxed_352_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_351_, v_i_boxed_352_, v_bs_350_);
return v_res_353_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_354_, lean_object* v_data_355_, lean_object* v_ref_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_toCold_363_; lean_object* v_currRecDepth_364_; lean_object* v_ref_365_; uint16_t v_optionFlags_366_; uint8_t v_suppressElabErrors_367_; uint8_t v_isRecordingDeps_368_; lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_traceState_372_; lean_object* v_traces_373_; lean_object* v___x_374_; size_t v_sz_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v_msg_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_418_; 
v_toCold_363_ = lean_ctor_get(v___y_360_, 0);
v_currRecDepth_364_ = lean_ctor_get(v___y_360_, 1);
v_ref_365_ = lean_ctor_get(v___y_360_, 2);
v_optionFlags_366_ = lean_ctor_get_uint16(v___y_360_, sizeof(void*)*3);
v_suppressElabErrors_367_ = lean_ctor_get_uint8(v___y_360_, sizeof(void*)*3 + 2);
v_isRecordingDeps_368_ = lean_ctor_get_uint8(v___y_360_, sizeof(void*)*3 + 3);
v_ref_369_ = l_Lean_replaceRef(v_ref_356_, v_ref_365_);
lean_inc(v_currRecDepth_364_);
lean_inc_ref(v_toCold_363_);
v___x_370_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_370_, 0, v_toCold_363_);
lean_ctor_set(v___x_370_, 1, v_currRecDepth_364_);
lean_ctor_set(v___x_370_, 2, v_ref_369_);
lean_ctor_set_uint16(v___x_370_, sizeof(void*)*3, v_optionFlags_366_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*3 + 2, v_suppressElabErrors_367_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*3 + 3, v_isRecordingDeps_368_);
v___x_371_ = lean_st_ref_get(v___y_361_);
v_traceState_372_ = lean_ctor_get(v___x_371_, 4);
lean_inc_ref(v_traceState_372_);
lean_dec(v___x_371_);
v_traces_373_ = lean_ctor_get(v_traceState_372_, 0);
lean_inc_ref(v_traces_373_);
lean_dec_ref(v_traceState_372_);
v___x_374_ = l_Lean_PersistentArray_toArray___redArg(v_traces_373_);
lean_dec_ref(v_traces_373_);
v_sz_375_ = lean_array_size(v___x_374_);
v___x_376_ = ((size_t)0ULL);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_375_, v___x_376_, v___x_374_);
v_msg_378_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_378_, 0, v_data_355_);
lean_ctor_set(v_msg_378_, 1, v_msg_357_);
lean_ctor_set(v_msg_378_, 2, v___x_377_);
v___x_379_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_378_, v___y_358_, v___y_359_, v___x_370_, v___y_361_);
lean_dec_ref_known(v___x_370_, 3);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_418_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_418_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_418_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v_traceState_385_; lean_object* v_env_386_; lean_object* v_nextMacroScope_387_; lean_object* v_ngen_388_; lean_object* v_auxDeclNGen_389_; lean_object* v_cache_390_; lean_object* v_recordedDeps_391_; lean_object* v_messages_392_; lean_object* v_infoState_393_; lean_object* v_snapshotTasks_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_417_; 
v___x_384_ = lean_st_ref_take(v___y_361_);
v_traceState_385_ = lean_ctor_get(v___x_384_, 4);
v_env_386_ = lean_ctor_get(v___x_384_, 0);
v_nextMacroScope_387_ = lean_ctor_get(v___x_384_, 1);
v_ngen_388_ = lean_ctor_get(v___x_384_, 2);
v_auxDeclNGen_389_ = lean_ctor_get(v___x_384_, 3);
v_cache_390_ = lean_ctor_get(v___x_384_, 5);
v_recordedDeps_391_ = lean_ctor_get(v___x_384_, 6);
v_messages_392_ = lean_ctor_get(v___x_384_, 7);
v_infoState_393_ = lean_ctor_get(v___x_384_, 8);
v_snapshotTasks_394_ = lean_ctor_get(v___x_384_, 9);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_417_ == 0)
{
v___x_396_ = v___x_384_;
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snapshotTasks_394_);
lean_inc(v_infoState_393_);
lean_inc(v_messages_392_);
lean_inc(v_recordedDeps_391_);
lean_inc(v_cache_390_);
lean_inc(v_traceState_385_);
lean_inc(v_auxDeclNGen_389_);
lean_inc(v_ngen_388_);
lean_inc(v_nextMacroScope_387_);
lean_inc(v_env_386_);
lean_dec(v___x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint64_t v_tid_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_415_; 
v_tid_398_ = lean_ctor_get_uint64(v_traceState_385_, sizeof(void*)*1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_traceState_385_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_traceState_385_, 0);
lean_dec(v_unused_416_);
v___x_400_ = v_traceState_385_;
v_isShared_401_ = v_isSharedCheck_415_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_traceState_385_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_415_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_ref_356_);
lean_ctor_set(v___x_403_, 1, v_a_380_);
v___x_404_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_354_, v___x_403_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_404_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_404_);
lean_ctor_set_uint64(v_reuseFailAlloc_414_, sizeof(void*)*1, v_tid_398_);
v___x_406_ = v_reuseFailAlloc_414_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v___x_406_);
v___x_408_ = v___x_396_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_env_386_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_387_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_388_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_389_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_cache_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_recordedDeps_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_messages_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_infoState_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_snapshotTasks_394_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_st_ref_put(v___y_361_, v___x_408_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_402_);
v___x_411_ = v___x_382_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_402_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_354_ = stack[0].m_obj;
lean_object* v_data_355_ = stack[1].m_obj;
lean_object* v_ref_356_ = stack[2].m_obj;
lean_object* v_msg_357_ = stack[3].m_obj;
lean_object* v___y_358_ = stack[4].m_obj;
lean_object* v___y_359_ = stack[5].m_obj;
lean_object* v___y_360_ = stack[6].m_obj;
lean_object* v___y_361_ = stack[7].m_obj;
lean_object* v_res_419_;
v_res_419_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_354_, v_data_355_, v_ref_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_420_, lean_object* v_data_421_, lean_object* v_ref_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_420_, v_data_421_, v_ref_422_, v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_430_){
_start:
{
if (lean_obj_tag(v_e_430_) == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 2;
return v___x_431_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = 0;
return v___x_432_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_430_ = stack[0].m_obj;
uint8_t v_res_433_;
v_res_433_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_430_);
stack->m_num = v_res_433_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_434_);
lean_dec_ref(v_e_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_437_, lean_object* v_opt_438_){
_start:
{
lean_object* v_name_439_; lean_object* v_defValue_440_; lean_object* v_map_441_; lean_object* v___x_442_; 
v_name_439_ = lean_ctor_get(v_opt_438_, 0);
v_defValue_440_ = lean_ctor_get(v_opt_438_, 1);
v_map_441_ = lean_ctor_get(v_opts_437_, 0);
v___x_442_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_441_, v_name_439_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_inc(v_defValue_440_);
return v_defValue_440_;
}
else
{
lean_object* v_val_443_; 
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v___x_442_, 1);
if (lean_obj_tag(v_val_443_) == 3)
{
lean_object* v_v_444_; 
v_v_444_ = lean_ctor_get(v_val_443_, 0);
lean_inc(v_v_444_);
lean_dec_ref_known(v_val_443_, 1);
return v_v_444_;
}
else
{
lean_dec(v_val_443_);
lean_inc(v_defValue_440_);
return v_defValue_440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_445_, lean_object* v_opt_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_445_, v_opt_446_);
lean_dec_ref(v_opt_446_);
lean_dec_ref(v_opts_445_);
return v_res_447_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v_x_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v_x_448_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v_x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 1);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v_x_448_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v_x_448_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v_x_448_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_448_ = stack[0].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_448_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_467_);
return v_res_469_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_470_; double v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_float_of_nat(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_475_; double v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(1000u);
v___x_476_ = lean_float_of_nat(v___x_475_);
return v___x_476_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_477_, uint8_t v_collapsed_478_, lean_object* v_tag_479_, lean_object* v_opts_480_, uint8_t v_clsEnabled_481_, lean_object* v_oldTraces_482_, lean_object* v_msg_483_, lean_object* v_resStartStop_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_fst_490_; lean_object* v_snd_491_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_data_495_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___y_511_; lean_object* v_a_512_; uint8_t v___y_527_; double v___y_559_; 
v_fst_490_ = lean_ctor_get(v_resStartStop_484_, 0);
lean_inc(v_fst_490_);
v_snd_491_ = lean_ctor_get(v_resStartStop_484_, 1);
lean_inc(v_snd_491_);
lean_dec_ref(v_resStartStop_484_);
v_fst_506_ = lean_ctor_get(v_snd_491_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v_snd_491_, 1);
lean_inc(v_snd_507_);
lean_dec(v_snd_491_);
v___x_508_ = l_Lean_trace_profiler;
v___x_509_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_480_, v___x_508_);
if (v___x_509_ == 0)
{
v___y_527_ = v___x_509_;
goto v___jp_526_;
}
else
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = l_Lean_trace_profiler_useHeartbeats;
v___x_565_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_480_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; double v___x_568_; double v___x_569_; double v___x_570_; 
v___x_566_ = l_Lean_trace_profiler_threshold;
v___x_567_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_480_, v___x_566_);
v___x_568_ = lean_float_of_nat(v___x_567_);
v___x_569_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_570_ = lean_float_div(v___x_568_, v___x_569_);
v___y_559_ = v___x_570_;
goto v___jp_558_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; double v___x_573_; 
v___x_571_ = l_Lean_trace_profiler_threshold;
v___x_572_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_480_, v___x_571_);
v___x_573_ = lean_float_of_nat(v___x_572_);
v___y_559_ = v___x_573_;
goto v___jp_558_;
}
}
v___jp_492_:
{
lean_object* v___x_496_; 
lean_inc(v___y_494_);
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_482_, v_data_495_, v___y_494_, v___y_493_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; 
lean_dec_ref_known(v___x_496_, 1);
v___x_497_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_490_);
return v___x_497_;
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_fst_490_);
v_a_498_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_496_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
v___jp_510_:
{
uint8_t v_result_513_; lean_object* v___x_514_; lean_object* v___x_515_; double v___x_516_; lean_object* v_data_517_; 
v_result_513_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_490_);
v___x_514_ = lean_box(v_result_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_479_);
lean_inc_ref(v___x_515_);
lean_inc(v_cls_477_);
v_data_517_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_517_, 0, v_cls_477_);
lean_ctor_set(v_data_517_, 1, v___x_515_);
lean_ctor_set(v_data_517_, 2, v_tag_479_);
lean_ctor_set_float(v_data_517_, sizeof(void*)*3, v___x_516_);
lean_ctor_set_float(v_data_517_, sizeof(void*)*3 + 8, v___x_516_);
lean_ctor_set_uint8(v_data_517_, sizeof(void*)*3 + 16, v_collapsed_478_);
if (v___x_509_ == 0)
{
lean_dec_ref_known(v___x_515_, 1);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_dec_ref(v_tag_479_);
lean_dec(v_cls_477_);
v___y_493_ = v_a_512_;
v___y_494_ = v___y_511_;
v_data_495_ = v_data_517_;
goto v___jp_492_;
}
else
{
lean_object* v_data_518_; double v___x_519_; double v___x_520_; 
lean_dec_ref_known(v_data_517_, 3);
v_data_518_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_518_, 0, v_cls_477_);
lean_ctor_set(v_data_518_, 1, v___x_515_);
lean_ctor_set(v_data_518_, 2, v_tag_479_);
v___x_519_ = lean_unbox_float(v_fst_506_);
lean_dec(v_fst_506_);
lean_ctor_set_float(v_data_518_, sizeof(void*)*3, v___x_519_);
v___x_520_ = lean_unbox_float(v_snd_507_);
lean_dec(v_snd_507_);
lean_ctor_set_float(v_data_518_, sizeof(void*)*3 + 8, v___x_520_);
lean_ctor_set_uint8(v_data_518_, sizeof(void*)*3 + 16, v_collapsed_478_);
v___y_493_ = v_a_512_;
v___y_494_ = v___y_511_;
v_data_495_ = v_data_518_;
goto v___jp_492_;
}
}
v___jp_521_:
{
lean_object* v_ref_522_; lean_object* v___x_523_; 
v_ref_522_ = lean_ctor_get(v___y_487_, 2);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v_fst_490_);
v___x_523_ = lean_apply_6(v_msg_483_, v_fst_490_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, lean_box(0));
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___y_511_ = v_ref_522_;
v_a_512_ = v_a_524_;
goto v___jp_510_;
}
else
{
lean_object* v___x_525_; 
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_511_ = v_ref_522_;
v_a_512_ = v___x_525_;
goto v___jp_510_;
}
}
v___jp_526_:
{
if (v_clsEnabled_481_ == 0)
{
if (v___y_527_ == 0)
{
lean_object* v___x_528_; lean_object* v_traceState_529_; lean_object* v_env_530_; lean_object* v_nextMacroScope_531_; lean_object* v_ngen_532_; lean_object* v_auxDeclNGen_533_; lean_object* v_cache_534_; lean_object* v_recordedDeps_535_; lean_object* v_messages_536_; lean_object* v_infoState_537_; lean_object* v_snapshotTasks_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_dec_ref(v_msg_483_);
lean_dec_ref(v_tag_479_);
lean_dec(v_cls_477_);
v___x_528_ = lean_st_ref_take(v___y_488_);
v_traceState_529_ = lean_ctor_get(v___x_528_, 4);
v_env_530_ = lean_ctor_get(v___x_528_, 0);
v_nextMacroScope_531_ = lean_ctor_get(v___x_528_, 1);
v_ngen_532_ = lean_ctor_get(v___x_528_, 2);
v_auxDeclNGen_533_ = lean_ctor_get(v___x_528_, 3);
v_cache_534_ = lean_ctor_get(v___x_528_, 5);
v_recordedDeps_535_ = lean_ctor_get(v___x_528_, 6);
v_messages_536_ = lean_ctor_get(v___x_528_, 7);
v_infoState_537_ = lean_ctor_get(v___x_528_, 8);
v_snapshotTasks_538_ = lean_ctor_get(v___x_528_, 9);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_557_ == 0)
{
v___x_540_ = v___x_528_;
v_isShared_541_ = v_isSharedCheck_557_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snapshotTasks_538_);
lean_inc(v_infoState_537_);
lean_inc(v_messages_536_);
lean_inc(v_recordedDeps_535_);
lean_inc(v_cache_534_);
lean_inc(v_traceState_529_);
lean_inc(v_auxDeclNGen_533_);
lean_inc(v_ngen_532_);
lean_inc(v_nextMacroScope_531_);
lean_inc(v_env_530_);
lean_dec(v___x_528_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_557_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint64_t v_tid_542_; lean_object* v_traces_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_556_; 
v_tid_542_ = lean_ctor_get_uint64(v_traceState_529_, sizeof(void*)*1);
v_traces_543_ = lean_ctor_get(v_traceState_529_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_traceState_529_);
if (v_isSharedCheck_556_ == 0)
{
v___x_545_ = v_traceState_529_;
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_traces_543_);
lean_dec(v_traceState_529_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_482_, v_traces_543_);
lean_dec_ref(v_traces_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_547_);
lean_ctor_set_uint64(v_reuseFailAlloc_555_, sizeof(void*)*1, v_tid_542_);
v___x_549_ = v_reuseFailAlloc_555_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 4, v___x_549_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_env_530_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_nextMacroScope_531_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_ngen_532_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_auxDeclNGen_533_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_cache_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_recordedDeps_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v_messages_536_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_infoState_537_);
lean_ctor_set(v_reuseFailAlloc_554_, 9, v_snapshotTasks_538_);
v___x_551_ = v_reuseFailAlloc_554_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_st_ref_put(v___y_488_, v___x_551_);
v___x_553_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_490_);
return v___x_553_;
}
}
}
}
}
else
{
goto v___jp_521_;
}
}
else
{
goto v___jp_521_;
}
}
v___jp_558_:
{
double v___x_560_; double v___x_561_; double v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_unbox_float(v_snd_507_);
v___x_561_ = lean_unbox_float(v_fst_506_);
v___x_562_ = lean_float_sub(v___x_560_, v___x_561_);
v___x_563_ = lean_float_decLt(v___y_559_, v___x_562_);
v___y_527_ = v___x_563_;
goto v___jp_526_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_477_ = stack[0].m_obj;
uint8_t v_collapsed_478_ = stack[1].m_num;
lean_object* v_tag_479_ = stack[2].m_obj;
lean_object* v_opts_480_ = stack[3].m_obj;
uint8_t v_clsEnabled_481_ = stack[4].m_num;
lean_object* v_oldTraces_482_ = stack[5].m_obj;
lean_object* v_msg_483_ = stack[6].m_obj;
lean_object* v_resStartStop_484_ = stack[7].m_obj;
lean_object* v___y_485_ = stack[8].m_obj;
lean_object* v___y_486_ = stack[9].m_obj;
lean_object* v___y_487_ = stack[10].m_obj;
lean_object* v___y_488_ = stack[11].m_obj;
lean_object* v_res_574_;
v_res_574_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_477_, v_collapsed_478_, v_tag_479_, v_opts_480_, v_clsEnabled_481_, v_oldTraces_482_, v_msg_483_, v_resStartStop_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_575_, lean_object* v_collapsed_576_, lean_object* v_tag_577_, lean_object* v_opts_578_, lean_object* v_clsEnabled_579_, lean_object* v_oldTraces_580_, lean_object* v_msg_581_, lean_object* v_resStartStop_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v_collapsed_boxed_588_; uint8_t v_clsEnabled_boxed_589_; lean_object* v_res_590_; 
v_collapsed_boxed_588_ = lean_unbox(v_collapsed_576_);
v_clsEnabled_boxed_589_ = lean_unbox(v_clsEnabled_579_);
v_res_590_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_575_, v_collapsed_boxed_588_, v_tag_577_, v_opts_578_, v_clsEnabled_boxed_589_, v_oldTraces_580_, v_msg_581_, v_resStartStop_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v_opts_578_);
return v_res_590_;
}
}
lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v_x_593_);
return v___x_599_;
}
else
{
lean_object* v_head_600_; lean_object* v_tail_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_624_; 
v_head_600_ = lean_ctor_get(v_x_592_, 0);
v_tail_601_ = lean_ctor_get(v_x_592_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_624_ == 0)
{
v___x_603_ = v_x_592_;
v_isShared_604_ = v_isSharedCheck_624_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_tail_601_);
lean_inc(v_head_600_);
lean_dec(v_x_592_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_624_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; 
lean_inc(v_head_600_);
v___x_605_ = l_Lean_MVarId_inferInstance(v_head_600_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_dec_ref_known(v___x_605_, 1);
lean_del_object(v___x_603_);
lean_dec(v_head_600_);
v_x_592_ = v_tail_601_;
goto _start;
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_623_; 
v_a_607_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_623_ == 0)
{
v___x_609_ = v___x_605_;
v_isShared_610_ = v_isSharedCheck_623_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_623_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint8_t v___y_612_; uint8_t v___x_621_; 
v___x_621_ = l_Lean_Exception_isInterrupt(v_a_607_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
lean_inc(v_a_607_);
v___x_622_ = l_Lean_Exception_isRuntime(v_a_607_);
v___y_612_ = v___x_622_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___x_621_;
goto v___jp_611_;
}
v___jp_611_:
{
if (v___y_612_ == 0)
{
lean_del_object(v___x_609_);
lean_dec(v_a_607_);
if (v___x_591_ == 0)
{
lean_del_object(v___x_603_);
lean_dec(v_head_600_);
v_x_592_ = v_tail_601_;
goto _start;
}
else
{
lean_object* v___x_615_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_x_593_);
v___x_615_ = v___x_603_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_head_600_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_x_593_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v_x_592_ = v_tail_601_;
v_x_593_ = v___x_615_;
goto _start;
}
}
}
else
{
lean_object* v___x_619_; 
lean_del_object(v___x_603_);
lean_dec(v_tail_601_);
lean_dec(v_head_600_);
lean_dec(v_x_593_);
if (v_isShared_610_ == 0)
{
v___x_619_ = v___x_609_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_607_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_591_ = stack[0].m_num;
lean_object* v_x_592_ = stack[1].m_obj;
lean_object* v_x_593_ = stack[2].m_obj;
lean_object* v___y_594_ = stack[3].m_obj;
lean_object* v___y_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_591_, v_x_592_, v_x_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_14703__boxed_634_; lean_object* v_res_635_; 
v___x_14703__boxed_634_ = lean_unbox(v___x_626_);
v_res_635_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14703__boxed_634_, v_x_627_, v_x_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_635_;
}
}
lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v_x_638_);
return v___x_644_;
}
else
{
lean_object* v_head_645_; lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_669_; 
v_head_645_ = lean_ctor_get(v_x_637_, 0);
v_tail_646_ = lean_ctor_get(v_x_637_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_669_ == 0)
{
v___x_648_ = v_x_637_;
v_isShared_649_ = v_isSharedCheck_669_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_inc(v_head_645_);
lean_dec(v_x_637_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_669_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_655_; 
lean_inc(v_head_645_);
v___x_655_ = l_Lean_MVarId_inferInstance(v_head_645_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_dec_ref_known(v___x_655_, 1);
if (v___x_636_ == 0)
{
lean_del_object(v___x_648_);
lean_dec(v_head_645_);
v_x_637_ = v_tail_646_;
goto _start;
}
else
{
goto v___jp_650_;
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_668_; 
v_a_657_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_668_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___y_662_; uint8_t v___x_666_; 
v___x_666_ = l_Lean_Exception_isInterrupt(v_a_657_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
lean_inc(v_a_657_);
v___x_667_ = l_Lean_Exception_isRuntime(v_a_657_);
v___y_662_ = v___x_667_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___x_666_;
goto v___jp_661_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_del_object(v___x_659_);
lean_dec(v_a_657_);
goto v___jp_650_;
}
else
{
lean_object* v___x_664_; 
lean_del_object(v___x_648_);
lean_dec(v_tail_646_);
lean_dec(v_head_645_);
lean_dec(v_x_638_);
if (v_isShared_660_ == 0)
{
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_657_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
v___jp_650_:
{
lean_object* v___x_652_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_x_638_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_head_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_x_638_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_x_637_ = v_tail_646_;
v_x_638_ = v___x_652_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_636_ = stack[0].m_num;
lean_object* v_x_637_ = stack[1].m_obj;
lean_object* v_x_638_ = stack[2].m_obj;
lean_object* v___y_639_ = stack[3].m_obj;
lean_object* v___y_640_ = stack[4].m_obj;
lean_object* v___y_641_ = stack[5].m_obj;
lean_object* v___y_642_ = stack[6].m_obj;
lean_object* v_res_670_;
v_res_670_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_636_, v_x_637_, v_x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
stack->m_obj
 = v_res_670_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
uint8_t v___x_14822__boxed_679_; lean_object* v_res_680_; 
v___x_14822__boxed_679_ = lean_unbox(v___x_671_);
v_res_680_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14822__boxed_679_, v_x_672_, v_x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_680_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_684_; double v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(1000000000u);
v___x_685_ = lean_float_of_nat(v___x_684_);
return v___x_685_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_686_, lean_object* v_g_687_, lean_object* v_e_688_, lean_object* v_cfg_689_, lean_object* v___x_690_, lean_object* v___x_691_, uint8_t v___x_692_, lean_object* v___x_693_, lean_object* v___f_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_toCold_700_; lean_object* v_options_701_; lean_object* v_inheritedTraceOptions_702_; uint8_t v_hasTrace_703_; lean_object* v___y_705_; 
v_toCold_700_ = lean_ctor_get(v___y_697_, 0);
v_options_701_ = lean_ctor_get(v_toCold_700_, 2);
v_inheritedTraceOptions_702_ = lean_ctor_get(v_toCold_700_, 11);
v_hasTrace_703_ = lean_ctor_get_uint8(v_options_701_, sizeof(void*)*1);
if (v_hasTrace_703_ == 0)
{
lean_object* v___x_726_; uint8_t v_transparency_727_; uint8_t v___x_728_; 
lean_dec_ref(v___f_694_);
lean_dec_ref(v___x_693_);
lean_dec(v___x_691_);
v___x_726_ = l_Lean_Meta_Context_config(v___y_695_);
v_transparency_727_ = lean_ctor_get_uint8(v___x_726_, 9);
lean_dec_ref(v___x_726_);
v___x_728_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_727_, v_transparency_686_);
if (v___x_728_ == 0)
{
lean_object* v_keyedConfig_729_; uint8_t v_trackZetaDelta_730_; lean_object* v_zetaDeltaSet_731_; lean_object* v_lctx_732_; lean_object* v_localInstances_733_; lean_object* v_defEqCtx_x3f_734_; lean_object* v_synthPendingDepth_735_; lean_object* v_customCanUnfoldPredicate_x3f_736_; uint8_t v_univApprox_737_; uint8_t v_inTypeClassResolution_738_; uint8_t v_cacheInferType_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_keyedConfig_729_ = lean_ctor_get(v___y_695_, 0);
v_trackZetaDelta_730_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7);
v_zetaDeltaSet_731_ = lean_ctor_get(v___y_695_, 1);
v_lctx_732_ = lean_ctor_get(v___y_695_, 2);
v_localInstances_733_ = lean_ctor_get(v___y_695_, 3);
v_defEqCtx_x3f_734_ = lean_ctor_get(v___y_695_, 4);
v_synthPendingDepth_735_ = lean_ctor_get(v___y_695_, 5);
v_customCanUnfoldPredicate_x3f_736_ = lean_ctor_get(v___y_695_, 6);
v_univApprox_737_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_738_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 2);
v_cacheInferType_739_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_729_);
v___x_740_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_686_, v_keyedConfig_729_);
lean_inc(v_customCanUnfoldPredicate_x3f_736_);
lean_inc(v_synthPendingDepth_735_);
lean_inc(v_defEqCtx_x3f_734_);
lean_inc_ref(v_localInstances_733_);
lean_inc_ref(v_lctx_732_);
lean_inc(v_zetaDeltaSet_731_);
v___x_741_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_zetaDeltaSet_731_);
lean_ctor_set(v___x_741_, 2, v_lctx_732_);
lean_ctor_set(v___x_741_, 3, v_localInstances_733_);
lean_ctor_set(v___x_741_, 4, v_defEqCtx_x3f_734_);
lean_ctor_set(v___x_741_, 5, v_synthPendingDepth_735_);
lean_ctor_set(v___x_741_, 6, v_customCanUnfoldPredicate_x3f_736_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*7, v_trackZetaDelta_730_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*7 + 1, v_univApprox_737_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*7 + 2, v_inTypeClassResolution_738_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*7 + 3, v_cacheInferType_739_);
v___x_742_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___x_741_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref_known(v___x_741_, 7);
v___y_705_ = v___x_742_;
goto v___jp_704_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
v___y_705_ = v___x_743_;
goto v___jp_704_;
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v_a_750_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v_a_765_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v_a_770_; uint8_t v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v_a_788_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v_a_800_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v_a_805_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; 
v___x_744_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_691_);
v___x_745_ = l_Lean_Name_append(v___x_744_, v___x_691_);
v___x_746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_702_, v_options_701_, v___x_745_);
lean_dec(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___y_866_; 
v___x_863_ = l_Lean_trace_profiler;
v___x_864_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_701_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_887_; uint8_t v_transparency_888_; uint8_t v___x_889_; 
lean_dec_ref(v___f_694_);
lean_dec_ref(v___x_693_);
lean_dec(v___x_691_);
v___x_887_ = l_Lean_Meta_Context_config(v___y_695_);
v_transparency_888_ = lean_ctor_get_uint8(v___x_887_, 9);
lean_dec_ref(v___x_887_);
v___x_889_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_888_, v_transparency_686_);
if (v___x_889_ == 0)
{
lean_object* v_keyedConfig_890_; uint8_t v_trackZetaDelta_891_; lean_object* v_zetaDeltaSet_892_; lean_object* v_lctx_893_; lean_object* v_localInstances_894_; lean_object* v_defEqCtx_x3f_895_; lean_object* v_synthPendingDepth_896_; lean_object* v_customCanUnfoldPredicate_x3f_897_; uint8_t v_univApprox_898_; uint8_t v_inTypeClassResolution_899_; uint8_t v_cacheInferType_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_keyedConfig_890_ = lean_ctor_get(v___y_695_, 0);
v_trackZetaDelta_891_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7);
v_zetaDeltaSet_892_ = lean_ctor_get(v___y_695_, 1);
v_lctx_893_ = lean_ctor_get(v___y_695_, 2);
v_localInstances_894_ = lean_ctor_get(v___y_695_, 3);
v_defEqCtx_x3f_895_ = lean_ctor_get(v___y_695_, 4);
v_synthPendingDepth_896_ = lean_ctor_get(v___y_695_, 5);
v_customCanUnfoldPredicate_x3f_897_ = lean_ctor_get(v___y_695_, 6);
v_univApprox_898_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_899_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 2);
v_cacheInferType_900_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_890_);
v___x_901_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_686_, v_keyedConfig_890_);
lean_inc(v_customCanUnfoldPredicate_x3f_897_);
lean_inc(v_synthPendingDepth_896_);
lean_inc(v_defEqCtx_x3f_895_);
lean_inc_ref(v_localInstances_894_);
lean_inc_ref(v_lctx_893_);
lean_inc(v_zetaDeltaSet_892_);
v___x_902_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_zetaDeltaSet_892_);
lean_ctor_set(v___x_902_, 2, v_lctx_893_);
lean_ctor_set(v___x_902_, 3, v_localInstances_894_);
lean_ctor_set(v___x_902_, 4, v_defEqCtx_x3f_895_);
lean_ctor_set(v___x_902_, 5, v_synthPendingDepth_896_);
lean_ctor_set(v___x_902_, 6, v_customCanUnfoldPredicate_x3f_897_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7, v_trackZetaDelta_891_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7 + 1, v_univApprox_898_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7 + 2, v_inTypeClassResolution_899_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7 + 3, v_cacheInferType_900_);
v___x_903_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___x_902_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref_known(v___x_902_, 7);
v___y_866_ = v___x_903_;
goto v___jp_865_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
v___y_866_ = v___x_904_;
goto v___jp_865_;
}
}
else
{
goto v___jp_820_;
}
v___jp_865_:
{
if (lean_obj_tag(v___y_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_867_ = lean_ctor_get(v___y_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___y_866_, 1);
v___x_868_ = lean_box(0);
v___x_869_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_864_, v_hasTrace_703_, v_a_867_, v___x_868_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref(v___y_695_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_878_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = l_List_reverse___redArg(v_a_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
return v___x_869_;
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___y_695_);
v_a_879_ = lean_ctor_get(v___y_866_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___y_866_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___y_866_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___y_866_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
else
{
goto v___jp_820_;
}
v___jp_747_:
{
lean_object* v___x_751_; double v___x_752_; double v___x_753_; double v___x_754_; double v___x_755_; double v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_751_ = lean_io_mono_nanos_now();
v___x_752_ = lean_float_of_nat(v___y_749_);
v___x_753_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_754_ = lean_float_div(v___x_752_, v___x_753_);
v___x_755_ = lean_float_of_nat(v___x_751_);
v___x_756_ = lean_float_div(v___x_755_, v___x_753_);
v___x_757_ = lean_box_float(v___x_754_);
v___x_758_ = lean_box_float(v___x_756_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_a_750_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_691_, v___x_692_, v___x_693_, v_options_701_, v___x_746_, v___y_748_, v___f_694_, v___x_760_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref(v___y_695_);
return v___x_761_;
}
v___jp_762_:
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_765_);
v___y_748_ = v___y_763_;
v___y_749_ = v___y_764_;
v_a_750_ = v___x_766_;
goto v___jp_747_;
}
v___jp_767_:
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v_a_770_);
v___y_748_ = v___y_768_;
v___y_749_ = v___y_769_;
v_a_750_ = v___x_771_;
goto v___jp_747_;
}
v___jp_772_:
{
if (lean_obj_tag(v___y_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_a_777_ = lean_ctor_get(v___y_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___y_776_, 1);
v___x_778_ = lean_box(0);
v___x_779_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_773_, v_hasTrace_703_, v_a_777_, v___x_778_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_List_reverse___redArg(v_a_780_);
v___y_768_ = v___y_774_;
v___y_769_ = v___y_775_;
v_a_770_ = v___x_781_;
goto v___jp_767_;
}
else
{
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_782_; 
v_a_782_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_779_, 1);
v___y_768_ = v___y_774_;
v___y_769_ = v___y_775_;
v_a_770_ = v_a_782_;
goto v___jp_767_;
}
else
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_779_, 1);
v___y_763_ = v___y_774_;
v___y_764_ = v___y_775_;
v_a_765_ = v_a_783_;
goto v___jp_762_;
}
}
}
else
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___y_776_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___y_776_, 1);
v___y_763_ = v___y_774_;
v___y_764_ = v___y_775_;
v_a_765_ = v_a_784_;
goto v___jp_762_;
}
}
v___jp_785_:
{
lean_object* v___x_789_; double v___x_790_; double v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_789_ = lean_io_get_num_heartbeats();
v___x_790_ = lean_float_of_nat(v___y_786_);
v___x_791_ = lean_float_of_nat(v___x_789_);
v___x_792_ = lean_box_float(v___x_790_);
v___x_793_ = lean_box_float(v___x_791_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_a_788_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_691_, v___x_692_, v___x_693_, v_options_701_, v___x_746_, v___y_787_, v___f_694_, v___x_795_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref(v___y_695_);
return v___x_796_;
}
v___jp_797_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_a_800_);
v___y_786_ = v___y_798_;
v___y_787_ = v___y_799_;
v_a_788_ = v___x_801_;
goto v___jp_785_;
}
v___jp_802_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_a_805_);
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v_a_788_ = v___x_806_;
goto v___jp_785_;
}
v___jp_807_:
{
if (lean_obj_tag(v___y_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_a_812_ = lean_ctor_get(v___y_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___y_811_, 1);
v___x_813_ = lean_box(0);
v___x_814_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_808_, v_a_812_, v___x_813_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = l_List_reverse___redArg(v_a_815_);
v___y_803_ = v___y_809_;
v___y_804_ = v___y_810_;
v_a_805_ = v___x_816_;
goto v___jp_802_;
}
else
{
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_814_, 1);
v___y_803_ = v___y_809_;
v___y_804_ = v___y_810_;
v_a_805_ = v_a_817_;
goto v___jp_802_;
}
else
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_814_, 1);
v___y_798_ = v___y_809_;
v___y_799_ = v___y_810_;
v_a_800_ = v_a_818_;
goto v___jp_797_;
}
}
}
else
{
lean_object* v_a_819_; 
v_a_819_ = lean_ctor_get(v___y_811_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___y_811_, 1);
v___y_798_ = v___y_809_;
v___y_799_ = v___y_810_;
v_a_800_ = v_a_819_;
goto v___jp_797_;
}
}
v___jp_820_:
{
lean_object* v___x_821_; lean_object* v_a_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_821_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_698_);
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v___x_821_);
v___x_823_ = l_Lean_trace_profiler_useHeartbeats;
v___x_824_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_701_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v_transparency_827_; uint8_t v___x_828_; 
v___x_825_ = lean_io_mono_nanos_now();
v___x_826_ = l_Lean_Meta_Context_config(v___y_695_);
v_transparency_827_ = lean_ctor_get_uint8(v___x_826_, 9);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_827_, v_transparency_686_);
if (v___x_828_ == 0)
{
lean_object* v_keyedConfig_829_; uint8_t v_trackZetaDelta_830_; lean_object* v_zetaDeltaSet_831_; lean_object* v_lctx_832_; lean_object* v_localInstances_833_; lean_object* v_defEqCtx_x3f_834_; lean_object* v_synthPendingDepth_835_; lean_object* v_customCanUnfoldPredicate_x3f_836_; uint8_t v_univApprox_837_; uint8_t v_inTypeClassResolution_838_; uint8_t v_cacheInferType_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_keyedConfig_829_ = lean_ctor_get(v___y_695_, 0);
v_trackZetaDelta_830_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7);
v_zetaDeltaSet_831_ = lean_ctor_get(v___y_695_, 1);
v_lctx_832_ = lean_ctor_get(v___y_695_, 2);
v_localInstances_833_ = lean_ctor_get(v___y_695_, 3);
v_defEqCtx_x3f_834_ = lean_ctor_get(v___y_695_, 4);
v_synthPendingDepth_835_ = lean_ctor_get(v___y_695_, 5);
v_customCanUnfoldPredicate_x3f_836_ = lean_ctor_get(v___y_695_, 6);
v_univApprox_837_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_838_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 2);
v_cacheInferType_839_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_829_);
v___x_840_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_686_, v_keyedConfig_829_);
lean_inc(v_customCanUnfoldPredicate_x3f_836_);
lean_inc(v_synthPendingDepth_835_);
lean_inc(v_defEqCtx_x3f_834_);
lean_inc_ref(v_localInstances_833_);
lean_inc_ref(v_lctx_832_);
lean_inc(v_zetaDeltaSet_831_);
v___x_841_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_zetaDeltaSet_831_);
lean_ctor_set(v___x_841_, 2, v_lctx_832_);
lean_ctor_set(v___x_841_, 3, v_localInstances_833_);
lean_ctor_set(v___x_841_, 4, v_defEqCtx_x3f_834_);
lean_ctor_set(v___x_841_, 5, v_synthPendingDepth_835_);
lean_ctor_set(v___x_841_, 6, v_customCanUnfoldPredicate_x3f_836_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7, v_trackZetaDelta_830_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 1, v_univApprox_837_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 2, v_inTypeClassResolution_838_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*7 + 3, v_cacheInferType_839_);
v___x_842_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___x_841_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref_known(v___x_841_, 7);
v___y_773_ = v___x_824_;
v___y_774_ = v_a_822_;
v___y_775_ = v___x_825_;
v___y_776_ = v___x_842_;
goto v___jp_772_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
v___y_773_ = v___x_824_;
v___y_774_ = v_a_822_;
v___y_775_ = v___x_825_;
v___y_776_ = v___x_843_;
goto v___jp_772_;
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v_transparency_846_; uint8_t v___x_847_; 
v___x_844_ = lean_io_get_num_heartbeats();
v___x_845_ = l_Lean_Meta_Context_config(v___y_695_);
v_transparency_846_ = lean_ctor_get_uint8(v___x_845_, 9);
lean_dec_ref(v___x_845_);
v___x_847_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_846_, v_transparency_686_);
if (v___x_847_ == 0)
{
lean_object* v_keyedConfig_848_; uint8_t v_trackZetaDelta_849_; lean_object* v_zetaDeltaSet_850_; lean_object* v_lctx_851_; lean_object* v_localInstances_852_; lean_object* v_defEqCtx_x3f_853_; lean_object* v_synthPendingDepth_854_; lean_object* v_customCanUnfoldPredicate_x3f_855_; uint8_t v_univApprox_856_; uint8_t v_inTypeClassResolution_857_; uint8_t v_cacheInferType_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_keyedConfig_848_ = lean_ctor_get(v___y_695_, 0);
v_trackZetaDelta_849_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7);
v_zetaDeltaSet_850_ = lean_ctor_get(v___y_695_, 1);
v_lctx_851_ = lean_ctor_get(v___y_695_, 2);
v_localInstances_852_ = lean_ctor_get(v___y_695_, 3);
v_defEqCtx_x3f_853_ = lean_ctor_get(v___y_695_, 4);
v_synthPendingDepth_854_ = lean_ctor_get(v___y_695_, 5);
v_customCanUnfoldPredicate_x3f_855_ = lean_ctor_get(v___y_695_, 6);
v_univApprox_856_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_857_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 2);
v_cacheInferType_858_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_848_);
v___x_859_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_686_, v_keyedConfig_848_);
lean_inc(v_customCanUnfoldPredicate_x3f_855_);
lean_inc(v_synthPendingDepth_854_);
lean_inc(v_defEqCtx_x3f_853_);
lean_inc_ref(v_localInstances_852_);
lean_inc_ref(v_lctx_851_);
lean_inc(v_zetaDeltaSet_850_);
v___x_860_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_zetaDeltaSet_850_);
lean_ctor_set(v___x_860_, 2, v_lctx_851_);
lean_ctor_set(v___x_860_, 3, v_localInstances_852_);
lean_ctor_set(v___x_860_, 4, v_defEqCtx_x3f_853_);
lean_ctor_set(v___x_860_, 5, v_synthPendingDepth_854_);
lean_ctor_set(v___x_860_, 6, v_customCanUnfoldPredicate_x3f_855_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7, v_trackZetaDelta_849_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7 + 1, v_univApprox_856_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7 + 2, v_inTypeClassResolution_857_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*7 + 3, v_cacheInferType_858_);
v___x_861_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___x_860_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref_known(v___x_860_, 7);
v___y_808_ = v___x_824_;
v___y_809_ = v___x_844_;
v___y_810_ = v_a_822_;
v___y_811_ = v___x_861_;
goto v___jp_807_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_MVarId_apply(v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
v___y_808_ = v___x_824_;
v___y_809_ = v___x_844_;
v___y_810_ = v_a_822_;
v___y_811_ = v___x_862_;
goto v___jp_807_;
}
}
}
}
v___jp_704_:
{
if (lean_obj_tag(v___y_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v___y_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___y_705_, 1);
v___x_707_ = lean_box(0);
v___x_708_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_703_, v_a_706_, v___x_707_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec_ref(v___y_695_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = l_List_reverse___redArg(v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
return v___x_708_;
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___y_695_);
v_a_718_ = lean_ctor_get(v___y_705_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___y_705_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___y_705_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___y_705_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
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
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_transparency_686_ = stack[0].m_num;
lean_object* v_g_687_ = stack[1].m_obj;
lean_object* v_e_688_ = stack[2].m_obj;
lean_object* v_cfg_689_ = stack[3].m_obj;
lean_object* v___x_690_ = stack[4].m_obj;
lean_object* v___x_691_ = stack[5].m_obj;
uint8_t v___x_692_ = stack[6].m_num;
lean_object* v___x_693_ = stack[7].m_obj;
lean_object* v___f_694_ = stack[8].m_obj;
lean_object* v___y_695_ = stack[9].m_obj;
lean_object* v___y_696_ = stack[10].m_obj;
lean_object* v___y_697_ = stack[11].m_obj;
lean_object* v___y_698_ = stack[12].m_obj;
lean_object* v_res_905_;
v_res_905_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_686_, v_g_687_, v_e_688_, v_cfg_689_, v___x_690_, v___x_691_, v___x_692_, v___x_693_, v___f_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
stack->m_obj
 = v_res_905_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_906_, lean_object* v_g_907_, lean_object* v_e_908_, lean_object* v_cfg_909_, lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v___f_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_transparency_boxed_920_; uint8_t v___x_14952__boxed_921_; lean_object* v_res_922_; 
v_transparency_boxed_920_ = lean_unbox(v_transparency_906_);
v___x_14952__boxed_921_ = lean_unbox(v___x_912_);
v_res_922_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_920_, v_g_907_, v_e_908_, v_cfg_909_, v___x_910_, v___x_911_, v___x_14952__boxed_921_, v___x_913_, v___f_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
return v_res_922_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_924_, lean_object* v_g_925_, lean_object* v_cfg_926_, lean_object* v_e_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; 
lean_inc_ref(v_e_927_);
v___f_933_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_933_, 0, v_e_927_);
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_935_ = lean_box(0);
v___x_936_ = 1;
v___x_937_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_938_ = lean_box(v_transparency_924_);
v___x_939_ = lean_box(v___x_936_);
v___f_940_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_940_, 0, v___x_938_);
lean_closure_set(v___f_940_, 1, v_g_925_);
lean_closure_set(v___f_940_, 2, v_e_927_);
lean_closure_set(v___f_940_, 3, v_cfg_926_);
lean_closure_set(v___f_940_, 4, v___x_935_);
lean_closure_set(v___f_940_, 5, v___x_934_);
lean_closure_set(v___f_940_, 6, v___x_939_);
lean_closure_set(v___f_940_, 7, v___x_937_);
lean_closure_set(v___f_940_, 8, v___f_933_);
v___x_941_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_940_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_941_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_transparency_924_ = stack[0].m_num;
lean_object* v_g_925_ = stack[1].m_obj;
lean_object* v_cfg_926_ = stack[2].m_obj;
lean_object* v_e_927_ = stack[3].m_obj;
lean_object* v___y_928_ = stack[4].m_obj;
lean_object* v___y_929_ = stack[5].m_obj;
lean_object* v___y_930_ = stack[6].m_obj;
lean_object* v___y_931_ = stack[7].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_924_, v_g_925_, v_cfg_926_, v_e_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_943_, lean_object* v_g_944_, lean_object* v_cfg_945_, lean_object* v_e_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
uint8_t v_transparency_boxed_952_; lean_object* v_res_953_; 
v_transparency_boxed_952_ = lean_unbox(v_transparency_943_);
v_res_953_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_952_, v_g_944_, v_cfg_945_, v_e_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_953_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_954_, uint8_t v_transparency_955_, lean_object* v_lemmas_956_, lean_object* v_g_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; lean_object* v___f_962_; lean_object* v___x_963_; 
v___x_961_ = lean_box(v_transparency_955_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_962_, 0, v___x_961_);
lean_closure_set(v___f_962_, 1, v_g_957_);
lean_closure_set(v___f_962_, 2, v_cfg_954_);
v___x_963_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_956_, v_a_958_, v_a_959_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_968_, 0, lean_box(0));
lean_closure_set(v___x_968_, 1, lean_box(0));
lean_closure_set(v___x_968_, 2, v___f_962_);
lean_closure_set(v___x_968_, 3, v_a_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v___f_962_);
v_a_973_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_963_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_963_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyTactics___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_954_ = stack[0].m_obj;
uint8_t v_transparency_955_ = stack[1].m_num;
lean_object* v_lemmas_956_ = stack[2].m_obj;
lean_object* v_g_957_ = stack[3].m_obj;
lean_object* v_a_958_ = stack[4].m_obj;
lean_object* v_a_959_ = stack[5].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_954_, v_transparency_955_, v_lemmas_956_, v_g_957_, v_a_958_, v_a_959_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_982_, lean_object* v_transparency_983_, lean_object* v_lemmas_984_, lean_object* v_g_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
uint8_t v_transparency_boxed_989_; lean_object* v_res_990_; 
v_transparency_boxed_989_ = lean_unbox(v_transparency_983_);
v_res_990_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_982_, v_transparency_boxed_989_, v_lemmas_984_, v_g_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec(v_a_986_);
return v_res_990_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_991_, uint8_t v_transparency_992_, lean_object* v_lemmas_993_, lean_object* v_g_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_991_, v_transparency_992_, v_lemmas_993_, v_g_994_, v_a_996_, v_a_998_);
return v___x_1000_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyTactics_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_991_ = stack[0].m_obj;
uint8_t v_transparency_992_ = stack[1].m_num;
lean_object* v_lemmas_993_ = stack[2].m_obj;
lean_object* v_g_994_ = stack[3].m_obj;
lean_object* v_a_995_ = stack[4].m_obj;
lean_object* v_a_996_ = stack[5].m_obj;
lean_object* v_a_997_ = stack[6].m_obj;
lean_object* v_a_998_ = stack[7].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_991_, v_transparency_992_, v_lemmas_993_, v_g_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1002_, lean_object* v_transparency_1003_, lean_object* v_lemmas_1004_, lean_object* v_g_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_transparency_boxed_1011_; lean_object* v_res_1012_; 
v_transparency_boxed_1011_ = lean_unbox(v_transparency_1003_);
v_res_1012_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1002_, v_transparency_boxed_1011_, v_lemmas_1004_, v_g_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1012_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_1014_);
return v___x_1020_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1014_ = stack[1].m_obj;
lean_object* v___y_1015_ = stack[2].m_obj;
lean_object* v___y_1016_ = stack[3].m_obj;
lean_object* v___y_1017_ = stack[4].m_obj;
lean_object* v___y_1018_ = stack[5].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_box(0), v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1022_, v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1029_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1030_, uint8_t v_transparency_1031_, lean_object* v_lemmas_1032_, lean_object* v_g_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1030_, v_transparency_1031_, v_lemmas_1032_, v_g_1033_, v_a_1035_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_Meta_Iterator_head___redArg(v_a_1040_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1041_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1039_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1039_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyFirst_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1030_ = stack[0].m_obj;
uint8_t v_transparency_1031_ = stack[1].m_num;
lean_object* v_lemmas_1032_ = stack[2].m_obj;
lean_object* v_g_1033_ = stack[3].m_obj;
lean_object* v_a_1034_ = stack[4].m_obj;
lean_object* v_a_1035_ = stack[5].m_obj;
lean_object* v_a_1036_ = stack[6].m_obj;
lean_object* v_a_1037_ = stack[7].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1030_, v_transparency_1031_, v_lemmas_1032_, v_g_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1051_, lean_object* v_transparency_1052_, lean_object* v_lemmas_1053_, lean_object* v_g_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
uint8_t v_transparency_boxed_1060_; lean_object* v_res_1061_; 
v_transparency_boxed_1060_ = lean_unbox(v_transparency_1052_);
v_res_1061_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1051_, v_transparency_boxed_1060_, v_lemmas_1053_, v_g_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1062_){
_start:
{
lean_object* v_toApplyRulesConfig_1063_; lean_object* v_toBacktrackConfig_1064_; 
v_toApplyRulesConfig_1063_ = lean_ctor_get(v_x_1062_, 0);
v_toBacktrackConfig_1064_ = lean_ctor_get(v_toApplyRulesConfig_1063_, 0);
lean_inc_ref(v_toBacktrackConfig_1064_);
return v_toBacktrackConfig_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1065_);
lean_dec_ref(v_x_1065_);
return v_res_1066_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1069_, lean_object* v_discharge_1070_, lean_object* v_g_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
lean_inc(v_g_1071_);
v___x_1077_ = lean_apply_6(v_test_1069_, v_g_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, lean_box(0));
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_unbox(v_a_1078_);
lean_dec(v_a_1078_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_del_object(v___x_1080_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
v___x_1083_ = lean_apply_6(v_discharge_1070_, v_g_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, lean_box(0));
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_dec(v_g_1071_);
lean_dec_ref(v_discharge_1070_);
v___x_1084_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1084_);
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_g_1071_);
lean_dec_ref(v_discharge_1070_);
v_a_1089_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1077_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1077_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_test_1069_ = stack[0].m_obj;
lean_object* v_discharge_1070_ = stack[1].m_obj;
lean_object* v_g_1071_ = stack[2].m_obj;
lean_object* v___y_1072_ = stack[3].m_obj;
lean_object* v___y_1073_ = stack[4].m_obj;
lean_object* v___y_1074_ = stack[5].m_obj;
lean_object* v___y_1075_ = stack[6].m_obj;
lean_object* v_res_1097_;
v_res_1097_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1069_, v_discharge_1070_, v_g_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
stack->m_obj
 = v_res_1097_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1098_, lean_object* v_discharge_1099_, lean_object* v_g_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1098_, v_discharge_1099_, v_g_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1107_, lean_object* v_test_1108_){
_start:
{
lean_object* v_toApplyRulesConfig_1109_; lean_object* v_toBacktrackConfig_1110_; uint8_t v_backtracking_1111_; uint8_t v_intro_1112_; uint8_t v_constructor_1113_; uint8_t v_suggestions_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1146_; 
v_toApplyRulesConfig_1109_ = lean_ctor_get(v_cfg_1107_, 0);
lean_inc_ref(v_toApplyRulesConfig_1109_);
v_toBacktrackConfig_1110_ = lean_ctor_get(v_toApplyRulesConfig_1109_, 0);
lean_inc_ref(v_toBacktrackConfig_1110_);
v_backtracking_1111_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*1);
v_intro_1112_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*1 + 1);
v_constructor_1113_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*1 + 2);
v_suggestions_1114_ = lean_ctor_get_uint8(v_cfg_1107_, sizeof(void*)*1 + 3);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_cfg_1107_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_cfg_1107_, 0);
lean_dec(v_unused_1147_);
v___x_1116_ = v_cfg_1107_;
v_isShared_1117_ = v_isSharedCheck_1146_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_cfg_1107_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1146_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_toApplyConfig_1118_; uint8_t v_transparency_1119_; uint8_t v_symm_1120_; uint8_t v_exfalso_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1144_; 
v_toApplyConfig_1118_ = lean_ctor_get(v_toApplyRulesConfig_1109_, 1);
v_transparency_1119_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1109_, sizeof(void*)*2);
v_symm_1120_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1109_, sizeof(void*)*2 + 1);
v_exfalso_1121_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1109_, sizeof(void*)*2 + 2);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_toApplyRulesConfig_1109_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_toApplyRulesConfig_1109_, 0);
lean_dec(v_unused_1145_);
v___x_1123_ = v_toApplyRulesConfig_1109_;
v_isShared_1124_ = v_isSharedCheck_1144_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_toApplyConfig_1118_);
lean_dec(v_toApplyRulesConfig_1109_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1144_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_maxDepth_1125_; lean_object* v_proc_1126_; lean_object* v_suspend_1127_; lean_object* v_discharge_1128_; uint8_t v_commitIndependentGoals_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1143_; 
v_maxDepth_1125_ = lean_ctor_get(v_toBacktrackConfig_1110_, 0);
v_proc_1126_ = lean_ctor_get(v_toBacktrackConfig_1110_, 1);
v_suspend_1127_ = lean_ctor_get(v_toBacktrackConfig_1110_, 2);
v_discharge_1128_ = lean_ctor_get(v_toBacktrackConfig_1110_, 3);
v_commitIndependentGoals_1129_ = lean_ctor_get_uint8(v_toBacktrackConfig_1110_, sizeof(void*)*4);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_toBacktrackConfig_1110_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1131_ = v_toBacktrackConfig_1110_;
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_discharge_1128_);
lean_inc(v_suspend_1127_);
lean_inc(v_proc_1126_);
lean_inc(v_maxDepth_1125_);
lean_dec(v_toBacktrackConfig_1110_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___f_1133_; lean_object* v___x_1135_; 
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1133_, 0, v_test_1108_);
lean_closure_set(v___f_1133_, 1, v_discharge_1128_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 3, v___f_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_maxDepth_1125_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_proc_1126_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_suspend_1127_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v___f_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*4, v_commitIndependentGoals_1129_);
v___x_1135_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1135_);
v___x_1137_ = v___x_1123_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_toApplyConfig_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*2, v_transparency_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*2 + 1, v_symm_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*2 + 2, v_exfalso_1121_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1137_);
v___x_1139_ = v___x_1116_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1140_, sizeof(void*)*1, v_backtracking_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1140_, sizeof(void*)*1 + 1, v_intro_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1140_, sizeof(void*)*1 + 2, v_constructor_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1140_, sizeof(void*)*1 + 3, v_suggestions_1114_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1148_, lean_object* v_proc_1149_, lean_object* v_orig_1150_, lean_object* v_goals_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
if (lean_obj_tag(v_goals_1151_) == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v_proc_1149_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v___y_1153_);
lean_inc_ref(v___y_1152_);
v___x_1157_ = lean_apply_7(v_proc_1148_, v_orig_1150_, v_goals_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, lean_box(0));
return v___x_1157_;
}
else
{
lean_object* v_head_1158_; lean_object* v_tail_1159_; lean_object* v___x_1160_; 
v_head_1158_ = lean_ctor_get(v_goals_1151_, 0);
v_tail_1159_ = lean_ctor_get(v_goals_1151_, 1);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v___y_1153_);
lean_inc_ref(v___y_1152_);
lean_inc(v_head_1158_);
v___x_1160_ = lean_apply_6(v_proc_1149_, v_head_1158_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, lean_box(0));
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1170_; 
lean_inc(v_tail_1159_);
lean_dec_ref_known(v_goals_1151_, 2);
lean_dec(v_orig_1150_);
lean_dec_ref(v_proc_1148_);
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1165_ = l_List_appendTR___redArg(v_a_1161_, v_tail_1159_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1166_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1183_; 
v_a_1171_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1173_ = v___x_1160_;
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1160_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___y_1176_; uint8_t v___x_1181_; 
v___x_1181_ = l_Lean_Exception_isInterrupt(v_a_1171_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1182_; 
lean_inc(v_a_1171_);
v___x_1182_ = l_Lean_Exception_isRuntime(v_a_1171_);
v___y_1176_ = v___x_1182_;
goto v___jp_1175_;
}
else
{
v___y_1176_ = v___x_1181_;
goto v___jp_1175_;
}
v___jp_1175_:
{
if (v___y_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_del_object(v___x_1173_);
lean_dec(v_a_1171_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v___y_1153_);
lean_inc_ref(v___y_1152_);
v___x_1177_ = lean_apply_7(v_proc_1148_, v_orig_1150_, v_goals_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, lean_box(0));
return v___x_1177_;
}
else
{
lean_object* v___x_1179_; 
lean_dec_ref_known(v_goals_1151_, 2);
lean_dec(v_orig_1150_);
lean_dec_ref(v_proc_1148_);
if (v_isShared_1174_ == 0)
{
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1171_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_proc_1148_ = stack[0].m_obj;
lean_object* v_proc_1149_ = stack[1].m_obj;
lean_object* v_orig_1150_ = stack[2].m_obj;
lean_object* v_goals_1151_ = stack[3].m_obj;
lean_object* v___y_1152_ = stack[4].m_obj;
lean_object* v___y_1153_ = stack[5].m_obj;
lean_object* v___y_1154_ = stack[6].m_obj;
lean_object* v___y_1155_ = stack[7].m_obj;
lean_object* v_res_1184_;
v_res_1184_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1148_, v_proc_1149_, v_orig_1150_, v_goals_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
stack->m_obj
 = v_res_1184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1185_, lean_object* v_proc_1186_, lean_object* v_orig_1187_, lean_object* v_goals_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1185_, v_proc_1186_, v_orig_1187_, v_goals_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1195_, lean_object* v_proc_1196_){
_start:
{
lean_object* v_toApplyRulesConfig_1197_; lean_object* v_toBacktrackConfig_1198_; uint8_t v_backtracking_1199_; uint8_t v_intro_1200_; uint8_t v_constructor_1201_; uint8_t v_suggestions_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1234_; 
v_toApplyRulesConfig_1197_ = lean_ctor_get(v_cfg_1195_, 0);
lean_inc_ref(v_toApplyRulesConfig_1197_);
v_toBacktrackConfig_1198_ = lean_ctor_get(v_toApplyRulesConfig_1197_, 0);
lean_inc_ref(v_toBacktrackConfig_1198_);
v_backtracking_1199_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1);
v_intro_1200_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1 + 1);
v_constructor_1201_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1 + 2);
v_suggestions_1202_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1 + 3);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_cfg_1195_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_cfg_1195_, 0);
lean_dec(v_unused_1235_);
v___x_1204_ = v_cfg_1195_;
v_isShared_1205_ = v_isSharedCheck_1234_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v_cfg_1195_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1234_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_toApplyConfig_1206_; uint8_t v_transparency_1207_; uint8_t v_symm_1208_; uint8_t v_exfalso_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1232_; 
v_toApplyConfig_1206_ = lean_ctor_get(v_toApplyRulesConfig_1197_, 1);
v_transparency_1207_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1197_, sizeof(void*)*2);
v_symm_1208_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1197_, sizeof(void*)*2 + 1);
v_exfalso_1209_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1197_, sizeof(void*)*2 + 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_toApplyRulesConfig_1197_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_toApplyRulesConfig_1197_, 0);
lean_dec(v_unused_1233_);
v___x_1211_ = v_toApplyRulesConfig_1197_;
v_isShared_1212_ = v_isSharedCheck_1232_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_toApplyConfig_1206_);
lean_dec(v_toApplyRulesConfig_1197_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1232_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_maxDepth_1213_; lean_object* v_proc_1214_; lean_object* v_suspend_1215_; lean_object* v_discharge_1216_; uint8_t v_commitIndependentGoals_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1231_; 
v_maxDepth_1213_ = lean_ctor_get(v_toBacktrackConfig_1198_, 0);
v_proc_1214_ = lean_ctor_get(v_toBacktrackConfig_1198_, 1);
v_suspend_1215_ = lean_ctor_get(v_toBacktrackConfig_1198_, 2);
v_discharge_1216_ = lean_ctor_get(v_toBacktrackConfig_1198_, 3);
v_commitIndependentGoals_1217_ = lean_ctor_get_uint8(v_toBacktrackConfig_1198_, sizeof(void*)*4);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_toBacktrackConfig_1198_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1219_ = v_toBacktrackConfig_1198_;
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_discharge_1216_);
lean_inc(v_suspend_1215_);
lean_inc(v_proc_1214_);
lean_inc(v_maxDepth_1213_);
lean_dec(v_toBacktrackConfig_1198_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___f_1221_; lean_object* v___x_1223_; 
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1221_, 0, v_proc_1214_);
lean_closure_set(v___f_1221_, 1, v_proc_1196_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___f_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_maxDepth_1213_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___f_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_suspend_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_discharge_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*4, v_commitIndependentGoals_1217_);
v___x_1223_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1223_);
v___x_1225_ = v___x_1211_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_toApplyConfig_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*2, v_transparency_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*2 + 1, v_symm_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*2 + 2, v_exfalso_1209_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1225_);
v___x_1227_ = v___x_1204_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1, v_backtracking_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1 + 1, v_intro_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1 + 2, v_constructor_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1 + 3, v_suggestions_1202_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = 1;
v___x_1243_ = l_Lean_Meta_intro1Core(v_g_1236_, v___x_1242_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1261_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1261_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1261_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1259_; 
v_snd_1248_ = lean_ctor_get(v_a_1244_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1244_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_a_1244_, 0);
lean_dec(v_unused_1260_);
v___x_1250_ = v_a_1244_;
v_isShared_1251_ = v_isSharedCheck_1259_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_dec(v_a_1244_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1259_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_box(0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 1);
lean_ctor_set(v___x_1250_, 1, v___x_1252_);
lean_ctor_set(v___x_1250_, 0, v_snd_1248_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_snd_1248_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1254_);
v___x_1256_ = v___x_1246_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1262_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1243_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1243_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1236_ = stack[0].m_obj;
lean_object* v___y_1237_ = stack[1].m_obj;
lean_object* v___y_1238_ = stack[2].m_obj;
lean_object* v___y_1239_ = stack[3].m_obj;
lean_object* v___y_1240_ = stack[4].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1279_){
_start:
{
lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___f_1280_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1281_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1279_, v___f_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v_ks_1286_; lean_object* v_vs_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1311_; 
v_ks_1286_ = lean_ctor_get(v_x_1282_, 0);
v_vs_1287_ = lean_ctor_get(v_x_1282_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1282_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1289_ = v_x_1282_;
v_isShared_1290_ = v_isSharedCheck_1311_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_vs_1287_);
lean_inc(v_ks_1286_);
lean_dec(v_x_1282_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1311_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = lean_array_get_size(v_ks_1286_);
v___x_1292_ = lean_nat_dec_lt(v_x_1283_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_dec(v_x_1283_);
v___x_1293_ = lean_array_push(v_ks_1286_, v_x_1284_);
v___x_1294_ = lean_array_push(v_vs_1287_, v_x_1285_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v___x_1294_);
lean_ctor_set(v___x_1289_, 0, v___x_1293_);
v___x_1296_ = v___x_1289_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
else
{
lean_object* v_k_x27_1298_; uint8_t v___x_1299_; 
v_k_x27_1298_ = lean_array_fget_borrowed(v_ks_1286_, v_x_1283_);
v___x_1299_ = l_Lean_instBEqMVarId_beq(v_x_1284_, v_k_x27_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1301_; 
if (v_isShared_1290_ == 0)
{
v___x_1301_ = v___x_1289_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_ks_1286_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_vs_1287_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_add(v_x_1283_, v___x_1302_);
lean_dec(v_x_1283_);
v_x_1282_ = v___x_1301_;
v_x_1283_ = v___x_1303_;
goto _start;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1306_ = lean_array_fset(v_ks_1286_, v_x_1283_, v_x_1284_);
v___x_1307_ = lean_array_fset(v_vs_1287_, v_x_1283_, v_x_1285_);
lean_dec(v_x_1283_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v___x_1307_);
lean_ctor_set(v___x_1289_, 0, v___x_1306_);
v___x_1309_ = v___x_1289_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1312_, lean_object* v_k_1313_, lean_object* v_v_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1312_, v___x_1315_, v_k_1313_, v_v_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1317_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1318_, size_t v_x_1319_, size_t v_x_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_es_1323_; size_t v___x_1324_; size_t v___x_1325_; lean_object* v_j_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_es_1323_ = lean_ctor_get(v_x_1318_, 0);
v___x_1324_ = ((size_t)31ULL);
v___x_1325_ = lean_usize_land(v_x_1319_, v___x_1324_);
v_j_1326_ = lean_usize_to_nat(v___x_1325_);
v___x_1327_ = lean_array_get_size(v_es_1323_);
v___x_1328_ = lean_nat_dec_lt(v_j_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec(v_j_1326_);
lean_dec(v_x_1322_);
lean_dec(v_x_1321_);
return v_x_1318_;
}
else
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1367_; 
lean_inc_ref(v_es_1323_);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v_x_1318_, 0);
lean_dec(v_unused_1368_);
v___x_1330_ = v_x_1318_;
v_isShared_1331_ = v_isSharedCheck_1367_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v_x_1318_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1367_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v_v_1332_; lean_object* v___x_1333_; lean_object* v_xs_x27_1334_; lean_object* v___y_1336_; 
v_v_1332_ = lean_array_fget(v_es_1323_, v_j_1326_);
v___x_1333_ = lean_box(0);
v_xs_x27_1334_ = lean_array_fset(v_es_1323_, v_j_1326_, v___x_1333_);
switch(lean_obj_tag(v_v_1332_))
{
case 0:
{
lean_object* v_key_1341_; lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_key_1341_ = lean_ctor_get(v_v_1332_, 0);
v_val_1342_ = lean_ctor_get(v_v_1332_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_v_1332_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1344_ = v_v_1332_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_inc(v_key_1341_);
lean_dec(v_v_1332_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_instBEqMVarId_beq(v_x_1321_, v_key_1341_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_del_object(v___x_1344_);
v___x_1347_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1341_, v_val_1342_, v_x_1321_, v_x_1322_);
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
v___y_1336_ = v___x_1348_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1350_; 
lean_dec(v_val_1342_);
lean_dec(v_key_1341_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_x_1322_);
lean_ctor_set(v___x_1344_, 0, v_x_1321_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_x_1321_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_x_1322_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v___y_1336_ = v___x_1350_;
goto v___jp_1335_;
}
}
}
}
case 1:
{
lean_object* v_node_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1365_; 
v_node_1353_ = lean_ctor_get(v_v_1332_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_v_1332_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1355_ = v_v_1332_;
v_isShared_1356_ = v_isSharedCheck_1365_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_node_1353_);
lean_dec(v_v_1332_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1365_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1357_ = ((size_t)5ULL);
v___x_1358_ = lean_usize_shift_right(v_x_1319_, v___x_1357_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_x_1320_, v___x_1359_);
v___x_1361_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1353_, v___x_1358_, v___x_1360_, v_x_1321_, v_x_1322_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1361_);
v___x_1363_ = v___x_1355_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v___y_1336_ = v___x_1363_;
goto v___jp_1335_;
}
}
}
default: 
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_x_1321_);
lean_ctor_set(v___x_1366_, 1, v_x_1322_);
v___y_1336_ = v___x_1366_;
goto v___jp_1335_;
}
}
v___jp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_array_fset(v_xs_x27_1334_, v_j_1326_, v___y_1336_);
lean_dec(v_j_1326_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1337_);
v___x_1339_ = v___x_1330_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
lean_object* v_ks_1369_; lean_object* v_vs_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1388_; 
v_ks_1369_ = lean_ctor_get(v_x_1318_, 0);
v_vs_1370_ = lean_ctor_get(v_x_1318_, 1);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1372_ = v_x_1318_;
v_isShared_1373_ = v_isSharedCheck_1388_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_vs_1370_);
lean_inc(v_ks_1369_);
lean_dec(v_x_1318_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1388_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_ks_1369_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_vs_1370_);
v___x_1375_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v_newNode_1376_; size_t v___x_1377_; uint8_t v___x_1378_; 
v_newNode_1376_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1375_, v_x_1321_, v_x_1322_);
v___x_1377_ = ((size_t)7ULL);
v___x_1378_ = lean_usize_dec_le(v___x_1377_, v_x_1320_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1379_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1376_);
v___x_1380_ = lean_unsigned_to_nat(4u);
v___x_1381_ = lean_nat_dec_lt(v___x_1379_, v___x_1380_);
lean_dec(v___x_1379_);
if (v___x_1381_ == 0)
{
lean_object* v_ks_1382_; lean_object* v_vs_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_ks_1382_ = lean_ctor_get(v_newNode_1376_, 0);
lean_inc_ref(v_ks_1382_);
v_vs_1383_ = lean_ctor_get(v_newNode_1376_, 1);
lean_inc_ref(v_vs_1383_);
lean_dec_ref(v_newNode_1376_);
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1320_, v_ks_1382_, v_vs_1383_, v___x_1384_, v___x_1385_);
lean_dec_ref(v_vs_1383_);
lean_dec_ref(v_ks_1382_);
return v___x_1386_;
}
else
{
return v_newNode_1376_;
}
}
else
{
return v_newNode_1376_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1318_ = stack[0].m_obj;
size_t v_x_1319_ = stack[1].m_num;
size_t v_x_1320_ = stack[2].m_num;
lean_object* v_x_1321_ = stack[3].m_obj;
lean_object* v_x_1322_ = stack[4].m_obj;
lean_object* v_res_1389_;
v_res_1389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1318_, v_x_1319_, v_x_1320_, v_x_1321_, v_x_1322_);
stack->m_obj
 = v_res_1389_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1390_, lean_object* v_keys_1391_, lean_object* v_vals_1392_, lean_object* v_i_1393_, lean_object* v_entries_1394_){
_start:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_array_get_size(v_keys_1391_);
v___x_1396_ = lean_nat_dec_lt(v_i_1393_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec(v_i_1393_);
return v_entries_1394_;
}
else
{
lean_object* v_k_1397_; lean_object* v_v_1398_; uint64_t v___x_1399_; size_t v_h_1400_; size_t v___x_1401_; lean_object* v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; size_t v_h_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_k_1397_ = lean_array_fget_borrowed(v_keys_1391_, v_i_1393_);
v_v_1398_ = lean_array_fget_borrowed(v_vals_1392_, v_i_1393_);
v___x_1399_ = l_Lean_instHashableMVarId_hash(v_k_1397_);
v_h_1400_ = lean_uint64_to_usize(v___x_1399_);
v___x_1401_ = ((size_t)5ULL);
v___x_1402_ = lean_unsigned_to_nat(1u);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_sub(v_depth_1390_, v___x_1403_);
v___x_1405_ = lean_usize_mul(v___x_1401_, v___x_1404_);
v_h_1406_ = lean_usize_shift_right(v_h_1400_, v___x_1405_);
v___x_1407_ = lean_nat_add(v_i_1393_, v___x_1402_);
lean_dec(v_i_1393_);
lean_inc(v_v_1398_);
lean_inc(v_k_1397_);
v___x_1408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1394_, v_h_1406_, v_depth_1390_, v_k_1397_, v_v_1398_);
v_i_1393_ = v___x_1407_;
v_entries_1394_ = v___x_1408_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1390_ = stack[0].m_num;
lean_object* v_keys_1391_ = stack[1].m_obj;
lean_object* v_vals_1392_ = stack[2].m_obj;
lean_object* v_i_1393_ = stack[3].m_obj;
lean_object* v_entries_1394_ = stack[4].m_obj;
lean_object* v_res_1410_;
v_res_1410_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1390_, v_keys_1391_, v_vals_1392_, v_i_1393_, v_entries_1394_);
stack->m_obj
 = v_res_1410_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1411_, lean_object* v_keys_1412_, lean_object* v_vals_1413_, lean_object* v_i_1414_, lean_object* v_entries_1415_){
_start:
{
size_t v_depth_boxed_1416_; lean_object* v_res_1417_; 
v_depth_boxed_1416_ = lean_unbox_usize(v_depth_1411_);
lean_dec(v_depth_1411_);
v_res_1417_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1416_, v_keys_1412_, v_vals_1413_, v_i_1414_, v_entries_1415_);
lean_dec_ref(v_vals_1413_);
lean_dec_ref(v_keys_1412_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_){
_start:
{
size_t v_x_870__boxed_1423_; size_t v_x_871__boxed_1424_; lean_object* v_res_1425_; 
v_x_870__boxed_1423_ = lean_unbox_usize(v_x_1419_);
lean_dec(v_x_1419_);
v_x_871__boxed_1424_ = lean_unbox_usize(v_x_1420_);
lean_dec(v_x_1420_);
v_res_1425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1418_, v_x_870__boxed_1423_, v_x_871__boxed_1424_, v_x_1421_, v_x_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
uint64_t v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = l_Lean_instHashableMVarId_hash(v_x_1427_);
v___x_1430_ = lean_uint64_to_usize(v___x_1429_);
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1426_, v___x_1430_, v___x_1431_, v_x_1427_, v_x_1428_);
return v___x_1432_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1433_, lean_object* v_val_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_mctx_1438_; lean_object* v_cache_1439_; lean_object* v_zetaDeltaFVarIds_1440_; lean_object* v_postponed_1441_; lean_object* v_diag_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1472_; 
v___x_1437_ = lean_st_ref_take(v___y_1435_);
v_mctx_1438_ = lean_ctor_get(v___x_1437_, 0);
v_cache_1439_ = lean_ctor_get(v___x_1437_, 1);
v_zetaDeltaFVarIds_1440_ = lean_ctor_get(v___x_1437_, 2);
v_postponed_1441_ = lean_ctor_get(v___x_1437_, 3);
v_diag_1442_ = lean_ctor_get(v___x_1437_, 4);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1444_ = v___x_1437_;
v_isShared_1445_ = v_isSharedCheck_1472_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_diag_1442_);
lean_inc(v_postponed_1441_);
lean_inc(v_zetaDeltaFVarIds_1440_);
lean_inc(v_cache_1439_);
lean_inc(v_mctx_1438_);
lean_dec(v___x_1437_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1472_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_depth_1446_; lean_object* v_levelAssignDepth_1447_; lean_object* v_lmvarCounter_1448_; lean_object* v_mvarCounter_1449_; lean_object* v_lDecls_1450_; lean_object* v_decls_1451_; lean_object* v_userNames_1452_; lean_object* v_lAssignment_1453_; lean_object* v_eAssignment_1454_; lean_object* v_dAssignment_1455_; lean_object* v_instanceTypedMVars_1456_; lean_object* v_synthNormMemo_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1471_; 
v_depth_1446_ = lean_ctor_get(v_mctx_1438_, 0);
v_levelAssignDepth_1447_ = lean_ctor_get(v_mctx_1438_, 1);
v_lmvarCounter_1448_ = lean_ctor_get(v_mctx_1438_, 2);
v_mvarCounter_1449_ = lean_ctor_get(v_mctx_1438_, 3);
v_lDecls_1450_ = lean_ctor_get(v_mctx_1438_, 4);
v_decls_1451_ = lean_ctor_get(v_mctx_1438_, 5);
v_userNames_1452_ = lean_ctor_get(v_mctx_1438_, 6);
v_lAssignment_1453_ = lean_ctor_get(v_mctx_1438_, 7);
v_eAssignment_1454_ = lean_ctor_get(v_mctx_1438_, 8);
v_dAssignment_1455_ = lean_ctor_get(v_mctx_1438_, 9);
v_instanceTypedMVars_1456_ = lean_ctor_get(v_mctx_1438_, 10);
v_synthNormMemo_1457_ = lean_ctor_get(v_mctx_1438_, 11);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_mctx_1438_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1459_ = v_mctx_1438_;
v_isShared_1460_ = v_isSharedCheck_1471_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_synthNormMemo_1457_);
lean_inc(v_instanceTypedMVars_1456_);
lean_inc(v_dAssignment_1455_);
lean_inc(v_eAssignment_1454_);
lean_inc(v_lAssignment_1453_);
lean_inc(v_userNames_1452_);
lean_inc(v_decls_1451_);
lean_inc(v_lDecls_1450_);
lean_inc(v_mvarCounter_1449_);
lean_inc(v_lmvarCounter_1448_);
lean_inc(v_levelAssignDepth_1447_);
lean_inc(v_depth_1446_);
lean_dec(v_mctx_1438_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1471_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1461_ = lean_box(0);
v___x_1462_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1454_, v_mvarId_1433_, v_val_1434_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 8, v___x_1462_);
v___x_1464_ = v___x_1459_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_depth_1446_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_levelAssignDepth_1447_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_lmvarCounter_1448_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_mvarCounter_1449_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v_lDecls_1450_);
lean_ctor_set(v_reuseFailAlloc_1470_, 5, v_decls_1451_);
lean_ctor_set(v_reuseFailAlloc_1470_, 6, v_userNames_1452_);
lean_ctor_set(v_reuseFailAlloc_1470_, 7, v_lAssignment_1453_);
lean_ctor_set(v_reuseFailAlloc_1470_, 8, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1470_, 9, v_dAssignment_1455_);
lean_ctor_set(v_reuseFailAlloc_1470_, 10, v_instanceTypedMVars_1456_);
lean_ctor_set(v_reuseFailAlloc_1470_, 11, v_synthNormMemo_1457_);
v___x_1464_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1464_);
v___x_1466_ = v___x_1444_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_cache_1439_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_zetaDeltaFVarIds_1440_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_postponed_1441_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_diag_1442_);
v___x_1466_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_st_ref_put(v___y_1435_, v___x_1466_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1461_);
return v___x_1468_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1433_ = stack[0].m_obj;
lean_object* v_val_1434_ = stack[1].m_obj;
lean_object* v___y_1435_ = stack[2].m_obj;
lean_object* v_res_1473_;
v_res_1473_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1433_, v_val_1434_, v___y_1435_);
stack->m_obj
 = v_res_1473_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1474_, lean_object* v_val_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1474_, v_val_1475_, v___y_1476_);
lean_dec(v___y_1476_);
return v_res_1478_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
lean_inc(v_g_1479_);
v___x_1485_ = l_Lean_MVarId_getType(v_g_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = lean_box(0);
v___x_1488_ = l_Lean_Meta_synthInstance(v_a_1486_, v___x_1487_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1479_, v_a_1489_, v___y_1481_);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v___x_1490_, 0);
lean_dec(v_unused_1499_);
v___x_1492_ = v___x_1490_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v___x_1490_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_box(0);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_g_1479_);
v_a_1500_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1488_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1488_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_g_1479_);
v_a_1508_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1485_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1485_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1479_ = stack[0].m_obj;
lean_object* v___y_1480_ = stack[1].m_obj;
lean_object* v___y_1481_ = stack[2].m_obj;
lean_object* v___y_1482_ = stack[3].m_obj;
lean_object* v___y_1483_ = stack[4].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1525_){
_start:
{
lean_object* v___f_1526_; lean_object* v___x_1527_; 
v___f_1526_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1527_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1525_, v___f_1526_);
return v___x_1527_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1528_, lean_object* v_val_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1528_, v_val_1529_, v___y_1531_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1528_ = stack[0].m_obj;
lean_object* v_val_1529_ = stack[1].m_obj;
lean_object* v___y_1530_ = stack[2].m_obj;
lean_object* v___y_1531_ = stack[3].m_obj;
lean_object* v___y_1532_ = stack[4].m_obj;
lean_object* v___y_1533_ = stack[5].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1528_, v_val_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1537_, lean_object* v_val_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1537_, v_val_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1546_, v_x_1547_, v_x_1548_);
return v___x_1549_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1550_, lean_object* v_x_1551_, size_t v_x_1552_, size_t v_x_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1551_, v_x_1552_, v_x_1553_, v_x_1554_, v_x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1551_ = stack[1].m_obj;
size_t v_x_1552_ = stack[2].m_num;
size_t v_x_1553_ = stack[3].m_num;
lean_object* v_x_1554_ = stack[4].m_obj;
lean_object* v_x_1555_ = stack[5].m_obj;
lean_object* v_res_1557_;
v_res_1557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_box(0), v_x_1551_, v_x_1552_, v_x_1553_, v_x_1554_, v_x_1555_);
stack->m_obj
 = v_res_1557_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
size_t v_x_1364__boxed_1564_; size_t v_x_1365__boxed_1565_; lean_object* v_res_1566_; 
v_x_1364__boxed_1564_ = lean_unbox_usize(v_x_1560_);
lean_dec(v_x_1560_);
v_x_1365__boxed_1565_ = lean_unbox_usize(v_x_1561_);
lean_dec(v_x_1561_);
v_res_1566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1558_, v_x_1559_, v_x_1364__boxed_1564_, v_x_1365__boxed_1565_, v_x_1562_, v_x_1563_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1567_, lean_object* v_n_1568_, lean_object* v_k_1569_, lean_object* v_v_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1568_, v_k_1569_, v_v_1570_);
return v___x_1571_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1572_, size_t v_depth_1573_, lean_object* v_keys_1574_, lean_object* v_vals_1575_, lean_object* v_heq_1576_, lean_object* v_i_1577_, lean_object* v_entries_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1573_, v_keys_1574_, v_vals_1575_, v_i_1577_, v_entries_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1573_ = stack[1].m_num;
lean_object* v_keys_1574_ = stack[2].m_obj;
lean_object* v_vals_1575_ = stack[3].m_obj;
lean_object* v_i_1577_ = stack[5].m_obj;
lean_object* v_entries_1578_ = stack[6].m_obj;
lean_object* v_res_1580_;
v_res_1580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_depth_1573_, v_keys_1574_, v_vals_1575_, lean_box(0), v_i_1577_, v_entries_1578_);
stack->m_obj
 = v_res_1580_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1581_, lean_object* v_depth_1582_, lean_object* v_keys_1583_, lean_object* v_vals_1584_, lean_object* v_heq_1585_, lean_object* v_i_1586_, lean_object* v_entries_1587_){
_start:
{
size_t v_depth_boxed_1588_; lean_object* v_res_1589_; 
v_depth_boxed_1588_ = lean_unbox_usize(v_depth_1582_);
lean_dec(v_depth_1582_);
v_res_1589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1581_, v_depth_boxed_1588_, v_keys_1583_, v_vals_1584_, v_heq_1585_, v_i_1586_, v_entries_1587_);
lean_dec_ref(v_vals_1584_);
lean_dec_ref(v_keys_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1591_, v_x_1592_, v_x_1593_, v_x_1594_);
return v___x_1595_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1596_, lean_object* v_discharge_1597_, lean_object* v_g_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v_g_1598_);
v___x_1604_ = lean_apply_6(v_discharge_1596_, v_g_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, lean_box(0));
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec(v_g_1598_);
lean_dec_ref(v_discharge_1597_);
return v___x_1604_;
}
else
{
lean_object* v_a_1605_; uint8_t v___y_1607_; uint8_t v___x_1609_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
v___x_1609_ = l_Lean_Exception_isInterrupt(v_a_1605_);
if (v___x_1609_ == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = l_Lean_Exception_isRuntime(v_a_1605_);
v___y_1607_ = v___x_1610_;
goto v___jp_1606_;
}
else
{
lean_dec(v_a_1605_);
v___y_1607_ = v___x_1609_;
goto v___jp_1606_;
}
v___jp_1606_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref_known(v___x_1604_, 1);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
v___x_1608_ = lean_apply_6(v_discharge_1597_, v_g_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, lean_box(0));
return v___x_1608_;
}
else
{
lean_dec(v_g_1598_);
lean_dec_ref(v_discharge_1597_);
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_discharge_1596_ = stack[0].m_obj;
lean_object* v_discharge_1597_ = stack[1].m_obj;
lean_object* v_g_1598_ = stack[2].m_obj;
lean_object* v___y_1599_ = stack[3].m_obj;
lean_object* v___y_1600_ = stack[4].m_obj;
lean_object* v___y_1601_ = stack[5].m_obj;
lean_object* v___y_1602_ = stack[6].m_obj;
lean_object* v_res_1611_;
v_res_1611_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1596_, v_discharge_1597_, v_g_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
stack->m_obj
 = v_res_1611_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1612_, lean_object* v_discharge_1613_, lean_object* v_g_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1612_, v_discharge_1613_, v_g_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1621_, lean_object* v_discharge_1622_){
_start:
{
lean_object* v_toApplyRulesConfig_1623_; lean_object* v_toBacktrackConfig_1624_; uint8_t v_backtracking_1625_; uint8_t v_intro_1626_; uint8_t v_constructor_1627_; uint8_t v_suggestions_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1660_; 
v_toApplyRulesConfig_1623_ = lean_ctor_get(v_cfg_1621_, 0);
lean_inc_ref(v_toApplyRulesConfig_1623_);
v_toBacktrackConfig_1624_ = lean_ctor_get(v_toApplyRulesConfig_1623_, 0);
lean_inc_ref(v_toBacktrackConfig_1624_);
v_backtracking_1625_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*1);
v_intro_1626_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*1 + 1);
v_constructor_1627_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*1 + 2);
v_suggestions_1628_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*1 + 3);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_cfg_1621_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_cfg_1621_, 0);
lean_dec(v_unused_1661_);
v___x_1630_ = v_cfg_1621_;
v_isShared_1631_ = v_isSharedCheck_1660_;
goto v_resetjp_1629_;
}
else
{
lean_dec(v_cfg_1621_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1660_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_toApplyConfig_1632_; uint8_t v_transparency_1633_; uint8_t v_symm_1634_; uint8_t v_exfalso_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1658_; 
v_toApplyConfig_1632_ = lean_ctor_get(v_toApplyRulesConfig_1623_, 1);
v_transparency_1633_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1623_, sizeof(void*)*2);
v_symm_1634_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1623_, sizeof(void*)*2 + 1);
v_exfalso_1635_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1623_, sizeof(void*)*2 + 2);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_toApplyRulesConfig_1623_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_toApplyRulesConfig_1623_, 0);
lean_dec(v_unused_1659_);
v___x_1637_ = v_toApplyRulesConfig_1623_;
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_toApplyConfig_1632_);
lean_dec(v_toApplyRulesConfig_1623_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_maxDepth_1639_; lean_object* v_proc_1640_; lean_object* v_suspend_1641_; lean_object* v_discharge_1642_; uint8_t v_commitIndependentGoals_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1657_; 
v_maxDepth_1639_ = lean_ctor_get(v_toBacktrackConfig_1624_, 0);
v_proc_1640_ = lean_ctor_get(v_toBacktrackConfig_1624_, 1);
v_suspend_1641_ = lean_ctor_get(v_toBacktrackConfig_1624_, 2);
v_discharge_1642_ = lean_ctor_get(v_toBacktrackConfig_1624_, 3);
v_commitIndependentGoals_1643_ = lean_ctor_get_uint8(v_toBacktrackConfig_1624_, sizeof(void*)*4);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_toBacktrackConfig_1624_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1645_ = v_toBacktrackConfig_1624_;
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_discharge_1642_);
lean_inc(v_suspend_1641_);
lean_inc(v_proc_1640_);
lean_inc(v_maxDepth_1639_);
lean_dec(v_toBacktrackConfig_1624_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___f_1647_; lean_object* v___x_1649_; 
v___f_1647_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1647_, 0, v_discharge_1622_);
lean_closure_set(v___f_1647_, 1, v_discharge_1642_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 3, v___f_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_maxDepth_1639_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_proc_1640_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_suspend_1641_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v___f_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, sizeof(void*)*4, v_commitIndependentGoals_1643_);
v___x_1649_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1649_);
v___x_1651_ = v___x_1637_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_toApplyConfig_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*2, v_transparency_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*2 + 1, v_symm_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*2 + 2, v_exfalso_1635_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1651_);
v___x_1653_ = v___x_1630_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*1, v_backtracking_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*1 + 1, v_intro_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*1 + 2, v_constructor_1627_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*1 + 3, v_suggestions_1628_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = 1;
v___x_1669_ = l_Lean_Meta_intro1Core(v_g_1662_, v___x_1668_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1688_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_snd_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1686_; 
v_snd_1674_ = lean_ctor_get(v_a_1670_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_a_1670_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_a_1670_, 0);
lean_dec(v_unused_1687_);
v___x_1676_ = v_a_1670_;
v_isShared_1677_ = v_isSharedCheck_1686_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_snd_1674_);
lean_dec(v_a_1670_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1686_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_box(0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 1);
lean_ctor_set(v___x_1676_, 1, v___x_1678_);
lean_ctor_set(v___x_1676_, 0, v_snd_1674_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_snd_1674_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1681_);
v___x_1683_ = v___x_1672_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1669_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1669_);
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
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1662_ = stack[0].m_obj;
lean_object* v___y_1663_ = stack[1].m_obj;
lean_object* v___y_1664_ = stack[2].m_obj;
lean_object* v___y_1665_ = stack[3].m_obj;
lean_object* v___y_1666_ = stack[4].m_obj;
lean_object* v_res_1697_;
v_res_1697_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
stack->m_obj
 = v_res_1697_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1706_){
_start:
{
lean_object* v___f_1707_; lean_object* v___x_1708_; 
v___f_1707_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1708_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1706_, v___f_1707_);
return v___x_1708_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1720_ = l_Lean_MVarId_constructor(v_g_1713_, v___x_1719_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1729_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_a_1721_);
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
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1720_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1713_ = stack[0].m_obj;
lean_object* v___y_1714_ = stack[1].m_obj;
lean_object* v___y_1715_ = stack[2].m_obj;
lean_object* v___y_1716_ = stack[3].m_obj;
lean_object* v___y_1717_ = stack[4].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1747_){
_start:
{
lean_object* v___f_1748_; lean_object* v___x_1749_; 
v___f_1748_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1749_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1747_, v___f_1748_);
return v___x_1749_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
lean_inc(v_g_1752_);
v___x_1758_ = l_Lean_MVarId_getType(v_g_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = lean_box(0);
v___x_1761_ = l_Lean_Meta_synthInstance(v_a_1759_, v___x_1760_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1771_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1752_, v_a_1762_, v___y_1754_);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1763_, 0);
lean_dec(v_unused_1772_);
v___x_1765_ = v___x_1763_;
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v___x_1763_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_g_1752_);
v_a_1773_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1761_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1761_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
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
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_g_1752_);
v_a_1781_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1758_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1758_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1752_ = stack[0].m_obj;
lean_object* v___y_1753_ = stack[1].m_obj;
lean_object* v___y_1754_ = stack[2].m_obj;
lean_object* v___y_1755_ = stack[3].m_obj;
lean_object* v___y_1756_ = stack[4].m_obj;
lean_object* v_res_1789_;
v_res_1789_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
stack->m_obj
 = v_res_1789_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1798_){
_start:
{
lean_object* v___f_1799_; lean_object* v___x_1800_; 
v___f_1799_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1800_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1798_, v___f_1799_);
return v___x_1800_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Lean_Expr_hasMVar(v_e_1801_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_e_1801_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v_mctx_1807_; lean_object* v___x_1808_; lean_object* v_fst_1809_; lean_object* v_snd_1810_; lean_object* v___x_1811_; lean_object* v_cache_1812_; lean_object* v_zetaDeltaFVarIds_1813_; lean_object* v_postponed_1814_; lean_object* v_diag_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
v___x_1806_ = lean_st_ref_get(v___y_1802_);
v_mctx_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc_ref(v_mctx_1807_);
lean_dec(v___x_1806_);
v___x_1808_ = l_Lean_instantiateMVarsCore(v_mctx_1807_, v_e_1801_);
v_fst_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_fst_1809_);
v_snd_1810_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_snd_1810_);
lean_dec_ref(v___x_1808_);
v___x_1811_ = lean_st_ref_take(v___y_1802_);
v_cache_1812_ = lean_ctor_get(v___x_1811_, 1);
v_zetaDeltaFVarIds_1813_ = lean_ctor_get(v___x_1811_, 2);
v_postponed_1814_ = lean_ctor_get(v___x_1811_, 3);
v_diag_1815_ = lean_ctor_get(v___x_1811_, 4);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1825_);
v___x_1817_ = v___x_1811_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_diag_1815_);
lean_inc(v_postponed_1814_);
lean_inc(v_zetaDeltaFVarIds_1813_);
lean_inc(v_cache_1812_);
lean_dec(v___x_1811_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v_snd_1810_);
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_snd_1810_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_cache_1812_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_zetaDeltaFVarIds_1813_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_postponed_1814_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_diag_1815_);
v___x_1820_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_st_ref_put(v___y_1802_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_fst_1809_);
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1801_ = stack[0].m_obj;
lean_object* v___y_1802_ = stack[1].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1801_, v___y_1802_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1827_, v___y_1828_);
lean_dec(v___y_1828_);
return v_res_1830_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1831_, v___y_1833_);
return v___x_1837_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1831_ = stack[0].m_obj;
lean_object* v___y_1832_ = stack[1].m_obj;
lean_object* v___y_1833_ = stack[2].m_obj;
lean_object* v___y_1834_ = stack[3].m_obj;
lean_object* v___y_1835_ = stack[4].m_obj;
lean_object* v_res_1838_;
v_res_1838_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
stack->m_obj
 = v_res_1838_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1845_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1846_, lean_object* v_x_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1846_, v_x_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1853_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1853_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1846_ = stack[0].m_obj;
lean_object* v_x_1847_ = stack[1].m_obj;
lean_object* v___y_1848_ = stack[2].m_obj;
lean_object* v___y_1849_ = stack[3].m_obj;
lean_object* v___y_1850_ = stack[4].m_obj;
lean_object* v___y_1851_ = stack[5].m_obj;
lean_object* v_res_1870_;
v_res_1870_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1846_, v_x_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
stack->m_obj
 = v_res_1870_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1871_, lean_object* v_x_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1871_, v_x_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1879_, lean_object* v_mvarId_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1880_, v_x_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1880_ = stack[1].m_obj;
lean_object* v_x_1881_ = stack[2].m_obj;
lean_object* v___y_1882_ = stack[3].m_obj;
lean_object* v___y_1883_ = stack[4].m_obj;
lean_object* v___y_1884_ = stack[5].m_obj;
lean_object* v___y_1885_ = stack[6].m_obj;
lean_object* v_res_1888_;
v_res_1888_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_box(0), v_mvarId_1880_, v_x_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
stack->m_obj
 = v_res_1888_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_mvarId_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1889_, v_mvarId_1890_, v_x_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_ref_1904_; lean_object* v___x_1905_; lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1914_; 
v_ref_1904_ = lean_ctor_get(v___y_1901_, 2);
v___x_1905_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_inc(v_ref_1904_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_ref_1904_);
lean_ctor_set(v___x_1910_, 1, v_a_1906_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 1);
lean_ctor_set(v___x_1908_, 0, v___x_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1898_ = stack[0].m_obj;
lean_object* v___y_1899_ = stack[1].m_obj;
lean_object* v___y_1900_ = stack[2].m_obj;
lean_object* v___y_1901_ = stack[3].m_obj;
lean_object* v___y_1902_ = stack[4].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = l_List_reverse___redArg(v_x_1924_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
else
{
lean_object* v_head_1932_; lean_object* v_tail_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1953_; 
v_head_1932_ = lean_ctor_get(v_x_1923_, 0);
v_tail_1933_ = lean_ctor_get(v_x_1923_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1923_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1935_ = v_x_1923_;
v_isShared_1936_ = v_isSharedCheck_1953_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_tail_1933_);
lean_inc(v_head_1932_);
lean_dec(v_x_1923_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1953_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_inc(v_head_1932_);
v___x_1937_ = l_Lean_Expr_mvar___override(v_head_1932_);
v___x_1938_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1938_, 0, v___x_1937_);
v___x_1939_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1932_, v___x_1938_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_x_1924_);
lean_ctor_set(v___x_1935_, 0, v_a_1940_);
v___x_1942_ = v___x_1935_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1940_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_x_1924_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_x_1923_ = v_tail_1933_;
v_x_1924_ = v___x_1942_;
goto _start;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1935_);
lean_dec(v_tail_1933_);
lean_dec(v_x_1924_);
v_a_1945_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1939_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1939_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1923_ = stack[0].m_obj;
lean_object* v_x_1924_ = stack[1].m_obj;
lean_object* v___y_1925_ = stack[2].m_obj;
lean_object* v___y_1926_ = stack[3].m_obj;
lean_object* v___y_1927_ = stack[4].m_obj;
lean_object* v___y_1928_ = stack[5].m_obj;
lean_object* v_res_1954_;
v_res_1954_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1923_, v_x_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
stack->m_obj
 = v_res_1954_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1955_, v_x_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1962_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
return v___x_1965_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1966_, lean_object* v_proc_1967_, lean_object* v_orig_1968_, lean_object* v_goals_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_box(0);
lean_inc(v_orig_1968_);
v___x_1976_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1968_, v___x_1975_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
v___x_1978_ = lean_apply_6(v_test_1966_, v_a_1977_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, lean_box(0));
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; uint8_t v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = lean_unbox(v_a_1979_);
lean_dec(v_a_1979_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_goals_1969_);
lean_dec(v_orig_1968_);
lean_dec_ref(v_proc_1967_);
v___x_1981_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1982_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1981_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
else
{
lean_object* v___x_1991_; 
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
v___x_1991_ = lean_apply_7(v_proc_1967_, v_orig_1968_, v_goals_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, lean_box(0));
return v___x_1991_;
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_goals_1969_);
lean_dec(v_orig_1968_);
lean_dec_ref(v_proc_1967_);
v_a_1992_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1978_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1978_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_goals_1969_);
lean_dec(v_orig_1968_);
lean_dec_ref(v_proc_1967_);
lean_dec_ref(v_test_1966_);
v_a_2000_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1976_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1976_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
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
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_test_1966_ = stack[0].m_obj;
lean_object* v_proc_1967_ = stack[1].m_obj;
lean_object* v_orig_1968_ = stack[2].m_obj;
lean_object* v_goals_1969_ = stack[3].m_obj;
lean_object* v___y_1970_ = stack[4].m_obj;
lean_object* v___y_1971_ = stack[5].m_obj;
lean_object* v___y_1972_ = stack[6].m_obj;
lean_object* v___y_1973_ = stack[7].m_obj;
lean_object* v_res_2008_;
v_res_2008_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1966_, v_proc_1967_, v_orig_1968_, v_goals_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
stack->m_obj
 = v_res_2008_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2009_, lean_object* v_proc_2010_, lean_object* v_orig_2011_, lean_object* v_goals_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2009_, v_proc_2010_, v_orig_2011_, v_goals_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2019_, lean_object* v_test_2020_){
_start:
{
lean_object* v_toApplyRulesConfig_2021_; lean_object* v_toBacktrackConfig_2022_; uint8_t v_backtracking_2023_; uint8_t v_intro_2024_; uint8_t v_constructor_2025_; uint8_t v_suggestions_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2058_; 
v_toApplyRulesConfig_2021_ = lean_ctor_get(v_cfg_2019_, 0);
lean_inc_ref(v_toApplyRulesConfig_2021_);
v_toBacktrackConfig_2022_ = lean_ctor_get(v_toApplyRulesConfig_2021_, 0);
lean_inc_ref(v_toBacktrackConfig_2022_);
v_backtracking_2023_ = lean_ctor_get_uint8(v_cfg_2019_, sizeof(void*)*1);
v_intro_2024_ = lean_ctor_get_uint8(v_cfg_2019_, sizeof(void*)*1 + 1);
v_constructor_2025_ = lean_ctor_get_uint8(v_cfg_2019_, sizeof(void*)*1 + 2);
v_suggestions_2026_ = lean_ctor_get_uint8(v_cfg_2019_, sizeof(void*)*1 + 3);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_cfg_2019_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_cfg_2019_, 0);
lean_dec(v_unused_2059_);
v___x_2028_ = v_cfg_2019_;
v_isShared_2029_ = v_isSharedCheck_2058_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v_cfg_2019_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2058_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_toApplyConfig_2030_; uint8_t v_transparency_2031_; uint8_t v_symm_2032_; uint8_t v_exfalso_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2056_; 
v_toApplyConfig_2030_ = lean_ctor_get(v_toApplyRulesConfig_2021_, 1);
v_transparency_2031_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2021_, sizeof(void*)*2);
v_symm_2032_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2021_, sizeof(void*)*2 + 1);
v_exfalso_2033_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2021_, sizeof(void*)*2 + 2);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_toApplyRulesConfig_2021_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_toApplyRulesConfig_2021_, 0);
lean_dec(v_unused_2057_);
v___x_2035_ = v_toApplyRulesConfig_2021_;
v_isShared_2036_ = v_isSharedCheck_2056_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_toApplyConfig_2030_);
lean_dec(v_toApplyRulesConfig_2021_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2056_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_maxDepth_2037_; lean_object* v_proc_2038_; lean_object* v_suspend_2039_; lean_object* v_discharge_2040_; uint8_t v_commitIndependentGoals_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2055_; 
v_maxDepth_2037_ = lean_ctor_get(v_toBacktrackConfig_2022_, 0);
v_proc_2038_ = lean_ctor_get(v_toBacktrackConfig_2022_, 1);
v_suspend_2039_ = lean_ctor_get(v_toBacktrackConfig_2022_, 2);
v_discharge_2040_ = lean_ctor_get(v_toBacktrackConfig_2022_, 3);
v_commitIndependentGoals_2041_ = lean_ctor_get_uint8(v_toBacktrackConfig_2022_, sizeof(void*)*4);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_toBacktrackConfig_2022_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2043_ = v_toBacktrackConfig_2022_;
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_discharge_2040_);
lean_inc(v_suspend_2039_);
lean_inc(v_proc_2038_);
lean_inc(v_maxDepth_2037_);
lean_dec(v_toBacktrackConfig_2022_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___f_2045_; lean_object* v___x_2047_; 
v___f_2045_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2045_, 0, v_test_2020_);
lean_closure_set(v___f_2045_, 1, v_proc_2038_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___f_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_maxDepth_2037_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___f_2045_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_suspend_2039_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_discharge_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*4, v_commitIndependentGoals_2041_);
v___x_2047_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2047_);
v___x_2049_ = v___x_2035_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_toApplyConfig_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*2, v_transparency_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*2 + 1, v_symm_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*2 + 2, v_exfalso_2033_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2049_);
v___x_2051_ = v___x_2028_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*1, v_backtracking_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*1 + 1, v_intro_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*1 + 2, v_constructor_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*1 + 3, v_suggestions_2026_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2060_, lean_object* v_msg_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2061_ = stack[1].m_obj;
lean_object* v___y_2062_ = stack[2].m_obj;
lean_object* v___y_2063_ = stack[3].m_obj;
lean_object* v___y_2064_ = stack[4].m_obj;
lean_object* v___y_2065_ = stack[5].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_box(0), v_msg_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2069_, v_msg_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2076_;
}
}
uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
uint8_t v___x_2078_; 
v___x_2078_ = 0;
return v___x_2078_;
}
else
{
lean_object* v_head_2079_; lean_object* v_tail_2080_; uint8_t v___x_2081_; 
v_head_2079_ = lean_ctor_get(v_x_2077_, 0);
v_tail_2080_ = lean_ctor_get(v_x_2077_, 1);
v___x_2081_ = l_Lean_Expr_hasMVar(v_head_2079_);
if (v___x_2081_ == 0)
{
v_x_2077_ = v_tail_2080_;
goto _start;
}
else
{
return v___x_2081_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2077_ = stack[0].m_obj;
uint8_t v_res_2083_;
v_res_2083_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2077_);
stack->m_num = v_res_2083_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2084_){
_start:
{
uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_res_2085_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2084_);
lean_dec(v_x_2084_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2087_, lean_object* v_sols_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2088_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
lean_inc(v___y_2092_);
lean_inc_ref(v___y_2091_);
lean_inc(v___y_2090_);
lean_inc_ref(v___y_2089_);
v___x_2095_ = lean_apply_6(v_test_2087_, v_sols_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, lean_box(0));
return v___x_2095_;
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v_sols_2088_);
lean_dec_ref(v_test_2087_);
v___x_2096_ = lean_box(v___x_2094_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_test_2087_ = stack[0].m_obj;
lean_object* v_sols_2088_ = stack[1].m_obj;
lean_object* v___y_2089_ = stack[2].m_obj;
lean_object* v___y_2090_ = stack[3].m_obj;
lean_object* v___y_2091_ = stack[4].m_obj;
lean_object* v___y_2092_ = stack[5].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2087_, v_sols_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2099_, lean_object* v_sols_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2099_, v_sols_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2107_, lean_object* v_test_2108_){
_start:
{
lean_object* v___f_2109_; lean_object* v___x_2110_; 
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2109_, 0, v_test_2108_);
v___x_2110_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2107_, v___f_2109_);
return v___x_2110_;
}
}
uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
uint8_t v___x_2113_; 
lean_dec_ref(v_e_2111_);
v___x_2113_ = 0;
return v___x_2113_;
}
else
{
lean_object* v_head_2114_; lean_object* v_tail_2115_; uint8_t v___x_2116_; 
v_head_2114_ = lean_ctor_get(v_x_2112_, 0);
v_tail_2115_ = lean_ctor_get(v_x_2112_, 1);
lean_inc_ref(v_e_2111_);
v___x_2116_ = l_Lean_Expr_occurs(v_e_2111_, v_head_2114_);
if (v___x_2116_ == 0)
{
v_x_2112_ = v_tail_2115_;
goto _start;
}
else
{
lean_dec_ref(v_e_2111_);
return v___x_2116_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2111_ = stack[0].m_obj;
lean_object* v_x_2112_ = stack[1].m_obj;
uint8_t v_res_2118_;
v_res_2118_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2111_, v_x_2112_);
stack->m_num = v_res_2118_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2119_, lean_object* v_x_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2119_, v_x_2120_);
lean_dec(v_x_2120_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2123_, lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = 1;
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; uint8_t v___x_2128_; 
v_head_2126_ = lean_ctor_get(v_x_2124_, 0);
lean_inc(v_head_2126_);
v_tail_2127_ = lean_ctor_get(v_x_2124_, 1);
lean_inc(v_tail_2127_);
lean_dec_ref_known(v_x_2124_, 2);
v___x_2128_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2126_, v_sols_2123_);
if (v___x_2128_ == 0)
{
lean_dec(v_tail_2127_);
return v___x_2128_;
}
else
{
v_x_2124_ = v_tail_2127_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_sols_2123_ = stack[0].m_obj;
lean_object* v_x_2124_ = stack[1].m_obj;
uint8_t v_res_2130_;
v_res_2130_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2123_, v_x_2124_);
stack->m_num = v_res_2130_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2131_, lean_object* v_x_2132_){
_start:
{
uint8_t v_res_2133_; lean_object* v_r_2134_; 
v_res_2133_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2131_, v_x_2132_);
lean_dec(v_sols_2131_);
v_r_2134_ = lean_box(v_res_2133_);
return v_r_2134_;
}
}
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2135_, lean_object* v_sols_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2136_, v_use_2135_);
v___x_2143_ = lean_box(v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_use_2135_ = stack[0].m_obj;
lean_object* v_sols_2136_ = stack[1].m_obj;
lean_object* v___y_2137_ = stack[2].m_obj;
lean_object* v___y_2138_ = stack[3].m_obj;
lean_object* v___y_2139_ = stack[4].m_obj;
lean_object* v___y_2140_ = stack[5].m_obj;
lean_object* v_res_2145_;
v_res_2145_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2135_, v_sols_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
stack->m_obj
 = v_res_2145_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2146_, lean_object* v_sols_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2146_, v_sols_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v_sols_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2154_, lean_object* v_use_2155_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; 
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2156_, 0, v_use_2155_);
v___x_2157_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2154_, v___f_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2158_){
_start:
{
lean_object* v___y_2160_; lean_object* v_toApplyRulesConfig_2161_; uint8_t v_backtracking_2162_; uint8_t v_intro_2163_; uint8_t v_constructor_2164_; uint8_t v_suggestions_2165_; uint8_t v_intro_2169_; 
v_intro_2169_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1 + 1);
if (v_intro_2169_ == 0)
{
lean_object* v_toApplyRulesConfig_2170_; uint8_t v_backtracking_2171_; uint8_t v_constructor_2172_; uint8_t v_suggestions_2173_; 
v_toApplyRulesConfig_2170_ = lean_ctor_get(v_cfg_2158_, 0);
lean_inc_ref(v_toApplyRulesConfig_2170_);
v_backtracking_2171_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1);
v_constructor_2172_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1 + 2);
v_suggestions_2173_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1 + 3);
v___y_2160_ = v_cfg_2158_;
v_toApplyRulesConfig_2161_ = v_toApplyRulesConfig_2170_;
v_backtracking_2162_ = v_backtracking_2171_;
v_intro_2163_ = v_intro_2169_;
v_constructor_2164_ = v_constructor_2172_;
v_suggestions_2165_ = v_suggestions_2173_;
goto v___jp_2159_;
}
else
{
lean_object* v_toApplyRulesConfig_2174_; uint8_t v_backtracking_2175_; uint8_t v_constructor_2176_; uint8_t v_suggestions_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2191_; 
v_toApplyRulesConfig_2174_ = lean_ctor_get(v_cfg_2158_, 0);
v_backtracking_2175_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1);
v_constructor_2176_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1 + 2);
v_suggestions_2177_ = lean_ctor_get_uint8(v_cfg_2158_, sizeof(void*)*1 + 3);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_cfg_2158_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2179_ = v_cfg_2158_;
v_isShared_2180_ = v_isSharedCheck_2191_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_toApplyRulesConfig_2174_);
lean_dec(v_cfg_2158_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2191_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = 0;
if (v_isShared_2180_ == 0)
{
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_toApplyRulesConfig_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*1, v_backtracking_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*1 + 2, v_constructor_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*1 + 3, v_suggestions_2177_);
v___x_2183_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v_toApplyRulesConfig_2185_; uint8_t v_backtracking_2186_; uint8_t v_intro_2187_; uint8_t v_constructor_2188_; uint8_t v_suggestions_2189_; 
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*1 + 1, v___x_2181_);
v___x_2184_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2183_);
v_toApplyRulesConfig_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc_ref(v_toApplyRulesConfig_2185_);
v_backtracking_2186_ = lean_ctor_get_uint8(v___x_2184_, sizeof(void*)*1);
v_intro_2187_ = lean_ctor_get_uint8(v___x_2184_, sizeof(void*)*1 + 1);
v_constructor_2188_ = lean_ctor_get_uint8(v___x_2184_, sizeof(void*)*1 + 2);
v_suggestions_2189_ = lean_ctor_get_uint8(v___x_2184_, sizeof(void*)*1 + 3);
v___y_2160_ = v___x_2184_;
v_toApplyRulesConfig_2161_ = v_toApplyRulesConfig_2185_;
v_backtracking_2162_ = v_backtracking_2186_;
v_intro_2163_ = v_intro_2187_;
v_constructor_2164_ = v_constructor_2188_;
v_suggestions_2165_ = v_suggestions_2189_;
goto v___jp_2159_;
}
}
}
v___jp_2159_:
{
if (v_constructor_2164_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2161_);
return v___y_2160_;
}
else
{
uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec_ref(v___y_2160_);
v___x_2166_ = 0;
v___x_2167_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2167_, 0, v_toApplyRulesConfig_2161_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1, v_backtracking_2162_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1 + 1, v_intro_2163_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1 + 2, v___x_2166_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1 + 3, v_suggestions_2165_);
v___x_2168_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2167_);
return v___x_2168_;
}
}
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = l_List_reverse___redArg(v_x_2193_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v_head_2203_; lean_object* v_tail_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2222_; 
v_head_2203_ = lean_ctor_get(v_x_2192_, 0);
v_tail_2204_ = lean_ctor_get(v_x_2192_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2206_ = v_x_2192_;
v_isShared_2207_ = v_isSharedCheck_2222_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_tail_2204_);
lean_inc(v_head_2203_);
lean_dec(v_x_2192_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2222_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; 
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
v___x_2208_ = lean_apply_7(v_head_2203_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, lean_box(0));
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 1, v_x_2193_);
lean_ctor_set(v___x_2206_, 0, v_a_2209_);
v___x_2211_ = v___x_2206_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2209_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_x_2193_);
v___x_2211_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
v_x_2192_ = v_tail_2204_;
v_x_2193_ = v___x_2211_;
goto _start;
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_del_object(v___x_2206_);
lean_dec(v_tail_2204_);
lean_dec(v_x_2193_);
v_a_2214_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2208_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2208_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2192_ = stack[0].m_obj;
lean_object* v_x_2193_ = stack[1].m_obj;
lean_object* v___y_2194_ = stack[2].m_obj;
lean_object* v___y_2195_ = stack[3].m_obj;
lean_object* v___y_2196_ = stack[4].m_obj;
lean_object* v___y_2197_ = stack[5].m_obj;
lean_object* v___y_2198_ = stack[6].m_obj;
lean_object* v___y_2199_ = stack[7].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2192_, v_x_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2224_, v_x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2233_;
}
}
lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2234_, lean_object* v_cfg_2235_, lean_object* v_lemmas_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
v___x_2244_ = lean_apply_8(v_ctx_2234_, v_cfg_2235_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, lean_box(0));
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2246_ = lean_box(0);
v___x_2247_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2236_, v___x_2246_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2256_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2256_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2256_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2252_ = l_List_appendTR___redArg(v_a_2245_, v_a_2248_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2252_);
v___x_2254_ = v___x_2250_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
lean_dec(v_a_2245_);
return v___x_2247_;
}
}
else
{
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v_lemmas_2236_);
return v___x_2244_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2234_ = stack[0].m_obj;
lean_object* v_cfg_2235_ = stack[1].m_obj;
lean_object* v_lemmas_2236_ = stack[2].m_obj;
lean_object* v___y_2237_ = stack[3].m_obj;
lean_object* v___y_2238_ = stack[4].m_obj;
lean_object* v___y_2239_ = stack[5].m_obj;
lean_object* v___y_2240_ = stack[6].m_obj;
lean_object* v___y_2241_ = stack[7].m_obj;
lean_object* v___y_2242_ = stack[8].m_obj;
lean_object* v_res_2257_;
v_res_2257_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2234_, v_cfg_2235_, v_lemmas_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
stack->m_obj
 = v_res_2257_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2258_, lean_object* v_cfg_2259_, lean_object* v_lemmas_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2258_, v_cfg_2259_, v_lemmas_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v_res_2268_;
}
}
uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2269_){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = 0;
return v___x_2270_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2269_ = stack[0].m_obj;
uint8_t v_res_2271_;
v_res_2271_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2269_);
stack->m_num = v_res_2271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2272_){
_start:
{
uint8_t v_res_2273_; lean_object* v_r_2274_; 
v_res_2273_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2272_);
lean_dec(v_x_2272_);
v_r_2274_ = lean_box(v_res_2273_);
return v_r_2274_;
}
}
lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2275_, lean_object* v___x_2276_, lean_object* v___x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2275_, v___x_2276_, v___x_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_fst_2288_; lean_object* v___x_2290_; 
v_fst_2288_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_fst_2288_);
lean_dec(v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_fst_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_fst_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2283_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2283_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2275_ = stack[0].m_obj;
lean_object* v___x_2276_ = stack[1].m_obj;
lean_object* v___x_2277_ = stack[2].m_obj;
lean_object* v___y_2278_ = stack[3].m_obj;
lean_object* v___y_2279_ = stack[4].m_obj;
lean_object* v___y_2280_ = stack[5].m_obj;
lean_object* v___y_2281_ = stack[6].m_obj;
lean_object* v_res_2301_;
v_res_2301_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2275_, v___x_2276_, v___x_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
stack->m_obj
 = v_res_2301_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2302_, lean_object* v___x_2303_, lean_object* v___x_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2302_, v___x_2303_, v___x_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2310_;
}
}
lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2325_, lean_object* v_g_2326_, lean_object* v_lemmas_2327_, lean_object* v_ctx_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; 
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2334_, 0, v_ctx_2328_);
lean_closure_set(v___f_2334_, 1, v_cfg_2325_);
lean_closure_set(v___f_2334_, 2, v_lemmas_2327_);
v___x_2335_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2336_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2337_, 0, v___f_2334_);
lean_closure_set(v___f_2337_, 1, v___x_2335_);
lean_closure_set(v___f_2337_, 2, v___x_2336_);
v___x_2338_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2326_, v___f_2337_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_2338_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_elabContextLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2325_ = stack[0].m_obj;
lean_object* v_g_2326_ = stack[1].m_obj;
lean_object* v_lemmas_2327_ = stack[2].m_obj;
lean_object* v_ctx_2328_ = stack[3].m_obj;
lean_object* v_a_2329_ = stack[4].m_obj;
lean_object* v_a_2330_ = stack[5].m_obj;
lean_object* v_a_2331_ = stack[6].m_obj;
lean_object* v_a_2332_ = stack[7].m_obj;
lean_object* v_res_2339_;
v_res_2339_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2325_, v_g_2326_, v_lemmas_2327_, v_ctx_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
stack->m_obj
 = v_res_2339_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2340_, lean_object* v_g_2341_, lean_object* v_lemmas_2342_, lean_object* v_ctx_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2340_, v_g_2341_, v_lemmas_2342_, v_ctx_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2349_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2350_, lean_object* v_lemmas_2351_, lean_object* v_ctx_2352_, lean_object* v_g_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; 
lean_inc(v_g_2353_);
lean_inc_ref(v_cfg_2350_);
v___x_2359_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2350_, v_g_2353_, v_lemmas_2351_, v_ctx_2352_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_toApplyRulesConfig_2360_; lean_object* v_a_2361_; lean_object* v_toApplyConfig_2362_; uint8_t v_transparency_2363_; lean_object* v___x_2364_; 
v_toApplyRulesConfig_2360_ = lean_ctor_get(v_cfg_2350_, 0);
lean_inc_ref(v_toApplyRulesConfig_2360_);
lean_dec_ref(v_cfg_2350_);
v_a_2361_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2359_, 1);
v_toApplyConfig_2362_ = lean_ctor_get(v_toApplyRulesConfig_2360_, 1);
lean_inc_ref(v_toApplyConfig_2362_);
v_transparency_2363_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2360_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2360_);
v___x_2364_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2362_, v_transparency_2363_, v_a_2361_, v_g_2353_, v_a_2355_, v_a_2357_);
return v___x_2364_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_g_2353_);
lean_dec_ref(v_cfg_2350_);
v_a_2365_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2359_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2359_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2350_ = stack[0].m_obj;
lean_object* v_lemmas_2351_ = stack[1].m_obj;
lean_object* v_ctx_2352_ = stack[2].m_obj;
lean_object* v_g_2353_ = stack[3].m_obj;
lean_object* v_a_2354_ = stack[4].m_obj;
lean_object* v_a_2355_ = stack[5].m_obj;
lean_object* v_a_2356_ = stack[6].m_obj;
lean_object* v_a_2357_ = stack[7].m_obj;
lean_object* v_res_2373_;
v_res_2373_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2350_, v_lemmas_2351_, v_ctx_2352_, v_g_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
stack->m_obj
 = v_res_2373_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2374_, lean_object* v_lemmas_2375_, lean_object* v_ctx_2376_, lean_object* v_g_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2374_, v_lemmas_2375_, v_ctx_2376_, v_g_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2383_;
}
}
lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2384_, lean_object* v_lemmas_2385_, lean_object* v_ctx_2386_, lean_object* v_g_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; 
lean_inc(v_g_2387_);
lean_inc_ref(v_cfg_2384_);
v___x_2393_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2384_, v_g_2387_, v_lemmas_2385_, v_ctx_2386_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_toApplyRulesConfig_2394_; lean_object* v_a_2395_; lean_object* v_toApplyConfig_2396_; uint8_t v_transparency_2397_; lean_object* v___x_2398_; 
v_toApplyRulesConfig_2394_ = lean_ctor_get(v_cfg_2384_, 0);
lean_inc_ref(v_toApplyRulesConfig_2394_);
lean_dec_ref(v_cfg_2384_);
v_a_2395_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2393_, 1);
v_toApplyConfig_2396_ = lean_ctor_get(v_toApplyRulesConfig_2394_, 1);
lean_inc_ref(v_toApplyConfig_2396_);
v_transparency_2397_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2394_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2394_);
v___x_2398_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2396_, v_transparency_2397_, v_a_2395_, v_g_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
return v___x_2398_;
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_g_2387_);
lean_dec_ref(v_cfg_2384_);
v_a_2399_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2393_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2393_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_applyFirstLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2384_ = stack[0].m_obj;
lean_object* v_lemmas_2385_ = stack[1].m_obj;
lean_object* v_ctx_2386_ = stack[2].m_obj;
lean_object* v_g_2387_ = stack[3].m_obj;
lean_object* v_a_2388_ = stack[4].m_obj;
lean_object* v_a_2389_ = stack[5].m_obj;
lean_object* v_a_2390_ = stack[6].m_obj;
lean_object* v_a_2391_ = stack[7].m_obj;
lean_object* v_res_2407_;
v_res_2407_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2384_, v_lemmas_2385_, v_ctx_2386_, v_g_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
stack->m_obj
 = v_res_2407_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2408_, lean_object* v_lemmas_2409_, lean_object* v_ctx_2410_, lean_object* v_g_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2408_, v_lemmas_2409_, v_ctx_2410_, v_g_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2418_, lean_object* v_i_2419_, lean_object* v_k_2420_){
_start:
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = lean_array_get_size(v_keys_2418_);
v___x_2422_ = lean_nat_dec_lt(v_i_2419_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_dec(v_i_2419_);
return v___x_2422_;
}
else
{
lean_object* v_k_x27_2423_; uint8_t v___x_2424_; 
v_k_x27_2423_ = lean_array_fget_borrowed(v_keys_2418_, v_i_2419_);
v___x_2424_ = l_Lean_instBEqMVarId_beq(v_k_2420_, v_k_x27_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_add(v_i_2419_, v___x_2425_);
lean_dec(v_i_2419_);
v_i_2419_ = v___x_2426_;
goto _start;
}
else
{
lean_dec(v_i_2419_);
return v___x_2422_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2418_ = stack[0].m_obj;
lean_object* v_i_2419_ = stack[1].m_obj;
lean_object* v_k_2420_ = stack[2].m_obj;
uint8_t v_res_2428_;
v_res_2428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2418_, v_i_2419_, v_k_2420_);
stack->m_num = v_res_2428_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2429_, lean_object* v_i_2430_, lean_object* v_k_2431_){
_start:
{
uint8_t v_res_2432_; lean_object* v_r_2433_; 
v_res_2432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2429_, v_i_2430_, v_k_2431_);
lean_dec(v_k_2431_);
lean_dec_ref(v_keys_2429_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2434_, size_t v_x_2435_, lean_object* v_x_2436_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
lean_object* v_es_2437_; lean_object* v___x_2438_; size_t v___x_2439_; size_t v___x_2440_; lean_object* v_j_2441_; lean_object* v___x_2442_; 
v_es_2437_ = lean_ctor_get(v_x_2434_, 0);
v___x_2438_ = lean_box(2);
v___x_2439_ = ((size_t)31ULL);
v___x_2440_ = lean_usize_land(v_x_2435_, v___x_2439_);
v_j_2441_ = lean_usize_to_nat(v___x_2440_);
v___x_2442_ = lean_array_get_borrowed(v___x_2438_, v_es_2437_, v_j_2441_);
lean_dec(v_j_2441_);
switch(lean_obj_tag(v___x_2442_))
{
case 0:
{
lean_object* v_key_2443_; uint8_t v___x_2444_; 
v_key_2443_ = lean_ctor_get(v___x_2442_, 0);
v___x_2444_ = l_Lean_instBEqMVarId_beq(v_x_2436_, v_key_2443_);
return v___x_2444_;
}
case 1:
{
lean_object* v_node_2445_; size_t v___x_2446_; size_t v___x_2447_; 
v_node_2445_ = lean_ctor_get(v___x_2442_, 0);
v___x_2446_ = ((size_t)5ULL);
v___x_2447_ = lean_usize_shift_right(v_x_2435_, v___x_2446_);
v_x_2434_ = v_node_2445_;
v_x_2435_ = v___x_2447_;
goto _start;
}
default: 
{
uint8_t v___x_2449_; 
v___x_2449_ = 0;
return v___x_2449_;
}
}
}
else
{
lean_object* v_ks_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_ks_2450_ = lean_ctor_get(v_x_2434_, 0);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2450_, v___x_2451_, v_x_2436_);
return v___x_2452_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2434_ = stack[0].m_obj;
size_t v_x_2435_ = stack[1].m_num;
lean_object* v_x_2436_ = stack[2].m_obj;
uint8_t v_res_2453_;
v_res_2453_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2434_, v_x_2435_, v_x_2436_);
stack->m_num = v_res_2453_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2454_, lean_object* v_x_2455_, lean_object* v_x_2456_){
_start:
{
size_t v_x_1994__boxed_2457_; uint8_t v_res_2458_; lean_object* v_r_2459_; 
v_x_1994__boxed_2457_ = lean_unbox_usize(v_x_2455_);
lean_dec(v_x_2455_);
v_res_2458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2454_, v_x_1994__boxed_2457_, v_x_2456_);
lean_dec(v_x_2456_);
lean_dec_ref(v_x_2454_);
v_r_2459_ = lean_box(v_res_2458_);
return v_r_2459_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2460_, lean_object* v_x_2461_){
_start:
{
uint64_t v___x_2462_; size_t v___x_2463_; uint8_t v___x_2464_; 
v___x_2462_ = l_Lean_instHashableMVarId_hash(v_x_2461_);
v___x_2463_ = lean_uint64_to_usize(v___x_2462_);
v___x_2464_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2460_, v___x_2463_, v_x_2461_);
return v___x_2464_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2460_ = stack[0].m_obj;
lean_object* v_x_2461_ = stack[1].m_obj;
uint8_t v_res_2465_;
v_res_2465_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2460_, v_x_2461_);
stack->m_num = v_res_2465_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
uint8_t v_res_2468_; lean_object* v_r_2469_; 
v_res_2468_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2466_, v_x_2467_);
lean_dec(v_x_2467_);
lean_dec_ref(v_x_2466_);
v_r_2469_ = lean_box(v_res_2468_);
return v_r_2469_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v_mctx_2474_; lean_object* v_eAssignment_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2473_ = lean_st_ref_get(v___y_2471_);
v_mctx_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_ref(v_mctx_2474_);
lean_dec(v___x_2473_);
v_eAssignment_2475_ = lean_ctor_get(v_mctx_2474_, 8);
lean_inc_ref(v_eAssignment_2475_);
lean_dec_ref(v_mctx_2474_);
v___x_2476_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2475_, v_mvarId_2470_);
lean_dec_ref(v_eAssignment_2475_);
v___x_2477_ = lean_box(v___x_2476_);
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2470_ = stack[0].m_obj;
lean_object* v___y_2471_ = stack[1].m_obj;
lean_object* v_res_2479_;
v_res_2479_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2470_, v___y_2471_);
stack->m_obj
 = v_res_2479_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec(v_mvarId_2480_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2484_, lean_object* v_x_2485_){
_start:
{
if (lean_obj_tag(v_x_2485_) == 0)
{
return v_x_2484_;
}
else
{
lean_object* v_head_2486_; lean_object* v_tail_2487_; lean_object* v___x_2488_; 
v_head_2486_ = lean_ctor_get(v_x_2485_, 0);
lean_inc(v_head_2486_);
v_tail_2487_ = lean_ctor_get(v_x_2485_, 1);
lean_inc(v_tail_2487_);
lean_dec_ref_known(v_x_2485_, 2);
v___x_2488_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2484_, v_head_2486_);
v_x_2484_ = v___x_2488_;
v_x_2485_ = v_tail_2487_;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2490_, lean_object* v_a_2491_, uint8_t v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
if (lean_obj_tag(v_a_2493_) == 0)
{
if (lean_obj_tag(v_a_2494_) == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_a_2491_);
lean_dec_ref(v_f_2490_);
v___x_2501_ = lean_box(v_a_2492_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v_a_2495_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
else
{
lean_object* v_head_2504_; lean_object* v_tail_2505_; 
v_head_2504_ = lean_ctor_get(v_a_2494_, 0);
lean_inc(v_head_2504_);
v_tail_2505_ = lean_ctor_get(v_a_2494_, 1);
lean_inc(v_tail_2505_);
lean_dec_ref_known(v_a_2494_, 2);
v_a_2493_ = v_head_2504_;
v_a_2494_ = v_tail_2505_;
goto _start;
}
}
else
{
lean_object* v_head_2507_; lean_object* v_tail_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2551_; 
v_head_2507_ = lean_ctor_get(v_a_2493_, 0);
v_tail_2508_ = lean_ctor_get(v_a_2493_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_a_2493_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2510_ = v_a_2493_;
v_isShared_2511_ = v_isSharedCheck_2551_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_tail_2508_);
lean_inc(v_head_2507_);
lean_dec(v_a_2493_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2551_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2550_; 
v___x_2512_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2507_, v___y_2497_);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2550_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2550_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_unbox(v_a_2513_);
lean_dec(v_a_2513_);
if (v___x_2517_ == 0)
{
lean_object* v_zero_2518_; uint8_t v_isZero_2519_; 
v_zero_2518_ = lean_unsigned_to_nat(0u);
v_isZero_2519_ = lean_nat_dec_eq(v_a_2491_, v_zero_2518_);
if (v_isZero_2519_ == 1)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
lean_del_object(v___x_2510_);
lean_dec(v_a_2491_);
lean_dec_ref(v_f_2490_);
v___x_2520_ = lean_array_push(v_a_2495_, v_head_2507_);
v___x_2521_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2520_, v_tail_2508_);
v___x_2522_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2521_, v_a_2494_);
v___x_2523_ = lean_box(v_a_2492_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2522_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2524_);
v___x_2526_ = v___x_2515_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
else
{
lean_object* v_one_2528_; lean_object* v_n_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_del_object(v___x_2515_);
v_one_2528_ = lean_unsigned_to_nat(1u);
v_n_2529_ = lean_nat_sub(v_a_2491_, v_one_2528_);
lean_dec(v_a_2491_);
v___x_2530_ = 1;
lean_inc_ref(v_f_2490_);
lean_inc(v_head_2507_);
v___x_2531_ = lean_apply_1(v_f_2490_, v_head_2507_);
v___x_2532_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2531_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
if (lean_obj_tag(v_a_2533_) == 0)
{
lean_object* v___x_2534_; 
lean_del_object(v___x_2510_);
v___x_2534_ = lean_array_push(v_a_2495_, v_head_2507_);
v_a_2491_ = v_n_2529_;
v_a_2493_ = v_tail_2508_;
v_a_2495_ = v___x_2534_;
goto _start;
}
else
{
lean_object* v_val_2536_; lean_object* v___x_2538_; 
lean_dec(v_head_2507_);
v_val_2536_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_a_2533_, 1);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v_a_2494_);
lean_ctor_set(v___x_2510_, 0, v_tail_2508_);
v___x_2538_ = v___x_2510_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_tail_2508_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_a_2494_);
v___x_2538_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
v_a_2491_ = v_n_2529_;
v_a_2492_ = v___x_2530_;
v_a_2493_ = v_val_2536_;
v_a_2494_ = v___x_2538_;
goto _start;
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_n_2529_);
lean_del_object(v___x_2510_);
lean_dec(v_tail_2508_);
lean_dec(v_head_2507_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_f_2490_);
v_a_2541_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2532_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2532_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
else
{
lean_del_object(v___x_2515_);
lean_del_object(v___x_2510_);
lean_dec(v_head_2507_);
v_a_2493_ = v_tail_2508_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2490_ = stack[0].m_obj;
lean_object* v_a_2491_ = stack[1].m_obj;
uint8_t v_a_2492_ = stack[2].m_num;
lean_object* v_a_2493_ = stack[3].m_obj;
lean_object* v_a_2494_ = stack[4].m_obj;
lean_object* v_a_2495_ = stack[5].m_obj;
lean_object* v___y_2496_ = stack[6].m_obj;
lean_object* v___y_2497_ = stack[7].m_obj;
lean_object* v___y_2498_ = stack[8].m_obj;
lean_object* v___y_2499_ = stack[9].m_obj;
lean_object* v_res_2552_;
v_res_2552_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
stack->m_obj
 = v_res_2552_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v_a_2115__boxed_2564_; lean_object* v_res_2565_; 
v_a_2115__boxed_2564_ = lean_unbox(v_a_2555_);
v_res_2565_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2553_, v_a_2554_, v_a_2115__boxed_2564_, v_a_2556_, v_a_2557_, v_a_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2565_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2566_, size_t v_i_2567_, size_t v_stop_2568_, lean_object* v_b_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_a_2576_; uint8_t v___x_2580_; 
v___x_2580_ = lean_usize_dec_eq(v_i_2567_, v_stop_2568_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2584_; 
v___x_2581_ = lean_array_uget_borrowed(v_as_2566_, v_i_2567_);
v___x_2584_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2581_, v___y_2571_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; uint8_t v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = lean_unbox(v_a_2585_);
lean_dec(v_a_2585_);
if (v___x_2586_ == 0)
{
goto v___jp_2582_;
}
else
{
v_a_2576_ = v_b_2569_;
goto v___jp_2575_;
}
}
else
{
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2587_; uint8_t v___x_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2588_ = lean_unbox(v_a_2587_);
lean_dec(v_a_2587_);
if (v___x_2588_ == 0)
{
v_a_2576_ = v_b_2569_;
goto v___jp_2575_;
}
else
{
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_b_2569_);
v_a_2589_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2584_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2584_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
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
v___jp_2582_:
{
lean_object* v___x_2583_; 
lean_inc(v___x_2581_);
v___x_2583_ = lean_array_push(v_b_2569_, v___x_2581_);
v_a_2576_ = v___x_2583_;
goto v___jp_2575_;
}
}
else
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_b_2569_);
return v___x_2597_;
}
v___jp_2575_:
{
size_t v___x_2577_; size_t v___x_2578_; 
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_add(v_i_2567_, v___x_2577_);
v_i_2567_ = v___x_2578_;
v_b_2569_ = v_a_2576_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2566_ = stack[0].m_obj;
size_t v_i_2567_ = stack[1].m_num;
size_t v_stop_2568_ = stack[2].m_num;
lean_object* v_b_2569_ = stack[3].m_obj;
lean_object* v___y_2570_ = stack[4].m_obj;
lean_object* v___y_2571_ = stack[5].m_obj;
lean_object* v___y_2572_ = stack[6].m_obj;
lean_object* v___y_2573_ = stack[7].m_obj;
lean_object* v_res_2598_;
v_res_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2566_, v_i_2567_, v_stop_2568_, v_b_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
stack->m_obj
 = v_res_2598_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2599_, lean_object* v_i_2600_, lean_object* v_stop_2601_, lean_object* v_b_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
size_t v_i_boxed_2608_; size_t v_stop_boxed_2609_; lean_object* v_res_2610_; 
v_i_boxed_2608_ = lean_unbox_usize(v_i_2600_);
lean_dec(v_i_2600_);
v_stop_boxed_2609_ = lean_unbox_usize(v_stop_2601_);
lean_dec(v_stop_2601_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2599_, v_i_boxed_2608_, v_stop_boxed_2609_, v_b_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_as_2599_);
return v_res_2610_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2614_ = lean_array_to_list(v___x_2613_);
return v___x_2614_;
}
}
lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2615_, lean_object* v_goals_2616_, lean_object* v_maxIters_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2623_ = 0;
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2627_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2615_, v_maxIters_2617_, v___x_2623_, v_goals_2616_, v___x_2624_, v___x_2626_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2670_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2670_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2670_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2669_; 
v_fst_2632_ = lean_ctor_get(v_a_2628_, 0);
v_snd_2633_ = lean_ctor_get(v_a_2628_, 1);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_a_2628_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2635_ = v_a_2628_;
v_isShared_2636_ = v_isSharedCheck_2669_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_snd_2633_);
lean_inc(v_fst_2632_);
lean_dec(v_a_2628_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2669_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = lean_array_get_size(v_snd_2633_);
v___x_2638_ = lean_nat_dec_lt(v___x_2625_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
lean_dec(v_snd_2633_);
v___x_2639_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2639_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_fst_2632_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2643_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2641_);
v___x_2643_ = v___x_2630_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
lean_del_object(v___x_2630_);
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2637_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2633_, v___x_2646_, v___x_2647_, v___x_2626_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v_snd_2633_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2660_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2660_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2660_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = lean_array_to_list(v_a_2649_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2653_);
v___x_2655_ = v___x_2635_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_fst_2632_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2657_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2655_);
v___x_2657_ = v___x_2651_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_del_object(v___x_2635_);
lean_dec(v_fst_2632_);
v_a_2661_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2648_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2648_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
v_a_2671_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2627_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2627_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2615_ = stack[0].m_obj;
lean_object* v_goals_2616_ = stack[1].m_obj;
lean_object* v_maxIters_2617_ = stack[2].m_obj;
lean_object* v___y_2618_ = stack[3].m_obj;
lean_object* v___y_2619_ = stack[4].m_obj;
lean_object* v___y_2620_ = stack[5].m_obj;
lean_object* v___y_2621_ = stack[6].m_obj;
lean_object* v_res_2679_;
v_res_2679_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2615_, v_goals_2616_, v_maxIters_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
stack->m_obj
 = v_res_2679_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2680_, lean_object* v_goals_2681_, lean_object* v_maxIters_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2680_, v_goals_2681_, v_maxIters_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2688_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2691_ = l_Lean_stringToMessageData(v___x_2690_);
return v___x_2691_;
}
}
lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2692_, lean_object* v_goals_2693_, lean_object* v_maxIters_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2692_, v_goals_2693_, v_maxIters_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2713_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2713_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2713_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v_fst_2705_; uint8_t v___x_2706_; 
v_fst_2705_ = lean_ctor_get(v_a_2701_, 0);
v___x_2706_ = lean_unbox(v_fst_2705_);
if (v___x_2706_ == 1)
{
lean_object* v_snd_2707_; lean_object* v___x_2709_; 
v_snd_2707_ = lean_ctor_get(v_a_2701_, 1);
lean_inc(v_snd_2707_);
lean_dec(v_a_2701_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v_snd_2707_);
v___x_2709_ = v___x_2703_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_snd_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_del_object(v___x_2703_);
lean_dec(v_a_2701_);
v___x_2711_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2712_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2711_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2712_;
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
v_a_2714_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2700_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2700_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2692_ = stack[0].m_obj;
lean_object* v_goals_2693_ = stack[1].m_obj;
lean_object* v_maxIters_2694_ = stack[2].m_obj;
lean_object* v___y_2695_ = stack[3].m_obj;
lean_object* v___y_2696_ = stack[4].m_obj;
lean_object* v___y_2697_ = stack[5].m_obj;
lean_object* v___y_2698_ = stack[6].m_obj;
lean_object* v_res_2722_;
v_res_2722_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2692_, v_goals_2693_, v_maxIters_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
stack->m_obj
 = v_res_2722_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2723_, lean_object* v_goals_2724_, lean_object* v_maxIters_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2723_, v_goals_2724_, v_maxIters_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
return v_res_2731_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2732_, lean_object* v_ctx_2733_, lean_object* v_cfg_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
uint8_t v_backtracking_2741_; 
v_backtracking_2741_ = lean_ctor_get_uint8(v_cfg_2734_, sizeof(void*)*1);
if (v_backtracking_2741_ == 0)
{
lean_object* v_toApplyRulesConfig_2742_; lean_object* v_toBacktrackConfig_2743_; lean_object* v_maxDepth_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_toApplyRulesConfig_2742_ = lean_ctor_get(v_cfg_2734_, 0);
v_toBacktrackConfig_2743_ = lean_ctor_get(v_toApplyRulesConfig_2742_, 0);
v_maxDepth_2744_ = lean_ctor_get(v_toBacktrackConfig_2743_, 0);
lean_inc(v_maxDepth_2744_);
v___x_2745_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2745_, 0, v_cfg_2734_);
lean_closure_set(v___x_2745_, 1, v_lemmas_2732_);
lean_closure_set(v___x_2745_, 2, v_ctx_2733_);
v___x_2746_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2745_, v_a_2735_, v_maxDepth_2744_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
return v___x_2746_;
}
else
{
lean_object* v_toApplyRulesConfig_2747_; lean_object* v_toBacktrackConfig_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_toApplyRulesConfig_2747_ = lean_ctor_get(v_cfg_2734_, 0);
v_toBacktrackConfig_2748_ = lean_ctor_get(v_toApplyRulesConfig_2747_, 0);
lean_inc_ref(v_toBacktrackConfig_2748_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2750_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2750_, 0, v_cfg_2734_);
lean_closure_set(v___x_2750_, 1, v_lemmas_2732_);
lean_closure_set(v___x_2750_, 2, v_ctx_2733_);
v___x_2751_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2748_, v___x_2749_, v___x_2750_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
return v___x_2751_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_lemmas_2732_ = stack[0].m_obj;
lean_object* v_ctx_2733_ = stack[1].m_obj;
lean_object* v_cfg_2734_ = stack[2].m_obj;
lean_object* v_a_2735_ = stack[3].m_obj;
lean_object* v_a_2736_ = stack[4].m_obj;
lean_object* v_a_2737_ = stack[5].m_obj;
lean_object* v_a_2738_ = stack[6].m_obj;
lean_object* v_a_2739_ = stack[7].m_obj;
lean_object* v_res_2752_;
v_res_2752_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2732_, v_ctx_2733_, v_cfg_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
stack->m_obj
 = v_res_2752_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2753_, lean_object* v_ctx_2754_, lean_object* v_cfg_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2753_, v_ctx_2754_, v_cfg_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
return v_res_2762_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2763_, v___y_2765_);
return v___x_2769_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2763_ = stack[0].m_obj;
lean_object* v___y_2764_ = stack[1].m_obj;
lean_object* v___y_2765_ = stack[2].m_obj;
lean_object* v___y_2766_ = stack[3].m_obj;
lean_object* v___y_2767_ = stack[4].m_obj;
lean_object* v_res_2770_;
v_res_2770_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
stack->m_obj
 = v_res_2770_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v_mvarId_2771_);
return v_res_2777_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2779_, v_x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2779_ = stack[1].m_obj;
lean_object* v_x_2780_ = stack[2].m_obj;
uint8_t v_res_2782_;
v_res_2782_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_x_2779_, v_x_2780_);
stack->m_num = v_res_2782_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
uint8_t v_res_2786_; lean_object* v_r_2787_; 
v_res_2786_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2783_, v_x_2784_, v_x_2785_);
lean_dec(v_x_2785_);
lean_dec_ref(v_x_2784_);
v_r_2787_ = lean_box(v_res_2786_);
return v_r_2787_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2788_, lean_object* v_x_2789_, size_t v_x_2790_, lean_object* v_x_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2789_, v_x_2790_, v_x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2789_ = stack[1].m_obj;
size_t v_x_2790_ = stack[2].m_num;
lean_object* v_x_2791_ = stack[3].m_obj;
uint8_t v_res_2793_;
v_res_2793_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_box(0), v_x_2789_, v_x_2790_, v_x_2791_);
stack->m_num = v_res_2793_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_){
_start:
{
size_t v_x_2792__boxed_2798_; uint8_t v_res_2799_; lean_object* v_r_2800_; 
v_x_2792__boxed_2798_ = lean_unbox_usize(v_x_2796_);
lean_dec(v_x_2796_);
v_res_2799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2794_, v_x_2795_, v_x_2792__boxed_2798_, v_x_2797_);
lean_dec(v_x_2797_);
lean_dec_ref(v_x_2795_);
v_r_2800_ = lean_box(v_res_2799_);
return v_r_2800_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2801_, lean_object* v_keys_2802_, lean_object* v_vals_2803_, lean_object* v_heq_2804_, lean_object* v_i_2805_, lean_object* v_k_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2802_, v_i_2805_, v_k_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2802_ = stack[1].m_obj;
lean_object* v_vals_2803_ = stack[2].m_obj;
lean_object* v_i_2805_ = stack[4].m_obj;
lean_object* v_k_2806_ = stack[5].m_obj;
uint8_t v_res_2808_;
v_res_2808_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_box(0), v_keys_2802_, v_vals_2803_, lean_box(0), v_i_2805_, v_k_2806_);
stack->m_num = v_res_2808_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2809_, lean_object* v_keys_2810_, lean_object* v_vals_2811_, lean_object* v_heq_2812_, lean_object* v_i_2813_, lean_object* v_k_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2809_, v_keys_2810_, v_vals_2811_, v_heq_2812_, v_i_2813_, v_k_2814_);
lean_dec(v_k_2814_);
lean_dec_ref(v_vals_2811_);
lean_dec_ref(v_keys_2810_);
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_solveByElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2820_ = stack[0].m_obj;
lean_object* v___y_2821_ = stack[1].m_obj;
lean_object* v___y_2822_ = stack[2].m_obj;
lean_object* v___y_2823_ = stack[3].m_obj;
lean_object* v___y_2824_ = stack[4].m_obj;
lean_object* v_res_2828_;
v_res_2828_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
stack->m_obj
 = v_res_2828_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v_x_2829_);
return v_res_2835_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2838_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2839_ = l_Lean_Name_append(v___x_2838_, v___x_2837_);
return v___x_2839_;
}
}
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2840_, lean_object* v_lemmas_2841_, lean_object* v_ctx_2842_, lean_object* v_goals_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___f_2849_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; uint8_t v___y_2854_; lean_object* v___y_2855_; uint8_t v___y_2856_; lean_object* v___y_2857_; lean_object* v_a_2858_; lean_object* v___y_2868_; uint8_t v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v_a_2875_; lean_object* v___y_2878_; lean_object* v___y_2879_; uint8_t v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; uint8_t v___y_2883_; lean_object* v___y_2884_; lean_object* v_a_2885_; uint8_t v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; uint8_t v___y_2904_; lean_object* v_a_2905_; lean_object* v_cfg_2907_; lean_object* v___x_2908_; 
v___f_2849_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v_cfg_2907_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2840_);
lean_inc(v_goals_2843_);
lean_inc_ref(v_cfg_2907_);
lean_inc_ref(v_ctx_2842_);
lean_inc(v_lemmas_2841_);
v___x_2908_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2841_, v_ctx_2842_, v_cfg_2907_, v_goals_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_dec_ref(v_cfg_2907_);
lean_dec(v_goals_2843_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
return v___x_2908_;
}
else
{
lean_object* v_a_2909_; uint8_t v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; uint8_t v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; uint8_t v___y_2953_; uint8_t v___x_3007_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v___x_3007_ = l_Lean_Exception_isInterrupt(v_a_2909_);
if (v___x_3007_ == 0)
{
uint8_t v___x_3008_; 
lean_inc(v_a_2909_);
v___x_3008_ = l_Lean_Exception_isRuntime(v_a_2909_);
v___y_2953_ = v___x_3008_;
goto v___jp_2952_;
}
else
{
v___y_2953_ = v___x_3007_;
goto v___jp_2952_;
}
v___jp_2910_:
{
lean_object* v___x_2918_; lean_object* v_a_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2918_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2847_);
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2918_);
v___x_2920_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2921_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2916_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_io_mono_nanos_now();
v___x_2923_ = l_Lean_MVarId_exfalso(v___y_2914_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2924_);
lean_ctor_set(v___x_2925_, 1, v___y_2917_);
v___x_2926_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2841_, v_ctx_2842_, v_cfg_2907_, v___x_2925_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 1);
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
v___y_2878_ = v_a_2919_;
v___y_2879_ = v___y_2912_;
v___y_2880_ = v___y_2911_;
v___y_2881_ = v___y_2913_;
v___y_2882_ = v___x_2922_;
v___y_2883_ = v___y_2915_;
v___y_2884_ = v___y_2916_;
v_a_2885_ = v___x_2932_;
goto v___jp_2877_;
}
}
}
else
{
lean_object* v_a_2935_; 
v_a_2935_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2926_, 1);
v___y_2898_ = v___y_2911_;
v___y_2899_ = v___y_2912_;
v___y_2900_ = v_a_2919_;
v___y_2901_ = v___y_2913_;
v___y_2902_ = v___x_2922_;
v___y_2903_ = v___y_2916_;
v___y_2904_ = v___y_2915_;
v_a_2905_ = v_a_2935_;
goto v___jp_2897_;
}
}
else
{
lean_object* v_a_2936_; 
lean_dec(v___y_2917_);
lean_dec_ref(v_cfg_2907_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
v_a_2936_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2923_, 1);
v___y_2898_ = v___y_2911_;
v___y_2899_ = v___y_2912_;
v___y_2900_ = v_a_2919_;
v___y_2901_ = v___y_2913_;
v___y_2902_ = v___x_2922_;
v___y_2903_ = v___y_2916_;
v___y_2904_ = v___y_2915_;
v_a_2905_ = v_a_2936_;
goto v___jp_2897_;
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_io_get_num_heartbeats();
v___x_2938_ = l_Lean_MVarId_exfalso(v___y_2914_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_a_2939_);
lean_ctor_set(v___x_2940_, 1, v___y_2917_);
v___x_2941_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2841_, v_ctx_2842_, v_cfg_2907_, v___x_2940_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 1);
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
v___y_2851_ = v___x_2937_;
v___y_2852_ = v_a_2919_;
v___y_2853_ = v___y_2912_;
v___y_2854_ = v___y_2911_;
v___y_2855_ = v___y_2913_;
v___y_2856_ = v___y_2915_;
v___y_2857_ = v___y_2916_;
v_a_2858_ = v___x_2947_;
goto v___jp_2850_;
}
}
}
else
{
lean_object* v_a_2950_; 
v_a_2950_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2941_, 1);
v___y_2868_ = v___x_2937_;
v___y_2869_ = v___y_2911_;
v___y_2870_ = v___y_2912_;
v___y_2871_ = v_a_2919_;
v___y_2872_ = v___y_2913_;
v___y_2873_ = v___y_2916_;
v___y_2874_ = v___y_2915_;
v_a_2875_ = v_a_2950_;
goto v___jp_2867_;
}
}
else
{
lean_object* v_a_2951_; 
lean_dec(v___y_2917_);
lean_dec_ref(v_cfg_2907_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
v_a_2951_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2938_, 1);
v___y_2868_ = v___x_2937_;
v___y_2869_ = v___y_2911_;
v___y_2870_ = v___y_2912_;
v___y_2871_ = v_a_2919_;
v___y_2872_ = v___y_2913_;
v___y_2873_ = v___y_2916_;
v___y_2874_ = v___y_2915_;
v_a_2875_ = v_a_2951_;
goto v___jp_2867_;
}
}
}
v___jp_2952_:
{
if (v___y_2953_ == 0)
{
if (lean_obj_tag(v_goals_2843_) == 1)
{
lean_object* v_tail_2954_; 
v_tail_2954_ = lean_ctor_get(v_goals_2843_, 1);
lean_inc(v_tail_2954_);
if (lean_obj_tag(v_tail_2954_) == 0)
{
lean_object* v_toApplyRulesConfig_2955_; uint8_t v_exfalso_2956_; 
v_toApplyRulesConfig_2955_ = lean_ctor_get(v_cfg_2907_, 0);
v_exfalso_2956_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2955_, sizeof(void*)*2 + 2);
if (v_exfalso_2956_ == 1)
{
lean_object* v_toCold_2957_; lean_object* v_options_2958_; uint8_t v_hasTrace_2959_; 
lean_dec_ref_known(v___x_2908_, 1);
v_toCold_2957_ = lean_ctor_get(v_a_2846_, 0);
v_options_2958_ = lean_ctor_get(v_toCold_2957_, 2);
v_hasTrace_2959_ = lean_ctor_get_uint8(v_options_2958_, sizeof(void*)*1);
if (v_hasTrace_2959_ == 0)
{
lean_object* v_head_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2978_; 
v_head_2960_ = lean_ctor_get(v_goals_2843_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_goals_2843_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_goals_2843_, 1);
lean_dec(v_unused_2979_);
v___x_2962_ = v_goals_2843_;
v_isShared_2963_ = v_isSharedCheck_2978_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_head_2960_);
lean_dec(v_goals_2843_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2978_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_MVarId_exfalso(v_head_2960_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v_a_2965_);
v___x_2967_ = v___x_2962_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2965_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_tail_2954_);
v___x_2967_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; 
v___x_2968_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2841_, v_ctx_2842_, v_cfg_2907_, v___x_2967_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2968_;
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2962_);
lean_dec_ref(v_cfg_2907_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
v_a_2970_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2964_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2964_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
else
{
lean_object* v_head_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3005_; 
v_head_2980_ = lean_ctor_get(v_goals_2843_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_goals_2843_);
if (v_isSharedCheck_3005_ == 0)
{
lean_object* v_unused_3006_; 
v_unused_3006_ = lean_ctor_get(v_goals_2843_, 1);
lean_dec(v_unused_3006_);
v___x_2982_ = v_goals_2843_;
v_isShared_2983_ = v_isSharedCheck_3005_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_head_2980_);
lean_dec(v_goals_2843_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3005_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v_inheritedTraceOptions_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v_inheritedTraceOptions_2984_ = lean_ctor_get(v_toCold_2957_, 11);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2986_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2987_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2984_, v_options_2958_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = l_Lean_trace_profiler;
v___x_2990_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2958_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_MVarId_exfalso(v_head_2980_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_a_2992_);
v___x_2994_ = v___x_2982_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2992_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_tail_2954_);
v___x_2994_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2841_, v_ctx_2842_, v_cfg_2907_, v___x_2994_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2995_;
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_del_object(v___x_2982_);
lean_dec_ref(v_cfg_2907_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
v_a_2997_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2991_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2991_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
else
{
lean_del_object(v___x_2982_);
v___y_2911_ = v_exfalso_2956_;
v___y_2912_ = v___x_2986_;
v___y_2913_ = v___x_2985_;
v___y_2914_ = v_head_2980_;
v___y_2915_ = v___x_2988_;
v___y_2916_ = v_options_2958_;
v___y_2917_ = v_tail_2954_;
goto v___jp_2910_;
}
}
else
{
lean_del_object(v___x_2982_);
v___y_2911_ = v_exfalso_2956_;
v___y_2912_ = v___x_2986_;
v___y_2913_ = v___x_2985_;
v___y_2914_ = v_head_2980_;
v___y_2915_ = v___x_2988_;
v___y_2916_ = v_options_2958_;
v___y_2917_ = v_tail_2954_;
goto v___jp_2910_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2843_, 2);
lean_dec_ref(v_cfg_2907_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
return v___x_2908_;
}
}
else
{
lean_dec(v_tail_2954_);
lean_dec_ref_known(v_goals_2843_, 2);
lean_dec_ref(v_cfg_2907_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
return v___x_2908_;
}
}
else
{
lean_dec_ref(v_cfg_2907_);
lean_dec(v_goals_2843_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
return v___x_2908_;
}
}
else
{
lean_dec_ref(v_cfg_2907_);
lean_dec(v_goals_2843_);
lean_dec_ref(v_ctx_2842_);
lean_dec(v_lemmas_2841_);
return v___x_2908_;
}
}
}
v___jp_2850_:
{
lean_object* v___x_2859_; double v___x_2860_; double v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2859_ = lean_io_get_num_heartbeats();
v___x_2860_ = lean_float_of_nat(v___y_2851_);
v___x_2861_ = lean_float_of_nat(v___x_2859_);
v___x_2862_ = lean_box_float(v___x_2860_);
v___x_2863_ = lean_box_float(v___x_2861_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_a_2858_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
lean_inc_ref(v___y_2853_);
lean_inc(v___y_2855_);
v___x_2866_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2855_, v___y_2854_, v___y_2853_, v___y_2857_, v___y_2856_, v___y_2852_, v___f_2849_, v___x_2865_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2866_;
}
v___jp_2867_:
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_a_2875_);
v___y_2851_ = v___y_2868_;
v___y_2852_ = v___y_2871_;
v___y_2853_ = v___y_2870_;
v___y_2854_ = v___y_2869_;
v___y_2855_ = v___y_2872_;
v___y_2856_ = v___y_2874_;
v___y_2857_ = v___y_2873_;
v_a_2858_ = v___x_2876_;
goto v___jp_2850_;
}
v___jp_2877_:
{
lean_object* v___x_2886_; double v___x_2887_; double v___x_2888_; double v___x_2889_; double v___x_2890_; double v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2886_ = lean_io_mono_nanos_now();
v___x_2887_ = lean_float_of_nat(v___y_2882_);
v___x_2888_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2889_ = lean_float_div(v___x_2887_, v___x_2888_);
v___x_2890_ = lean_float_of_nat(v___x_2886_);
v___x_2891_ = lean_float_div(v___x_2890_, v___x_2888_);
v___x_2892_ = lean_box_float(v___x_2889_);
v___x_2893_ = lean_box_float(v___x_2891_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v_a_2885_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
lean_inc_ref(v___y_2879_);
lean_inc(v___y_2881_);
v___x_2896_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2881_, v___y_2880_, v___y_2879_, v___y_2884_, v___y_2883_, v___y_2878_, v___f_2849_, v___x_2895_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2896_;
}
v___jp_2897_:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_a_2905_);
v___y_2878_ = v___y_2900_;
v___y_2879_ = v___y_2899_;
v___y_2880_ = v___y_2898_;
v___y_2881_ = v___y_2901_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2904_;
v___y_2884_ = v___y_2903_;
v_a_2885_ = v___x_2906_;
goto v___jp_2877_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_solveByElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2840_ = stack[0].m_obj;
lean_object* v_lemmas_2841_ = stack[1].m_obj;
lean_object* v_ctx_2842_ = stack[2].m_obj;
lean_object* v_goals_2843_ = stack[3].m_obj;
lean_object* v_a_2844_ = stack[4].m_obj;
lean_object* v_a_2845_ = stack[5].m_obj;
lean_object* v_a_2846_ = stack[6].m_obj;
lean_object* v_a_2847_ = stack[7].m_obj;
lean_object* v_res_3009_;
v_res_3009_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2840_, v_lemmas_2841_, v_ctx_2842_, v_goals_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3010_, lean_object* v_lemmas_3011_, lean_object* v_ctx_3012_, lean_object* v_goals_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3010_, v_lemmas_3011_, v_ctx_3012_, v_goals_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
return v_res_3019_;
}
}
lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3020_, lean_object* v_x_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
if (lean_obj_tag(v_x_3020_) == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = l_List_reverse___redArg(v_x_3021_);
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
else
{
lean_object* v_head_3029_; lean_object* v_tail_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3053_; 
v_head_3029_ = lean_ctor_get(v_x_3020_, 0);
v_tail_3030_ = lean_ctor_get(v_x_3020_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_x_3020_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3032_ = v_x_3020_;
v_isShared_3033_ = v_isSharedCheck_3053_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_tail_3030_);
lean_inc(v_head_3029_);
lean_dec(v_x_3020_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3053_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_Expr_applySymm(v_head_3029_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v_x_3021_);
lean_ctor_set(v___x_3032_, 0, v_a_3035_);
v___x_3037_ = v___x_3032_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3035_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_x_3021_);
v___x_3037_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
v_x_3020_ = v_tail_3030_;
v_x_3021_ = v___x_3037_;
goto _start;
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3052_; 
lean_del_object(v___x_3032_);
v_a_3040_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3042_ = v___x_3034_;
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3034_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
uint8_t v___y_3045_; uint8_t v___x_3050_; 
v___x_3050_ = l_Lean_Exception_isInterrupt(v_a_3040_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
lean_inc(v_a_3040_);
v___x_3051_ = l_Lean_Exception_isRuntime(v_a_3040_);
v___y_3045_ = v___x_3051_;
goto v___jp_3044_;
}
else
{
v___y_3045_ = v___x_3050_;
goto v___jp_3044_;
}
v___jp_3044_:
{
if (v___y_3045_ == 0)
{
lean_del_object(v___x_3042_);
lean_dec(v_a_3040_);
v_x_3020_ = v_tail_3030_;
goto _start;
}
else
{
lean_object* v___x_3048_; 
lean_dec(v_tail_3030_);
lean_dec(v_x_3021_);
if (v_isShared_3043_ == 0)
{
v___x_3048_ = v___x_3042_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3040_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3020_ = stack[0].m_obj;
lean_object* v_x_3021_ = stack[1].m_obj;
lean_object* v___y_3022_ = stack[2].m_obj;
lean_object* v___y_3023_ = stack[3].m_obj;
lean_object* v___y_3024_ = stack[4].m_obj;
lean_object* v___y_3025_ = stack[5].m_obj;
lean_object* v_res_3054_;
v_res_3054_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3020_, v_x_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
stack->m_obj
 = v_res_3054_;
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3055_, v_x_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
return v_res_3062_;
}
}
lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3063_, lean_object* v_hyps_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
if (v_symm_3063_ == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_hyps_3064_);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_box(0);
lean_inc(v_hyps_3064_);
v___x_3072_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3064_, v___x_3071_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3081_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3081_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3081_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3077_ = l_List_appendTR___redArg(v_hyps_3064_, v_a_3073_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3077_);
v___x_3079_ = v___x_3075_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
else
{
lean_dec(v_hyps_3064_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_saturateSymm_0interp(lean_interpreter_value* stack)
{
uint8_t v_symm_3063_ = stack[0].m_num;
lean_object* v_hyps_3064_ = stack[1].m_obj;
lean_object* v_a_3065_ = stack[2].m_obj;
lean_object* v_a_3066_ = stack[3].m_obj;
lean_object* v_a_3067_ = stack[4].m_obj;
lean_object* v_a_3068_ = stack[5].m_obj;
lean_object* v_res_3082_;
v_res_3082_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3063_, v_hyps_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
stack->m_obj
 = v_res_3082_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3083_, lean_object* v_hyps_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
uint8_t v_symm_boxed_3090_; lean_object* v_res_3091_; 
v_symm_boxed_3090_ = lean_unbox(v_symm_3083_);
v_res_3091_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3090_, v_hyps_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
return v_res_3091_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3092_, size_t v_sz_3093_, size_t v_i_3094_, lean_object* v_b_3095_){
_start:
{
uint8_t v___x_3097_; 
v___x_3097_ = lean_usize_dec_lt(v_i_3094_, v_sz_3093_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_b_3095_);
return v___x_3098_;
}
else
{
lean_object* v_snd_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3117_; 
v_snd_3099_ = lean_ctor_get(v_b_3095_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_b_3095_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v_b_3095_, 0);
lean_dec(v_unused_3118_);
v___x_3101_ = v_b_3095_;
v_isShared_3102_ = v_isSharedCheck_3117_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snd_3099_);
lean_dec(v_b_3095_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3117_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v_a_3105_; lean_object* v_a_3112_; 
v___x_3103_ = lean_box(0);
v_a_3112_ = lean_array_uget_borrowed(v_as_3092_, v_i_3094_);
if (lean_obj_tag(v_a_3112_) == 0)
{
v_a_3105_ = v_snd_3099_;
goto v___jp_3104_;
}
else
{
lean_object* v_val_3113_; uint8_t v___x_3114_; 
v_val_3113_ = lean_ctor_get(v_a_3112_, 0);
v___x_3114_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_inc(v_val_3113_);
v___x_3115_ = l_Lean_LocalDecl_toExpr(v_val_3113_);
v___x_3116_ = lean_array_push(v_snd_3099_, v___x_3115_);
v_a_3105_ = v___x_3116_;
goto v___jp_3104_;
}
else
{
v_a_3105_ = v_snd_3099_;
goto v___jp_3104_;
}
}
v___jp_3104_:
{
lean_object* v___x_3107_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v_a_3105_);
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3107_ = v___x_3101_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_a_3105_);
v___x_3107_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
size_t v___x_3108_; size_t v___x_3109_; 
v___x_3108_ = ((size_t)1ULL);
v___x_3109_ = lean_usize_add(v_i_3094_, v___x_3108_);
v_i_3094_ = v___x_3109_;
v_b_3095_ = v___x_3107_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3092_ = stack[0].m_obj;
size_t v_sz_3093_ = stack[1].m_num;
size_t v_i_3094_ = stack[2].m_num;
lean_object* v_b_3095_ = stack[3].m_obj;
lean_object* v_res_3119_;
v_res_3119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3092_, v_sz_3093_, v_i_3094_, v_b_3095_);
stack->m_obj
 = v_res_3119_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3120_, lean_object* v_sz_3121_, lean_object* v_i_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_){
_start:
{
size_t v_sz_boxed_3125_; size_t v_i_boxed_3126_; lean_object* v_res_3127_; 
v_sz_boxed_3125_ = lean_unbox_usize(v_sz_3121_);
lean_dec(v_sz_3121_);
v_i_boxed_3126_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_res_3127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3120_, v_sz_boxed_3125_, v_i_boxed_3126_, v_b_3123_);
lean_dec_ref(v_as_3120_);
return v_res_3127_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3128_, size_t v_sz_3129_, size_t v_i_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_usize_dec_lt(v_i_3130_, v_sz_3129_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_b_3131_);
return v___x_3140_;
}
else
{
lean_object* v_snd_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3159_; 
v_snd_3141_ = lean_ctor_get(v_b_3131_, 1);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_b_3131_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v_b_3131_, 0);
lean_dec(v_unused_3160_);
v___x_3143_ = v_b_3131_;
v_isShared_3144_ = v_isSharedCheck_3159_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_snd_3141_);
lean_dec(v_b_3131_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3159_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v_a_3147_; lean_object* v_a_3154_; 
v___x_3145_ = lean_box(0);
v_a_3154_ = lean_array_uget_borrowed(v_as_3128_, v_i_3130_);
if (lean_obj_tag(v_a_3154_) == 0)
{
v_a_3147_ = v_snd_3141_;
goto v___jp_3146_;
}
else
{
lean_object* v_val_3155_; uint8_t v___x_3156_; 
v_val_3155_ = lean_ctor_get(v_a_3154_, 0);
v___x_3156_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_inc(v_val_3155_);
v___x_3157_ = l_Lean_LocalDecl_toExpr(v_val_3155_);
v___x_3158_ = lean_array_push(v_snd_3141_, v___x_3157_);
v_a_3147_ = v___x_3158_;
goto v___jp_3146_;
}
else
{
v_a_3147_ = v_snd_3141_;
goto v___jp_3146_;
}
}
v___jp_3146_:
{
lean_object* v___x_3149_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 1, v_a_3147_);
lean_ctor_set(v___x_3143_, 0, v___x_3145_);
v___x_3149_ = v___x_3143_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_a_3147_);
v___x_3149_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
size_t v___x_3150_; size_t v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = ((size_t)1ULL);
v___x_3151_ = lean_usize_add(v_i_3130_, v___x_3150_);
v___x_3152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3128_, v_sz_3129_, v___x_3151_, v___x_3149_);
return v___x_3152_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3128_ = stack[0].m_obj;
size_t v_sz_3129_ = stack[1].m_num;
size_t v_i_3130_ = stack[2].m_num;
lean_object* v_b_3131_ = stack[3].m_obj;
lean_object* v___y_3132_ = stack[4].m_obj;
lean_object* v___y_3133_ = stack[5].m_obj;
lean_object* v___y_3134_ = stack[6].m_obj;
lean_object* v___y_3135_ = stack[7].m_obj;
lean_object* v___y_3136_ = stack[8].m_obj;
lean_object* v___y_3137_ = stack[9].m_obj;
lean_object* v_res_3161_;
v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3128_, v_sz_3129_, v_i_3130_, v_b_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
stack->m_obj
 = v_res_3161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3162_, lean_object* v_sz_3163_, lean_object* v_i_3164_, lean_object* v_b_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
size_t v_sz_boxed_3173_; size_t v_i_boxed_3174_; lean_object* v_res_3175_; 
v_sz_boxed_3173_ = lean_unbox_usize(v_sz_3163_);
lean_dec(v_sz_3163_);
v_i_boxed_3174_ = lean_unbox_usize(v_i_3164_);
lean_dec(v_i_3164_);
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3162_, v_sz_boxed_3173_, v_i_boxed_3174_, v_b_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3176_, size_t v_sz_3177_, size_t v_i_3178_, lean_object* v_b_3179_){
_start:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_usize_dec_lt(v_i_3178_, v_sz_3177_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_b_3179_);
return v___x_3182_;
}
else
{
lean_object* v_snd_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3201_; 
v_snd_3183_ = lean_ctor_get(v_b_3179_, 1);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_b_3179_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; 
v_unused_3202_ = lean_ctor_get(v_b_3179_, 0);
lean_dec(v_unused_3202_);
v___x_3185_ = v_b_3179_;
v_isShared_3186_ = v_isSharedCheck_3201_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_snd_3183_);
lean_dec(v_b_3179_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3201_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v_a_3189_; lean_object* v_a_3196_; 
v___x_3187_ = lean_box(0);
v_a_3196_ = lean_array_uget_borrowed(v_as_3176_, v_i_3178_);
if (lean_obj_tag(v_a_3196_) == 0)
{
v_a_3189_ = v_snd_3183_;
goto v___jp_3188_;
}
else
{
lean_object* v_val_3197_; uint8_t v___x_3198_; 
v_val_3197_ = lean_ctor_get(v_a_3196_, 0);
v___x_3198_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_inc(v_val_3197_);
v___x_3199_ = l_Lean_LocalDecl_toExpr(v_val_3197_);
v___x_3200_ = lean_array_push(v_snd_3183_, v___x_3199_);
v_a_3189_ = v___x_3200_;
goto v___jp_3188_;
}
else
{
v_a_3189_ = v_snd_3183_;
goto v___jp_3188_;
}
}
v___jp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v_a_3189_);
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3191_ = v___x_3185_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_a_3189_);
v___x_3191_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
size_t v___x_3192_; size_t v___x_3193_; 
v___x_3192_ = ((size_t)1ULL);
v___x_3193_ = lean_usize_add(v_i_3178_, v___x_3192_);
v_i_3178_ = v___x_3193_;
v_b_3179_ = v___x_3191_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3176_ = stack[0].m_obj;
size_t v_sz_3177_ = stack[1].m_num;
size_t v_i_3178_ = stack[2].m_num;
lean_object* v_b_3179_ = stack[3].m_obj;
lean_object* v_res_3203_;
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3176_, v_sz_3177_, v_i_3178_, v_b_3179_);
stack->m_obj
 = v_res_3203_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3204_, lean_object* v_sz_3205_, lean_object* v_i_3206_, lean_object* v_b_3207_, lean_object* v___y_3208_){
_start:
{
size_t v_sz_boxed_3209_; size_t v_i_boxed_3210_; lean_object* v_res_3211_; 
v_sz_boxed_3209_ = lean_unbox_usize(v_sz_3205_);
lean_dec(v_sz_3205_);
v_i_boxed_3210_ = lean_unbox_usize(v_i_3206_);
lean_dec(v_i_3206_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3204_, v_sz_boxed_3209_, v_i_boxed_3210_, v_b_3207_);
lean_dec_ref(v_as_3204_);
return v_res_3211_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_b_3215_);
return v___x_3224_;
}
else
{
lean_object* v_snd_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3243_; 
v_snd_3225_ = lean_ctor_get(v_b_3215_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_b_3215_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_b_3215_, 0);
lean_dec(v_unused_3244_);
v___x_3227_ = v_b_3215_;
v_isShared_3228_ = v_isSharedCheck_3243_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_snd_3225_);
lean_dec(v_b_3215_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3243_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v_a_3231_; lean_object* v_a_3238_; 
v___x_3229_ = lean_box(0);
v_a_3238_ = lean_array_uget_borrowed(v_as_3212_, v_i_3214_);
if (lean_obj_tag(v_a_3238_) == 0)
{
v_a_3231_ = v_snd_3225_;
goto v___jp_3230_;
}
else
{
lean_object* v_val_3239_; uint8_t v___x_3240_; 
v_val_3239_ = lean_ctor_get(v_a_3238_, 0);
v___x_3240_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_inc(v_val_3239_);
v___x_3241_ = l_Lean_LocalDecl_toExpr(v_val_3239_);
v___x_3242_ = lean_array_push(v_snd_3225_, v___x_3241_);
v_a_3231_ = v___x_3242_;
goto v___jp_3230_;
}
else
{
v_a_3231_ = v_snd_3225_;
goto v___jp_3230_;
}
}
v___jp_3230_:
{
lean_object* v___x_3233_; 
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 1, v_a_3231_);
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3233_ = v___x_3227_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_a_3231_);
v___x_3233_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
size_t v___x_3234_; size_t v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = ((size_t)1ULL);
v___x_3235_ = lean_usize_add(v_i_3214_, v___x_3234_);
v___x_3236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3212_, v_sz_3213_, v___x_3235_, v___x_3233_);
return v___x_3236_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3212_ = stack[0].m_obj;
size_t v_sz_3213_ = stack[1].m_num;
size_t v_i_3214_ = stack[2].m_num;
lean_object* v_b_3215_ = stack[3].m_obj;
lean_object* v___y_3216_ = stack[4].m_obj;
lean_object* v___y_3217_ = stack[5].m_obj;
lean_object* v___y_3218_ = stack[6].m_obj;
lean_object* v___y_3219_ = stack[7].m_obj;
lean_object* v___y_3220_ = stack[8].m_obj;
lean_object* v___y_3221_ = stack[9].m_obj;
lean_object* v_res_3245_;
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3212_, v_sz_3213_, v_i_3214_, v_b_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
stack->m_obj
 = v_res_3245_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3246_, lean_object* v_sz_3247_, lean_object* v_i_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
size_t v_sz_boxed_3257_; size_t v_i_boxed_3258_; lean_object* v_res_3259_; 
v_sz_boxed_3257_ = lean_unbox_usize(v_sz_3247_);
lean_dec(v_sz_3247_);
v_i_boxed_3258_ = lean_unbox_usize(v_i_3248_);
lean_dec(v_i_3248_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3246_, v_sz_boxed_3257_, v_i_boxed_3258_, v_b_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v_as_3246_);
return v_res_3259_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3260_, lean_object* v_n_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
if (lean_obj_tag(v_n_3261_) == 0)
{
lean_object* v_cs_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; size_t v_sz_3273_; size_t v___x_3274_; lean_object* v___x_3275_; 
v_cs_3270_ = lean_ctor_get(v_n_3261_, 0);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v_b_3262_);
v_sz_3273_ = lean_array_size(v_cs_3270_);
v___x_3274_ = ((size_t)0ULL);
v___x_3275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3260_, v_cs_3270_, v_sz_3273_, v___x_3274_, v___x_3272_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3290_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3290_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3290_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_fst_3280_; 
v_fst_3280_ = lean_ctor_get(v_a_3276_, 0);
if (lean_obj_tag(v_fst_3280_) == 0)
{
lean_object* v_snd_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v_snd_3281_ = lean_ctor_get(v_a_3276_, 1);
lean_inc(v_snd_3281_);
lean_dec(v_a_3276_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_snd_3281_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3282_);
v___x_3284_ = v___x_3278_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
else
{
lean_object* v_val_3286_; lean_object* v___x_3288_; 
lean_inc_ref(v_fst_3280_);
lean_dec(v_a_3276_);
v_val_3286_ = lean_ctor_get(v_fst_3280_, 0);
lean_inc(v_val_3286_);
lean_dec_ref_known(v_fst_3280_, 1);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v_val_3286_);
v___x_3288_ = v___x_3278_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_val_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
v_a_3291_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3275_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3275_);
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
else
{
lean_object* v_vs_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; size_t v_sz_3302_; size_t v___x_3303_; lean_object* v___x_3304_; 
v_vs_3299_ = lean_ctor_get(v_n_3261_, 0);
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v_b_3262_);
v_sz_3302_ = lean_array_size(v_vs_3299_);
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3299_, v_sz_3302_, v___x_3303_, v___x_3301_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3319_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3319_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3319_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v_fst_3309_; 
v_fst_3309_ = lean_ctor_get(v_a_3305_, 0);
if (lean_obj_tag(v_fst_3309_) == 0)
{
lean_object* v_snd_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v_snd_3310_ = lean_ctor_get(v_a_3305_, 1);
lean_inc(v_snd_3310_);
lean_dec(v_a_3305_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_snd_3310_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3311_);
v___x_3313_ = v___x_3307_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3317_; 
lean_inc_ref(v_fst_3309_);
lean_dec(v_a_3305_);
v_val_3315_ = lean_ctor_get(v_fst_3309_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v_fst_3309_, 1);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v_val_3315_);
v___x_3317_ = v___x_3307_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_val_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
v_a_3320_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3304_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3304_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3260_ = stack[0].m_obj;
lean_object* v_n_3261_ = stack[1].m_obj;
lean_object* v_b_3262_ = stack[2].m_obj;
lean_object* v___y_3263_ = stack[3].m_obj;
lean_object* v___y_3264_ = stack[4].m_obj;
lean_object* v___y_3265_ = stack[5].m_obj;
lean_object* v___y_3266_ = stack[6].m_obj;
lean_object* v___y_3267_ = stack[7].m_obj;
lean_object* v___y_3268_ = stack[8].m_obj;
lean_object* v_res_3328_;
v_res_3328_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3260_, v_n_3261_, v_b_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
stack->m_obj
 = v_res_3328_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3329_, lean_object* v_as_3330_, size_t v_sz_3331_, size_t v_i_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v___x_3341_; 
v___x_3341_ = lean_usize_dec_lt(v_i_3332_, v_sz_3331_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v_b_3333_);
return v___x_3342_;
}
else
{
lean_object* v_snd_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3377_; 
v_snd_3343_ = lean_ctor_get(v_b_3333_, 1);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_b_3333_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v_b_3333_, 0);
lean_dec(v_unused_3378_);
v___x_3345_ = v_b_3333_;
v_isShared_3346_ = v_isSharedCheck_3377_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3343_);
lean_dec(v_b_3333_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3377_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v_a_3348_; lean_object* v___x_3349_; 
v___x_3347_ = lean_box(0);
v_a_3348_ = lean_array_uget_borrowed(v_as_3330_, v_i_3332_);
lean_inc(v_snd_3343_);
v___x_3349_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3329_, v_a_3348_, v_snd_3343_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3368_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3368_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3368_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
if (lean_obj_tag(v_a_3350_) == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_a_3350_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3354_);
v___x_3356_ = v___x_3345_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_snd_3343_);
v___x_3356_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3358_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3356_);
v___x_3358_ = v___x_3352_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; 
lean_del_object(v___x_3352_);
lean_dec(v_snd_3343_);
v_a_3361_ = lean_ctor_get(v_a_3350_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v_a_3350_, 1);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v_a_3361_);
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3363_ = v___x_3345_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_a_3361_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
size_t v___x_3364_; size_t v___x_3365_; 
v___x_3364_ = ((size_t)1ULL);
v___x_3365_ = lean_usize_add(v_i_3332_, v___x_3364_);
v_i_3332_ = v___x_3365_;
v_b_3333_ = v___x_3363_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_del_object(v___x_3345_);
lean_dec(v_snd_3343_);
v_a_3369_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3349_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3349_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3329_ = stack[0].m_obj;
lean_object* v_as_3330_ = stack[1].m_obj;
size_t v_sz_3331_ = stack[2].m_num;
size_t v_i_3332_ = stack[3].m_num;
lean_object* v_b_3333_ = stack[4].m_obj;
lean_object* v___y_3334_ = stack[5].m_obj;
lean_object* v___y_3335_ = stack[6].m_obj;
lean_object* v___y_3336_ = stack[7].m_obj;
lean_object* v___y_3337_ = stack[8].m_obj;
lean_object* v___y_3338_ = stack[9].m_obj;
lean_object* v___y_3339_ = stack[10].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3329_, v_as_3330_, v_sz_3331_, v_i_3332_, v_b_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3380_, lean_object* v_as_3381_, lean_object* v_sz_3382_, lean_object* v_i_3383_, lean_object* v_b_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
size_t v_sz_boxed_3392_; size_t v_i_boxed_3393_; lean_object* v_res_3394_; 
v_sz_boxed_3392_ = lean_unbox_usize(v_sz_3382_);
lean_dec(v_sz_3382_);
v_i_boxed_3393_ = lean_unbox_usize(v_i_3383_);
lean_dec(v_i_3383_);
v_res_3394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3380_, v_as_3381_, v_sz_boxed_3392_, v_i_boxed_3393_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec_ref(v_as_3381_);
lean_dec_ref(v_init_3380_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3395_, lean_object* v_n_3396_, lean_object* v_b_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3395_, v_n_3396_, v_b_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_n_3396_);
lean_dec_ref(v_init_3395_);
return v_res_3405_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3406_, lean_object* v_init_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_root_3415_; lean_object* v_tail_3416_; lean_object* v___x_3417_; 
v_root_3415_ = lean_ctor_get(v_t_3406_, 0);
v_tail_3416_ = lean_ctor_get(v_t_3406_, 1);
lean_inc_ref(v_init_3407_);
v___x_3417_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3407_, v_root_3415_, v_init_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec_ref(v_init_3407_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3454_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3454_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3454_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
if (lean_obj_tag(v_a_3418_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; 
v_a_3422_ = lean_ctor_get(v_a_3418_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v_a_3418_, 1);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v_a_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; size_t v_sz_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
lean_del_object(v___x_3420_);
v_a_3426_ = lean_ctor_get(v_a_3418_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v_a_3418_, 1);
v___x_3427_ = lean_box(0);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v_a_3426_);
v_sz_3429_ = lean_array_size(v_tail_3416_);
v___x_3430_ = ((size_t)0ULL);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3416_, v_sz_3429_, v___x_3430_, v___x_3428_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3445_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_fst_3436_; 
v_fst_3436_ = lean_ctor_get(v_a_3432_, 0);
if (lean_obj_tag(v_fst_3436_) == 0)
{
lean_object* v_snd_3437_; lean_object* v___x_3439_; 
v_snd_3437_ = lean_ctor_get(v_a_3432_, 1);
lean_inc(v_snd_3437_);
lean_dec(v_a_3432_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_snd_3437_);
v___x_3439_ = v___x_3434_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_snd_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
else
{
lean_object* v_val_3441_; lean_object* v___x_3443_; 
lean_inc_ref(v_fst_3436_);
lean_dec(v_a_3432_);
v_val_3441_ = lean_ctor_get(v_fst_3436_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v_fst_3436_, 1);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_val_3441_);
v___x_3443_ = v___x_3434_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_val_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_a_3446_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3431_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3431_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
v_a_3455_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3417_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3417_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3406_ = stack[0].m_obj;
lean_object* v_init_3407_ = stack[1].m_obj;
lean_object* v___y_3408_ = stack[2].m_obj;
lean_object* v___y_3409_ = stack[3].m_obj;
lean_object* v___y_3410_ = stack[4].m_obj;
lean_object* v___y_3411_ = stack[5].m_obj;
lean_object* v___y_3412_ = stack[6].m_obj;
lean_object* v___y_3413_ = stack[7].m_obj;
lean_object* v_res_3463_;
v_res_3463_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3406_, v_init_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
stack->m_obj
 = v_res_3463_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3464_, lean_object* v_init_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3464_, v_init_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v_t_3464_);
return v_res_3473_;
}
}
lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_lctx_3483_; lean_object* v_decls_3484_; lean_object* v_hs_3485_; lean_object* v___x_3486_; 
v_lctx_3483_ = lean_ctor_get(v___y_3478_, 2);
v_decls_3484_ = lean_ctor_get(v_lctx_3483_, 1);
v_hs_3485_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3486_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3484_, v_hs_3485_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
return v___x_3486_;
}
}
LEAN_EXPORT void l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3476_ = stack[0].m_obj;
lean_object* v___y_3477_ = stack[1].m_obj;
lean_object* v___y_3478_ = stack[2].m_obj;
lean_object* v___y_3479_ = stack[3].m_obj;
lean_object* v___y_3480_ = stack[4].m_obj;
lean_object* v___y_3481_ = stack[5].m_obj;
lean_object* v_res_3487_;
v_res_3487_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
stack->m_obj
 = v_res_3487_;
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3495_;
}
}
lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3496_, lean_object* v_cfg_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
if (v_only_3496_ == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_toApplyRulesConfig_3506_; lean_object* v_a_3507_; uint8_t v_symm_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_toApplyRulesConfig_3506_ = lean_ctor_get(v_cfg_3497_, 0);
v_a_3507_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___x_3505_, 1);
v_symm_3508_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3506_, sizeof(void*)*2 + 1);
v___x_3509_ = lean_array_to_list(v_a_3507_);
v___x_3510_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3508_, v___x_3509_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3510_;
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
v_a_3511_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3505_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3505_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_box(0);
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_applyRules___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_only_3496_ = stack[0].m_num;
lean_object* v_cfg_3497_ = stack[1].m_obj;
lean_object* v___y_3498_ = stack[2].m_obj;
lean_object* v___y_3499_ = stack[3].m_obj;
lean_object* v___y_3500_ = stack[4].m_obj;
lean_object* v___y_3501_ = stack[5].m_obj;
lean_object* v___y_3502_ = stack[6].m_obj;
lean_object* v___y_3503_ = stack[7].m_obj;
lean_object* v_res_3521_;
v_res_3521_ = l_Lean_MVarId_applyRules___lam__0(v_only_3496_, v_cfg_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
stack->m_obj
 = v_res_3521_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3522_, lean_object* v_cfg_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v_only_boxed_3531_; lean_object* v_res_3532_; 
v_only_boxed_3531_ = lean_unbox(v_only_3522_);
v_res_3532_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3531_, v_cfg_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v_cfg_3523_);
return v_res_3532_;
}
}
lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3533_, lean_object* v_lemmas_3534_, uint8_t v_only_3535_, lean_object* v_g_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_toApplyRulesConfig_3542_; uint8_t v_intro_3543_; uint8_t v_constructor_3544_; uint8_t v_suggestions_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3558_; 
v_toApplyRulesConfig_3542_ = lean_ctor_get(v_cfg_3533_, 0);
v_intro_3543_ = lean_ctor_get_uint8(v_cfg_3533_, sizeof(void*)*1 + 1);
v_constructor_3544_ = lean_ctor_get_uint8(v_cfg_3533_, sizeof(void*)*1 + 2);
v_suggestions_3545_ = lean_ctor_get_uint8(v_cfg_3533_, sizeof(void*)*1 + 3);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_cfg_3533_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3547_ = v_cfg_3533_;
v_isShared_3548_ = v_isSharedCheck_3558_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_toApplyRulesConfig_3542_);
lean_dec(v_cfg_3533_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3558_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v_ctx_3550_; uint8_t v___x_3551_; lean_object* v___x_3553_; 
v___x_3549_ = lean_box(v_only_3535_);
v_ctx_3550_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3550_, 0, v___x_3549_);
v___x_3551_ = 0;
if (v_isShared_3548_ == 0)
{
v___x_3553_ = v___x_3547_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_toApplyRulesConfig_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3557_, sizeof(void*)*1 + 1, v_intro_3543_);
lean_ctor_set_uint8(v_reuseFailAlloc_3557_, sizeof(void*)*1 + 2, v_constructor_3544_);
lean_ctor_set_uint8(v_reuseFailAlloc_3557_, sizeof(void*)*1 + 3, v_suggestions_3545_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*1, v___x_3551_);
v___x_3554_ = lean_box(0);
v___x_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3555_, 0, v_g_3536_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3553_, v_lemmas_3534_, v_ctx_3550_, v___x_3555_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
return v___x_3556_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_applyRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3533_ = stack[0].m_obj;
lean_object* v_lemmas_3534_ = stack[1].m_obj;
uint8_t v_only_3535_ = stack[2].m_num;
lean_object* v_g_3536_ = stack[3].m_obj;
lean_object* v_a_3537_ = stack[4].m_obj;
lean_object* v_a_3538_ = stack[5].m_obj;
lean_object* v_a_3539_ = stack[6].m_obj;
lean_object* v_a_3540_ = stack[7].m_obj;
lean_object* v_res_3559_;
v_res_3559_ = l_Lean_MVarId_applyRules(v_cfg_3533_, v_lemmas_3534_, v_only_3535_, v_g_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
stack->m_obj
 = v_res_3559_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3560_, lean_object* v_lemmas_3561_, lean_object* v_only_3562_, lean_object* v_g_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
uint8_t v_only_boxed_3569_; lean_object* v_res_3570_; 
v_only_boxed_3569_ = lean_unbox(v_only_3562_);
v_res_3570_ = l_Lean_MVarId_applyRules(v_cfg_3560_, v_lemmas_3561_, v_only_boxed_3569_, v_g_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
return v_res_3570_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3571_, size_t v_sz_3572_, size_t v_i_3573_, lean_object* v_b_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3571_, v_sz_3572_, v_i_3573_, v_b_3574_);
return v___x_3582_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3571_ = stack[0].m_obj;
size_t v_sz_3572_ = stack[1].m_num;
size_t v_i_3573_ = stack[2].m_num;
lean_object* v_b_3574_ = stack[3].m_obj;
lean_object* v___y_3575_ = stack[4].m_obj;
lean_object* v___y_3576_ = stack[5].m_obj;
lean_object* v___y_3577_ = stack[6].m_obj;
lean_object* v___y_3578_ = stack[7].m_obj;
lean_object* v___y_3579_ = stack[8].m_obj;
lean_object* v___y_3580_ = stack[9].m_obj;
lean_object* v_res_3583_;
v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3571_, v_sz_3572_, v_i_3573_, v_b_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
stack->m_obj
 = v_res_3583_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3584_, lean_object* v_sz_3585_, lean_object* v_i_3586_, lean_object* v_b_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
size_t v_sz_boxed_3595_; size_t v_i_boxed_3596_; lean_object* v_res_3597_; 
v_sz_boxed_3595_ = lean_unbox_usize(v_sz_3585_);
lean_dec(v_sz_3585_);
v_i_boxed_3596_ = lean_unbox_usize(v_i_3586_);
lean_dec(v_i_3586_);
v_res_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3584_, v_sz_boxed_3595_, v_i_boxed_3596_, v_b_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v_as_3584_);
return v_res_3597_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3598_, size_t v_sz_3599_, size_t v_i_3600_, lean_object* v_b_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3598_, v_sz_3599_, v_i_3600_, v_b_3601_);
return v___x_3609_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3598_ = stack[0].m_obj;
size_t v_sz_3599_ = stack[1].m_num;
size_t v_i_3600_ = stack[2].m_num;
lean_object* v_b_3601_ = stack[3].m_obj;
lean_object* v___y_3602_ = stack[4].m_obj;
lean_object* v___y_3603_ = stack[5].m_obj;
lean_object* v___y_3604_ = stack[6].m_obj;
lean_object* v___y_3605_ = stack[7].m_obj;
lean_object* v___y_3606_ = stack[8].m_obj;
lean_object* v___y_3607_ = stack[9].m_obj;
lean_object* v_res_3610_;
v_res_3610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3598_, v_sz_3599_, v_i_3600_, v_b_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
stack->m_obj
 = v_res_3610_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3611_, lean_object* v_sz_3612_, lean_object* v_i_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
size_t v_sz_boxed_3622_; size_t v_i_boxed_3623_; lean_object* v_res_3624_; 
v_sz_boxed_3622_ = lean_unbox_usize(v_sz_3612_);
lean_dec(v_sz_3612_);
v_i_boxed_3623_ = lean_unbox_usize(v_i_3613_);
lean_dec(v_i_3613_);
v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3611_, v_sz_boxed_3622_, v_i_boxed_3623_, v_b_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v_as_3611_);
return v_res_3624_;
}
}
lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v___x_3633_; uint8_t v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_box(0);
v___x_3634_ = 1;
v___x_3635_ = l_Lean_Elab_Term_elabTerm(v_t_3625_, v___x_3633_, v___x_3634_, v___x_3634_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
return v___x_3635_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3625_ = stack[0].m_obj;
lean_object* v_a_3626_ = stack[1].m_obj;
lean_object* v_a_3627_ = stack[2].m_obj;
lean_object* v_a_3628_ = stack[3].m_obj;
lean_object* v_a_3629_ = stack[4].m_obj;
lean_object* v_a_3630_ = stack[5].m_obj;
lean_object* v_a_3631_ = stack[6].m_obj;
lean_object* v_res_3636_;
v_res_3636_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
stack->m_obj
 = v_res_3636_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
return v_res_3645_;
}
}
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_ref_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_ref_3651_ = lean_ctor_get(v___y_3648_, 2);
v___x_3652_ = 0;
v___x_3653_ = l_Lean_SourceInfo_fromRef(v_ref_3651_, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3646_ = stack[0].m_obj;
lean_object* v___y_3647_ = stack[1].m_obj;
lean_object* v___y_3648_ = stack[2].m_obj;
lean_object* v___y_3649_ = stack[3].m_obj;
lean_object* v_res_3655_;
v_res_3655_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
stack->m_obj
 = v_res_3655_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3661_;
}
}
uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object* v_a_3662_, lean_object* v_x_3663_){
_start:
{
if (lean_obj_tag(v_x_3663_) == 0)
{
uint8_t v___x_3664_; 
v___x_3664_ = 0;
return v___x_3664_;
}
else
{
lean_object* v_head_3665_; lean_object* v_tail_3666_; uint8_t v___x_3667_; 
v_head_3665_ = lean_ctor_get(v_x_3663_, 0);
v_tail_3666_ = lean_ctor_get(v_x_3663_, 1);
v___x_3667_ = lean_expr_eqv(v_a_3662_, v_head_3665_);
if (v___x_3667_ == 0)
{
v_x_3663_ = v_tail_3666_;
goto _start;
}
else
{
return v___x_3667_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3662_ = stack[0].m_obj;
lean_object* v_x_3663_ = stack[1].m_obj;
uint8_t v_res_3669_;
v_res_3669_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3662_, v_x_3663_);
stack->m_num = v_res_3669_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object* v_a_3670_, lean_object* v_x_3671_){
_start:
{
uint8_t v_res_3672_; lean_object* v_r_3673_; 
v_res_3672_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3670_, v_x_3671_);
lean_dec(v_x_3671_);
lean_dec_ref(v_a_3670_);
v_r_3673_ = lean_box(v_res_3672_);
return v_r_3673_;
}
}
uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(lean_object* v_ys_3674_, lean_object* v_x_3675_){
_start:
{
uint8_t v___x_3676_; 
v___x_3676_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_x_3675_, v_ys_3674_);
if (v___x_3676_ == 0)
{
uint8_t v___x_3677_; 
v___x_3677_ = 1;
return v___x_3677_;
}
else
{
uint8_t v___x_3678_; 
v___x_3678_ = 0;
return v___x_3678_;
}
}
}
LEAN_EXPORT void l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_3674_ = stack[0].m_obj;
lean_object* v_x_3675_ = stack[1].m_obj;
uint8_t v_res_3679_;
v_res_3679_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(v_ys_3674_, v_x_3675_);
stack->m_num = v_res_3679_;
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed(lean_object* v_ys_3680_, lean_object* v_x_3681_){
_start:
{
uint8_t v_res_3682_; lean_object* v_r_3683_; 
v_res_3682_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(v_ys_3680_, v_x_3681_);
lean_dec_ref(v_x_3681_);
lean_dec(v_ys_3680_);
v_r_3683_ = lean_box(v_res_3682_);
return v_r_3683_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_xs_3684_, lean_object* v_ys_3685_){
_start:
{
lean_object* v___f_3686_; lean_object* v___x_3687_; 
v___f_3686_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3686_, 0, v_ys_3685_);
v___x_3687_ = l_List_filter___redArg(v___f_3686_, v_xs_3684_);
return v___x_3687_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object* v_x_3688_, lean_object* v_x_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
if (lean_obj_tag(v_x_3688_) == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = l_List_reverse___redArg(v_x_3689_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
return v___x_3698_;
}
else
{
lean_object* v_head_3699_; lean_object* v_tail_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3718_; 
v_head_3699_ = lean_ctor_get(v_x_3688_, 0);
v_tail_3700_ = lean_ctor_get(v_x_3688_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3702_ = v_x_3688_;
v_isShared_3703_ = v_isSharedCheck_3718_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_tail_3700_);
lean_inc(v_head_3699_);
lean_dec(v_x_3688_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3718_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; 
v___x_3704_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3699_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3707_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 1, v_x_3689_);
lean_ctor_set(v___x_3702_, 0, v_a_3705_);
v___x_3707_ = v___x_3702_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3705_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_x_3689_);
v___x_3707_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
v_x_3688_ = v_tail_3700_;
v_x_3689_ = v___x_3707_;
goto _start;
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_del_object(v___x_3702_);
lean_dec(v_tail_3700_);
lean_dec(v_x_3689_);
v_a_3710_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3704_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3704_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3688_ = stack[0].m_obj;
lean_object* v_x_3689_ = stack[1].m_obj;
lean_object* v___y_3690_ = stack[2].m_obj;
lean_object* v___y_3691_ = stack[3].m_obj;
lean_object* v___y_3692_ = stack[4].m_obj;
lean_object* v___y_3693_ = stack[5].m_obj;
lean_object* v___y_3694_ = stack[6].m_obj;
lean_object* v___y_3695_ = stack[7].m_obj;
lean_object* v_res_3719_;
v_res_3719_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3688_, v_x_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
stack->m_obj
 = v_res_3719_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_x_3720_, lean_object* v_x_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3720_, v_x_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
return v_res_3729_;
}
}
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3730_, uint8_t v_noDefaults_3731_, uint8_t v_star_3732_, lean_object* v_cfg_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
if (v_noDefaults_3731_ == 0)
{
goto v___jp_3741_;
}
else
{
if (v_star_3732_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec(v_remove_3730_);
v___x_3760_ = lean_box(0);
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
return v___x_3761_;
}
else
{
goto v___jp_3741_;
}
}
v___jp_3741_:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = lean_box(0);
v___x_3745_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_remove_3730_, v___x_3744_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_toApplyRulesConfig_3746_; lean_object* v_a_3747_; uint8_t v_symm_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_toApplyRulesConfig_3746_ = lean_ctor_get(v_cfg_3733_, 0);
v_a_3747_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3745_, 1);
v_symm_3748_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3746_, sizeof(void*)*2 + 1);
v___x_3749_ = lean_array_to_list(v_a_3743_);
v___x_3750_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v___x_3749_, v_a_3747_);
v___x_3751_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3748_, v___x_3750_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3751_;
}
else
{
lean_dec(v_a_3743_);
return v___x_3745_;
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_remove_3730_);
v_a_3752_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3742_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3742_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_remove_3730_ = stack[0].m_obj;
uint8_t v_noDefaults_3731_ = stack[1].m_num;
uint8_t v_star_3732_ = stack[2].m_num;
lean_object* v_cfg_3733_ = stack[3].m_obj;
lean_object* v___y_3734_ = stack[4].m_obj;
lean_object* v___y_3735_ = stack[5].m_obj;
lean_object* v___y_3736_ = stack[6].m_obj;
lean_object* v___y_3737_ = stack[7].m_obj;
lean_object* v___y_3738_ = stack[8].m_obj;
lean_object* v___y_3739_ = stack[9].m_obj;
lean_object* v_res_3762_;
v_res_3762_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3730_, v_noDefaults_3731_, v_star_3732_, v_cfg_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
stack->m_obj
 = v_res_3762_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3763_, lean_object* v_noDefaults_3764_, lean_object* v_star_3765_, lean_object* v_cfg_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
uint8_t v_noDefaults_boxed_3774_; uint8_t v_star_boxed_3775_; lean_object* v_res_3776_; 
v_noDefaults_boxed_3774_ = lean_unbox(v_noDefaults_3764_);
v_star_boxed_3775_ = lean_unbox(v_star_3765_);
v_res_3776_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3763_, v_noDefaults_boxed_3774_, v_star_boxed_3775_, v_cfg_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec_ref(v_cfg_3766_);
return v_res_3776_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t v_sz_3777_, size_t v_i_3778_, lean_object* v_bs_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
uint8_t v___x_3783_; 
v___x_3783_ = lean_usize_dec_lt(v_i_3778_, v_sz_3777_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_bs_3779_);
return v___x_3784_;
}
else
{
lean_object* v_v_3785_; lean_object* v___x_3786_; lean_object* v_bs_x27_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_v_3785_ = lean_array_uget(v_bs_3779_, v_i_3778_);
v___x_3786_ = lean_unsigned_to_nat(0u);
v_bs_x27_3787_ = lean_array_uset(v_bs_3779_, v_i_3778_, v___x_3786_);
v___x_3788_ = l_Lean_Syntax_getId(v_v_3785_);
lean_dec(v_v_3785_);
v___x_3789_ = l_Lean_labelled(v___x_3788_, v___y_3780_, v___y_3781_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v___x_3791_ = ((size_t)1ULL);
v___x_3792_ = lean_usize_add(v_i_3778_, v___x_3791_);
v___x_3793_ = lean_array_uset(v_bs_x27_3787_, v_i_3778_, v_a_3790_);
v_i_3778_ = v___x_3792_;
v_bs_3779_ = v___x_3793_;
goto _start;
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec_ref(v_bs_x27_3787_);
v_a_3795_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3789_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3789_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3777_ = stack[0].m_num;
size_t v_i_3778_ = stack[1].m_num;
lean_object* v_bs_3779_ = stack[2].m_obj;
lean_object* v___y_3780_ = stack[3].m_obj;
lean_object* v___y_3781_ = stack[4].m_obj;
lean_object* v_res_3803_;
v_res_3803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3777_, v_i_3778_, v_bs_3779_, v___y_3780_, v___y_3781_);
stack->m_obj
 = v_res_3803_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object* v_sz_3804_, lean_object* v_i_3805_, lean_object* v_bs_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
size_t v_sz_boxed_3810_; size_t v_i_boxed_3811_; lean_object* v_res_3812_; 
v_sz_boxed_3810_ = lean_unbox_usize(v_sz_3804_);
lean_dec(v_sz_3804_);
v_i_boxed_3811_ = lean_unbox_usize(v_i_3805_);
lean_dec(v_i_3805_);
v_res_3812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_boxed_3810_, v_i_boxed_3811_, v_bs_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
return v_res_3812_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3813_, size_t v_i_3814_, size_t v_stop_3815_, lean_object* v_b_3816_){
_start:
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_usize_dec_eq(v_i_3814_, v_stop_3815_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; 
v___x_3818_ = lean_array_uget_borrowed(v_as_3813_, v_i_3814_);
v___x_3819_ = l_Array_append___redArg(v_b_3816_, v___x_3818_);
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_add(v_i_3814_, v___x_3820_);
v_i_3814_ = v___x_3821_;
v_b_3816_ = v___x_3819_;
goto _start;
}
else
{
return v_b_3816_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3813_ = stack[0].m_obj;
size_t v_i_3814_ = stack[1].m_num;
size_t v_stop_3815_ = stack[2].m_num;
lean_object* v_b_3816_ = stack[3].m_obj;
lean_object* v_res_3823_;
v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3813_, v_i_3814_, v_stop_3815_, v_b_3816_);
stack->m_obj
 = v_res_3823_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3824_, lean_object* v_i_3825_, lean_object* v_stop_3826_, lean_object* v_b_3827_){
_start:
{
size_t v_i_boxed_3828_; size_t v_stop_boxed_3829_; lean_object* v_res_3830_; 
v_i_boxed_3828_ = lean_unbox_usize(v_i_3825_);
lean_dec(v_i_3825_);
v_stop_boxed_3829_ = lean_unbox_usize(v_stop_3826_);
lean_dec(v_stop_3826_);
v_res_3830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3824_, v_i_boxed_3828_, v_stop_boxed_3829_, v_b_3827_);
lean_dec_ref(v_as_3824_);
return v_res_3830_;
}
}
lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3831_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3839_;
}
}
LEAN_EXPORT void l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_3831_ = stack[0].m_obj;
lean_object* v___y_3832_ = stack[1].m_obj;
lean_object* v___y_3833_ = stack[2].m_obj;
lean_object* v___y_3834_ = stack[3].m_obj;
lean_object* v___y_3835_ = stack[4].m_obj;
lean_object* v___y_3836_ = stack[5].m_obj;
lean_object* v___y_3837_ = stack[6].m_obj;
lean_object* v_res_3840_;
v_res_3840_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
stack->m_obj
 = v_res_3840_;
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
if (lean_obj_tag(v_a_3850_) == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = l_List_reverse___redArg(v_a_3851_);
return v___x_3852_;
}
else
{
lean_object* v_head_3853_; lean_object* v_tail_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3863_; 
v_head_3853_ = lean_ctor_get(v_a_3850_, 0);
v_tail_3854_ = lean_ctor_get(v_a_3850_, 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_a_3850_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3856_ = v_a_3850_;
v_isShared_3857_ = v_isSharedCheck_3863_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_tail_3854_);
lean_inc(v_head_3853_);
lean_dec(v_a_3850_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3863_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___f_3858_; lean_object* v___x_3860_; 
v___f_3858_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3858_, 0, v_head_3853_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 1, v_a_3851_);
lean_ctor_set(v___x_3856_, 0, v___f_3858_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___f_3858_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3851_);
v___x_3860_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
v_a_3850_ = v_tail_3854_;
v_a_3851_ = v___x_3860_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
if (lean_obj_tag(v_a_3864_) == 0)
{
lean_object* v___x_3866_; 
v___x_3866_ = l_List_reverse___redArg(v_a_3865_);
return v___x_3866_;
}
else
{
lean_object* v_head_3867_; lean_object* v_tail_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3877_; 
v_head_3867_ = lean_ctor_get(v_a_3864_, 0);
v_tail_3868_ = lean_ctor_get(v_a_3864_, 1);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_a_3864_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3870_ = v_a_3864_;
v_isShared_3871_ = v_isSharedCheck_3877_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_tail_3868_);
lean_inc(v_head_3867_);
lean_dec(v_a_3864_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3877_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3872_, 0, v_head_3867_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v_a_3865_);
lean_ctor_set(v___x_3870_, 0, v___x_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_a_3865_);
v___x_3874_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
v_a_3864_ = v_tail_3868_;
v_a_3865_ = v___x_3874_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3880_ = l_Lean_stringToMessageData(v___x_3879_);
return v___x_3880_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3883_ = l_String_toRawSubstring_x27(v___x_3882_);
return v___x_3883_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3894_ = l_String_toRawSubstring_x27(v___x_3893_);
return v___x_3894_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12));
v___x_3905_ = l_String_toRawSubstring_x27(v___x_3904_);
return v___x_3905_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3916_ = l_String_toRawSubstring_x27(v___x_3915_);
return v___x_3916_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3929_ = l_Lean_stringToMessageData(v___x_3928_);
return v___x_3929_;
}
}
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3930_, uint8_t v_star_3931_, lean_object* v_add_3932_, lean_object* v_remove_3933_, lean_object* v_use_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___f_3965_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; 
v___x_3963_ = lean_box(v_noDefaults_3930_);
v___x_3964_ = lean_box(v_star_3931_);
lean_inc(v_remove_3933_);
v___f_3965_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3965_, 0, v_remove_3933_);
lean_closure_set(v___f_3965_, 1, v___x_3963_);
lean_closure_set(v___f_3965_, 2, v___x_3964_);
if (v_star_3931_ == 0)
{
v___y_3982_ = v_a_3935_;
v___y_3983_ = v_a_3936_;
v___y_3984_ = v_a_3937_;
v___y_3985_ = v_a_3938_;
goto v___jp_3981_;
}
else
{
if (v_noDefaults_3930_ == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref(v___f_3965_);
lean_dec_ref(v_use_3934_);
lean_dec(v_remove_3933_);
lean_dec(v_add_3932_);
v___x_4042_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4043_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4042_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4043_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
else
{
v___y_3982_ = v_a_3935_;
v___y_3983_ = v_a_3936_;
v___y_3984_ = v_a_3937_;
v___y_3985_ = v_a_3938_;
goto v___jp_3981_;
}
}
v___jp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___y_3942_);
lean_ctor_set(v___x_3943_, 1, v___y_3941_);
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
v___jp_3945_:
{
uint8_t v___x_3952_; 
v___x_3952_ = l_List_isEmpty___redArg(v_remove_3933_);
lean_dec(v_remove_3933_);
if (v___x_3952_ == 0)
{
if (v_noDefaults_3930_ == 0)
{
v___y_3941_ = v___y_3949_;
v___y_3942_ = v___y_3951_;
goto v___jp_3940_;
}
else
{
if (v_star_3931_ == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
v___x_3953_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3954_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3953_, v___y_3947_, v___y_3950_, v___y_3946_, v___y_3948_);
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
else
{
v___y_3941_ = v___y_3949_;
v___y_3942_ = v___y_3951_;
goto v___jp_3940_;
}
}
}
else
{
v___y_3941_ = v___y_3949_;
v___y_3942_ = v___y_3951_;
goto v___jp_3940_;
}
}
v___jp_3966_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_array_to_list(v___y_3973_);
lean_inc(v___y_3969_);
v___x_3975_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3974_, v___y_3969_);
if (v_noDefaults_3930_ == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3932_, v___y_3969_);
v___x_3977_ = l_List_appendTR___redArg(v___x_3976_, v___x_3975_);
v___x_3978_ = l_List_appendTR___redArg(v___x_3977_, v___y_3972_);
v___y_3946_ = v___y_3967_;
v___y_3947_ = v___y_3968_;
v___y_3948_ = v___y_3970_;
v___y_3949_ = v___f_3965_;
v___y_3950_ = v___y_3971_;
v___y_3951_ = v___x_3978_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v___y_3972_);
v___x_3979_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3932_, v___y_3969_);
v___x_3980_ = l_List_appendTR___redArg(v___x_3979_, v___x_3975_);
v___y_3946_ = v___y_3967_;
v___y_3947_ = v___y_3968_;
v___y_3948_ = v___y_3970_;
v___y_3949_ = v___f_3965_;
v___y_3950_ = v___y_3971_;
v___y_3951_ = v___x_3980_;
goto v___jp_3945_;
}
}
v___jp_3981_:
{
lean_object* v_toCold_3986_; lean_object* v_ref_3987_; lean_object* v_quotContext_3988_; lean_object* v_currMacroScope_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v_a_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v_a_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v_a_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; size_t v_sz_4024_; size_t v___x_4025_; lean_object* v___x_4026_; 
v_toCold_3986_ = lean_ctor_get(v___y_3984_, 0);
v_ref_3987_ = lean_ctor_get(v___y_3984_, 2);
v_quotContext_3988_ = lean_ctor_get(v_toCold_3986_, 8);
v_currMacroScope_3989_ = lean_ctor_get(v_toCold_3986_, 9);
v___x_3990_ = 0;
v___x_3991_ = l_Lean_SourceInfo_fromRef(v_ref_3987_, v___x_3990_);
v___x_3992_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3993_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3989_, 4);
lean_inc_n(v_quotContext_3988_, 4);
v___x_3994_ = l_Lean_addMacroScope(v_quotContext_3988_, v___x_3993_, v_currMacroScope_3989_);
v___x_3995_ = lean_box(0);
v___x_3996_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6));
v___x_3997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3991_);
lean_ctor_set(v___x_3997_, 1, v___x_3992_);
lean_ctor_set(v___x_3997_, 2, v___x_3994_);
lean_ctor_set(v___x_3997_, 3, v___x_3996_);
v___x_3998_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8);
v___x_4001_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9));
v___x_4002_ = l_Lean_addMacroScope(v_quotContext_3988_, v___x_4001_, v_currMacroScope_3989_);
v___x_4003_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_4004_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4004_, 0, v_a_3999_);
lean_ctor_set(v___x_4004_, 1, v___x_4000_);
lean_ctor_set(v___x_4004_, 2, v___x_4002_);
lean_ctor_set(v___x_4004_, 3, v___x_4003_);
v___x_4005_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_4005_);
v___x_4007_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13);
v___x_4008_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14));
v___x_4009_ = l_Lean_addMacroScope(v_quotContext_3988_, v___x_4008_, v_currMacroScope_3989_);
v___x_4010_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16));
v___x_4011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4011_, 0, v_a_4006_);
lean_ctor_set(v___x_4011_, 1, v___x_4007_);
lean_ctor_set(v___x_4011_, 2, v___x_4009_);
lean_ctor_set(v___x_4011_, 3, v___x_4010_);
v___x_4012_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref(v___x_4012_);
v___x_4014_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18);
v___x_4015_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4016_ = l_Lean_addMacroScope(v_quotContext_3988_, v___x_4015_, v_currMacroScope_3989_);
v___x_4017_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4018_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4018_, 0, v_a_4013_);
lean_ctor_set(v___x_4018_, 1, v___x_4014_);
lean_ctor_set(v___x_4018_, 2, v___x_4016_);
lean_ctor_set(v___x_4018_, 3, v___x_4017_);
v___x_4019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
lean_ctor_set(v___x_4019_, 1, v___x_3995_);
v___x_4020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4011_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4004_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_3997_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
v___x_4023_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_4022_, v___x_3995_);
v_sz_4024_ = lean_array_size(v_use_3934_);
v___x_4025_ = ((size_t)0ULL);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_4024_, v___x_4025_, v_use_3934_, v___y_3984_, v___y_3985_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4030_ = lean_array_get_size(v_a_4027_);
v___x_4031_ = lean_nat_dec_lt(v___x_4028_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_dec(v_a_4027_);
v___y_3967_ = v___y_3984_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___x_3995_;
v___y_3970_ = v___y_3985_;
v___y_3971_ = v___y_3983_;
v___y_3972_ = v___x_4023_;
v___y_3973_ = v___x_4029_;
goto v___jp_3966_;
}
else
{
size_t v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_usize_of_nat(v___x_4030_);
v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4027_, v___x_4025_, v___x_4032_, v___x_4029_);
lean_dec(v_a_4027_);
v___y_3967_ = v___y_3984_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___x_3995_;
v___y_3970_ = v___y_3985_;
v___y_3971_ = v___y_3983_;
v___y_3972_ = v___x_4023_;
v___y_3973_ = v___x_4033_;
goto v___jp_3966_;
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_dec(v___x_4023_);
lean_dec_ref(v___f_3965_);
lean_dec(v_remove_3933_);
lean_dec(v_add_3932_);
v_a_4034_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4026_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4026_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SolveByElim_mkAssumptionSet_0interp(lean_interpreter_value* stack)
{
uint8_t v_noDefaults_3930_ = stack[0].m_num;
uint8_t v_star_3931_ = stack[1].m_num;
lean_object* v_add_3932_ = stack[2].m_obj;
lean_object* v_remove_3933_ = stack[3].m_obj;
lean_object* v_use_3934_ = stack[4].m_obj;
lean_object* v_a_3935_ = stack[5].m_obj;
lean_object* v_a_3936_ = stack[6].m_obj;
lean_object* v_a_3937_ = stack[7].m_obj;
lean_object* v_a_3938_ = stack[8].m_obj;
lean_object* v_res_4052_;
v_res_4052_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_3930_, v_star_3931_, v_add_3932_, v_remove_3933_, v_use_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
stack->m_obj
 = v_res_4052_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4053_, lean_object* v_star_4054_, lean_object* v_add_4055_, lean_object* v_remove_4056_, lean_object* v_use_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
uint8_t v_noDefaults_boxed_4063_; uint8_t v_star_boxed_4064_; lean_object* v_res_4065_; 
v_noDefaults_boxed_4063_ = lean_unbox(v_noDefaults_4053_);
v_star_boxed_4064_ = lean_unbox(v_star_4054_);
v_res_4065_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4063_, v_star_boxed_4064_, v_add_4055_, v_remove_4056_, v_use_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
return v_res_4065_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t v_sz_4066_, size_t v_i_4067_, lean_object* v_bs_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_4066_, v_i_4067_, v_bs_4068_, v___y_4071_, v___y_4072_);
return v___x_4074_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4066_ = stack[0].m_num;
size_t v_i_4067_ = stack[1].m_num;
lean_object* v_bs_4068_ = stack[2].m_obj;
lean_object* v___y_4069_ = stack[3].m_obj;
lean_object* v___y_4070_ = stack[4].m_obj;
lean_object* v___y_4071_ = stack[5].m_obj;
lean_object* v___y_4072_ = stack[6].m_obj;
lean_object* v_res_4075_;
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_4066_, v_i_4067_, v_bs_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
stack->m_obj
 = v_res_4075_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object* v_sz_4076_, lean_object* v_i_4077_, lean_object* v_bs_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
size_t v_sz_boxed_4084_; size_t v_i_boxed_4085_; lean_object* v_res_4086_; 
v_sz_boxed_4084_ = lean_unbox_usize(v_sz_4076_);
lean_dec(v_sz_4076_);
v_i_boxed_4085_ = lean_unbox_usize(v_i_4077_);
lean_dec(v_i_4077_);
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_boxed_4084_, v_i_boxed_4085_, v_bs_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
return v_res_4086_;
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

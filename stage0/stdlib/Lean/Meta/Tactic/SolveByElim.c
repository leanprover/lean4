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
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
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
uint8_t v___x_13738__boxed_300_; uint8_t v___x_13739__boxed_301_; lean_object* v_res_302_; 
v___x_13738__boxed_300_ = lean_unbox(v___x_291_);
v___x_13739__boxed_301_ = lean_unbox(v___x_292_);
v_res_302_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13738__boxed_300_, v___x_13739__boxed_301_, v_x_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
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
lean_object* v_toCold_355_; lean_object* v_currRecDepth_356_; lean_object* v_ref_357_; uint16_t v_optionFlags_358_; uint8_t v_suppressElabErrors_359_; uint8_t v_checkDeprecated_360_; uint8_t v_isRecordingDeps_361_; lean_object* v_ref_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_traceState_365_; lean_object* v_traces_366_; lean_object* v___x_367_; size_t v_sz_368_; size_t v___x_369_; lean_object* v___x_370_; lean_object* v_msg_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_411_; 
v_toCold_355_ = lean_ctor_get(v___y_352_, 0);
v_currRecDepth_356_ = lean_ctor_get(v___y_352_, 1);
v_ref_357_ = lean_ctor_get(v___y_352_, 2);
v_optionFlags_358_ = lean_ctor_get_uint16(v___y_352_, sizeof(void*)*3);
v_suppressElabErrors_359_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 2);
v_checkDeprecated_360_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 3);
v_isRecordingDeps_361_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*3 + 4);
v_ref_362_ = l_Lean_replaceRef(v_ref_348_, v_ref_357_);
lean_inc(v_currRecDepth_356_);
lean_inc_ref(v_toCold_355_);
v___x_363_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_363_, 0, v_toCold_355_);
lean_ctor_set(v___x_363_, 1, v_currRecDepth_356_);
lean_ctor_set(v___x_363_, 2, v_ref_362_);
lean_ctor_set_uint16(v___x_363_, sizeof(void*)*3, v_optionFlags_358_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*3 + 2, v_suppressElabErrors_359_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*3 + 3, v_checkDeprecated_360_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*3 + 4, v_isRecordingDeps_361_);
v___x_364_ = lean_st_ref_get(v___y_353_);
v_traceState_365_ = lean_ctor_get(v___x_364_, 4);
lean_inc_ref(v_traceState_365_);
lean_dec(v___x_364_);
v_traces_366_ = lean_ctor_get(v_traceState_365_, 0);
lean_inc_ref(v_traces_366_);
lean_dec_ref(v_traceState_365_);
v___x_367_ = l_Lean_PersistentArray_toArray___redArg(v_traces_366_);
lean_dec_ref(v_traces_366_);
v_sz_368_ = lean_array_size(v___x_367_);
v___x_369_ = ((size_t)0ULL);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_368_, v___x_369_, v___x_367_);
v_msg_371_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_371_, 0, v_data_347_);
lean_ctor_set(v_msg_371_, 1, v_msg_349_);
lean_ctor_set(v_msg_371_, 2, v___x_370_);
v___x_372_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_371_, v___y_350_, v___y_351_, v___x_363_, v___y_353_);
lean_dec_ref_known(v___x_363_, 3);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_411_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_411_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_411_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v_traceState_378_; lean_object* v_env_379_; lean_object* v_nextMacroScope_380_; lean_object* v_ngen_381_; lean_object* v_auxDeclNGen_382_; lean_object* v_cache_383_; lean_object* v_recordedDeps_384_; lean_object* v_messages_385_; lean_object* v_infoState_386_; lean_object* v_snapshotTasks_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_410_; 
v___x_377_ = lean_st_ref_take(v___y_353_);
v_traceState_378_ = lean_ctor_get(v___x_377_, 4);
v_env_379_ = lean_ctor_get(v___x_377_, 0);
v_nextMacroScope_380_ = lean_ctor_get(v___x_377_, 1);
v_ngen_381_ = lean_ctor_get(v___x_377_, 2);
v_auxDeclNGen_382_ = lean_ctor_get(v___x_377_, 3);
v_cache_383_ = lean_ctor_get(v___x_377_, 5);
v_recordedDeps_384_ = lean_ctor_get(v___x_377_, 6);
v_messages_385_ = lean_ctor_get(v___x_377_, 7);
v_infoState_386_ = lean_ctor_get(v___x_377_, 8);
v_snapshotTasks_387_ = lean_ctor_get(v___x_377_, 9);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_410_ == 0)
{
v___x_389_ = v___x_377_;
v_isShared_390_ = v_isSharedCheck_410_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snapshotTasks_387_);
lean_inc(v_infoState_386_);
lean_inc(v_messages_385_);
lean_inc(v_recordedDeps_384_);
lean_inc(v_cache_383_);
lean_inc(v_traceState_378_);
lean_inc(v_auxDeclNGen_382_);
lean_inc(v_ngen_381_);
lean_inc(v_nextMacroScope_380_);
lean_inc(v_env_379_);
lean_dec(v___x_377_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_410_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint64_t v_tid_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_408_; 
v_tid_391_ = lean_ctor_get_uint64(v_traceState_378_, sizeof(void*)*1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_traceState_378_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v_traceState_378_, 0);
lean_dec(v_unused_409_);
v___x_393_ = v_traceState_378_;
v_isShared_394_ = v_isSharedCheck_408_;
goto v_resetjp_392_;
}
else
{
lean_dec(v_traceState_378_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_408_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_ref_348_);
lean_ctor_set(v___x_396_, 1, v_a_373_);
v___x_397_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_346_, v___x_396_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_397_);
lean_ctor_set_uint64(v_reuseFailAlloc_407_, sizeof(void*)*1, v_tid_391_);
v___x_399_ = v_reuseFailAlloc_407_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 4, v___x_399_);
v___x_401_ = v___x_389_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_env_379_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_nextMacroScope_380_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_ngen_381_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_auxDeclNGen_382_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_406_, 5, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_406_, 6, v_recordedDeps_384_);
lean_ctor_set(v_reuseFailAlloc_406_, 7, v_messages_385_);
lean_ctor_set(v_reuseFailAlloc_406_, 8, v_infoState_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 9, v_snapshotTasks_387_);
v___x_401_ = v_reuseFailAlloc_406_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_st_ref_put(v___y_353_, v___x_401_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_395_);
v___x_404_ = v___x_375_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_395_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_412_, lean_object* v_data_413_, lean_object* v_ref_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_412_, v_data_413_, v_ref_414_, v_msg_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_422_){
_start:
{
if (lean_obj_tag(v_e_422_) == 0)
{
uint8_t v___x_423_; 
v___x_423_ = 2;
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_425_);
lean_dec_ref(v_e_425_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_428_, lean_object* v_opt_429_){
_start:
{
lean_object* v_name_430_; lean_object* v_defValue_431_; lean_object* v_map_432_; lean_object* v___x_433_; 
v_name_430_ = lean_ctor_get(v_opt_429_, 0);
v_defValue_431_ = lean_ctor_get(v_opt_429_, 1);
v_map_432_ = lean_ctor_get(v_opts_428_, 0);
v___x_433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_432_, v_name_430_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_inc(v_defValue_431_);
return v_defValue_431_;
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_433_, 1);
if (lean_obj_tag(v_val_434_) == 3)
{
lean_object* v_v_435_; 
v_v_435_ = lean_ctor_get(v_val_434_, 0);
lean_inc(v_v_435_);
lean_dec_ref_known(v_val_434_, 1);
return v_v_435_;
}
else
{
lean_dec(v_val_434_);
lean_inc(v_defValue_431_);
return v_defValue_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_436_, lean_object* v_opt_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_436_, v_opt_437_);
lean_dec_ref(v_opt_437_);
lean_dec_ref(v_opts_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v_x_439_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v_x_439_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v_x_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 1);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v_x_439_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v_x_439_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v_x_439_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 0);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_457_);
return v_res_459_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_460_; double v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_float_of_nat(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_465_; double v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(1000u);
v___x_466_ = lean_float_of_nat(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_467_, uint8_t v_collapsed_468_, lean_object* v_tag_469_, lean_object* v_opts_470_, uint8_t v_clsEnabled_471_, lean_object* v_oldTraces_472_, lean_object* v_msg_473_, lean_object* v_resStartStop_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v_data_485_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___y_501_; lean_object* v_a_502_; uint8_t v___y_517_; double v___y_549_; 
v_fst_480_ = lean_ctor_get(v_resStartStop_474_, 0);
lean_inc(v_fst_480_);
v_snd_481_ = lean_ctor_get(v_resStartStop_474_, 1);
lean_inc(v_snd_481_);
lean_dec_ref(v_resStartStop_474_);
v_fst_496_ = lean_ctor_get(v_snd_481_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v_snd_481_, 1);
lean_inc(v_snd_497_);
lean_dec(v_snd_481_);
v___x_498_ = l_Lean_trace_profiler;
v___x_499_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_470_, v___x_498_);
if (v___x_499_ == 0)
{
v___y_517_ = v___x_499_;
goto v___jp_516_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = l_Lean_trace_profiler_useHeartbeats;
v___x_555_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_470_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; double v___x_558_; double v___x_559_; double v___x_560_; 
v___x_556_ = l_Lean_trace_profiler_threshold;
v___x_557_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_470_, v___x_556_);
v___x_558_ = lean_float_of_nat(v___x_557_);
v___x_559_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_560_ = lean_float_div(v___x_558_, v___x_559_);
v___y_549_ = v___x_560_;
goto v___jp_548_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; double v___x_563_; 
v___x_561_ = l_Lean_trace_profiler_threshold;
v___x_562_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_470_, v___x_561_);
v___x_563_ = lean_float_of_nat(v___x_562_);
v___y_549_ = v___x_563_;
goto v___jp_548_;
}
}
v___jp_482_:
{
lean_object* v___x_486_; 
lean_inc(v___y_483_);
v___x_486_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_472_, v_data_485_, v___y_483_, v___y_484_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v___x_487_; 
lean_dec_ref_known(v___x_486_, 1);
v___x_487_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_480_);
return v___x_487_;
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_fst_480_);
v_a_488_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_486_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
v___jp_500_:
{
uint8_t v_result_503_; lean_object* v___x_504_; lean_object* v___x_505_; double v___x_506_; lean_object* v_data_507_; 
v_result_503_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_480_);
v___x_504_ = lean_box(v_result_503_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_469_);
lean_inc_ref(v___x_505_);
lean_inc(v_cls_467_);
v_data_507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_507_, 0, v_cls_467_);
lean_ctor_set(v_data_507_, 1, v___x_505_);
lean_ctor_set(v_data_507_, 2, v_tag_469_);
lean_ctor_set_float(v_data_507_, sizeof(void*)*3, v___x_506_);
lean_ctor_set_float(v_data_507_, sizeof(void*)*3 + 8, v___x_506_);
lean_ctor_set_uint8(v_data_507_, sizeof(void*)*3 + 16, v_collapsed_468_);
if (v___x_499_ == 0)
{
lean_dec_ref_known(v___x_505_, 1);
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
lean_dec_ref(v_tag_469_);
lean_dec(v_cls_467_);
v___y_483_ = v___y_501_;
v___y_484_ = v_a_502_;
v_data_485_ = v_data_507_;
goto v___jp_482_;
}
else
{
lean_object* v_data_508_; double v___x_509_; double v___x_510_; 
lean_dec_ref_known(v_data_507_, 3);
v_data_508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_508_, 0, v_cls_467_);
lean_ctor_set(v_data_508_, 1, v___x_505_);
lean_ctor_set(v_data_508_, 2, v_tag_469_);
v___x_509_ = lean_unbox_float(v_fst_496_);
lean_dec(v_fst_496_);
lean_ctor_set_float(v_data_508_, sizeof(void*)*3, v___x_509_);
v___x_510_ = lean_unbox_float(v_snd_497_);
lean_dec(v_snd_497_);
lean_ctor_set_float(v_data_508_, sizeof(void*)*3 + 8, v___x_510_);
lean_ctor_set_uint8(v_data_508_, sizeof(void*)*3 + 16, v_collapsed_468_);
v___y_483_ = v___y_501_;
v___y_484_ = v_a_502_;
v_data_485_ = v_data_508_;
goto v___jp_482_;
}
}
v___jp_511_:
{
lean_object* v_ref_512_; lean_object* v___x_513_; 
v_ref_512_ = lean_ctor_get(v___y_477_, 2);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
lean_inc(v___y_476_);
lean_inc_ref(v___y_475_);
lean_inc(v_fst_480_);
v___x_513_ = lean_apply_6(v_msg_473_, v_fst_480_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, lean_box(0));
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___y_501_ = v_ref_512_;
v_a_502_ = v_a_514_;
goto v___jp_500_;
}
else
{
lean_object* v___x_515_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_501_ = v_ref_512_;
v_a_502_ = v___x_515_;
goto v___jp_500_;
}
}
v___jp_516_:
{
if (v_clsEnabled_471_ == 0)
{
if (v___y_517_ == 0)
{
lean_object* v___x_518_; lean_object* v_traceState_519_; lean_object* v_env_520_; lean_object* v_nextMacroScope_521_; lean_object* v_ngen_522_; lean_object* v_auxDeclNGen_523_; lean_object* v_cache_524_; lean_object* v_recordedDeps_525_; lean_object* v_messages_526_; lean_object* v_infoState_527_; lean_object* v_snapshotTasks_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_snd_497_);
lean_dec(v_fst_496_);
lean_dec_ref(v_msg_473_);
lean_dec_ref(v_tag_469_);
lean_dec(v_cls_467_);
v___x_518_ = lean_st_ref_take(v___y_478_);
v_traceState_519_ = lean_ctor_get(v___x_518_, 4);
v_env_520_ = lean_ctor_get(v___x_518_, 0);
v_nextMacroScope_521_ = lean_ctor_get(v___x_518_, 1);
v_ngen_522_ = lean_ctor_get(v___x_518_, 2);
v_auxDeclNGen_523_ = lean_ctor_get(v___x_518_, 3);
v_cache_524_ = lean_ctor_get(v___x_518_, 5);
v_recordedDeps_525_ = lean_ctor_get(v___x_518_, 6);
v_messages_526_ = lean_ctor_get(v___x_518_, 7);
v_infoState_527_ = lean_ctor_get(v___x_518_, 8);
v_snapshotTasks_528_ = lean_ctor_get(v___x_518_, 9);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_547_ == 0)
{
v___x_530_ = v___x_518_;
v_isShared_531_ = v_isSharedCheck_547_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snapshotTasks_528_);
lean_inc(v_infoState_527_);
lean_inc(v_messages_526_);
lean_inc(v_recordedDeps_525_);
lean_inc(v_cache_524_);
lean_inc(v_traceState_519_);
lean_inc(v_auxDeclNGen_523_);
lean_inc(v_ngen_522_);
lean_inc(v_nextMacroScope_521_);
lean_inc(v_env_520_);
lean_dec(v___x_518_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_547_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint64_t v_tid_532_; lean_object* v_traces_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_546_; 
v_tid_532_ = lean_ctor_get_uint64(v_traceState_519_, sizeof(void*)*1);
v_traces_533_ = lean_ctor_get(v_traceState_519_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_traceState_519_);
if (v_isSharedCheck_546_ == 0)
{
v___x_535_ = v_traceState_519_;
v_isShared_536_ = v_isSharedCheck_546_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_traces_533_);
lean_dec(v_traceState_519_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_546_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_472_, v_traces_533_);
lean_dec_ref(v_traces_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_537_);
lean_ctor_set_uint64(v_reuseFailAlloc_545_, sizeof(void*)*1, v_tid_532_);
v___x_539_ = v_reuseFailAlloc_545_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v___x_539_);
v___x_541_ = v___x_530_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_env_520_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_nextMacroScope_521_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_ngen_522_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_auxDeclNGen_523_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_544_, 5, v_cache_524_);
lean_ctor_set(v_reuseFailAlloc_544_, 6, v_recordedDeps_525_);
lean_ctor_set(v_reuseFailAlloc_544_, 7, v_messages_526_);
lean_ctor_set(v_reuseFailAlloc_544_, 8, v_infoState_527_);
lean_ctor_set(v_reuseFailAlloc_544_, 9, v_snapshotTasks_528_);
v___x_541_ = v_reuseFailAlloc_544_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_st_ref_put(v___y_478_, v___x_541_);
v___x_543_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_480_);
return v___x_543_;
}
}
}
}
}
else
{
goto v___jp_511_;
}
}
else
{
goto v___jp_511_;
}
}
v___jp_548_:
{
double v___x_550_; double v___x_551_; double v___x_552_; uint8_t v___x_553_; 
v___x_550_ = lean_unbox_float(v_snd_497_);
v___x_551_ = lean_unbox_float(v_fst_496_);
v___x_552_ = lean_float_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_float_decLt(v___y_549_, v___x_552_);
v___y_517_ = v___x_553_;
goto v___jp_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_564_, lean_object* v_collapsed_565_, lean_object* v_tag_566_, lean_object* v_opts_567_, lean_object* v_clsEnabled_568_, lean_object* v_oldTraces_569_, lean_object* v_msg_570_, lean_object* v_resStartStop_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_collapsed_boxed_577_; uint8_t v_clsEnabled_boxed_578_; lean_object* v_res_579_; 
v_collapsed_boxed_577_ = lean_unbox(v_collapsed_565_);
v_clsEnabled_boxed_578_ = lean_unbox(v_clsEnabled_568_);
v_res_579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_564_, v_collapsed_boxed_577_, v_tag_566_, v_opts_567_, v_clsEnabled_boxed_578_, v_oldTraces_569_, v_msg_570_, v_resStartStop_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec_ref(v_opts_567_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_x_582_);
return v___x_588_;
}
else
{
lean_object* v_head_589_; lean_object* v_tail_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_614_; 
v_head_589_ = lean_ctor_get(v_x_581_, 0);
v_tail_590_ = lean_ctor_get(v_x_581_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_614_ == 0)
{
v___x_592_ = v_x_581_;
v_isShared_593_ = v_isSharedCheck_614_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_tail_590_);
lean_inc(v_head_589_);
lean_dec(v_x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_614_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; 
lean_inc(v_head_589_);
v___x_594_ = l_Lean_MVarId_inferInstance(v_head_589_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_dec_ref_known(v___x_594_, 1);
lean_del_object(v___x_592_);
lean_dec(v_head_589_);
v_x_581_ = v_tail_590_;
goto _start;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_613_; 
v_a_596_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_613_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_613_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_613_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_Exception_isInterrupt(v_a_596_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
lean_inc(v_a_596_);
v___x_601_ = l_Lean_Exception_isRuntime(v_a_596_);
if (v___x_601_ == 0)
{
lean_del_object(v___x_598_);
lean_dec(v_a_596_);
if (v___x_580_ == 0)
{
lean_del_object(v___x_592_);
lean_dec(v_head_589_);
v_x_581_ = v_tail_590_;
goto _start;
}
else
{
lean_object* v___x_604_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v_x_582_);
v___x_604_ = v___x_592_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_head_589_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_x_582_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
v_x_581_ = v_tail_590_;
v_x_582_ = v___x_604_;
goto _start;
}
}
}
else
{
lean_object* v___x_608_; 
lean_del_object(v___x_592_);
lean_dec(v_tail_590_);
lean_dec(v_head_589_);
lean_dec(v_x_582_);
if (v_isShared_599_ == 0)
{
v___x_608_ = v___x_598_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_596_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v___x_611_; 
lean_del_object(v___x_592_);
lean_dec(v_tail_590_);
lean_dec(v_head_589_);
lean_dec(v_x_582_);
if (v_isShared_599_ == 0)
{
v___x_611_ = v___x_598_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_596_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
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
uint8_t v___x_14167__boxed_623_; lean_object* v_res_624_; 
v___x_14167__boxed_623_ = lean_unbox(v___x_615_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14167__boxed_623_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
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
lean_object* v_head_634_; lean_object* v_tail_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_659_; 
v_head_634_ = lean_ctor_get(v_x_626_, 0);
v_tail_635_ = lean_ctor_get(v_x_626_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_659_ == 0)
{
v___x_637_ = v_x_626_;
v_isShared_638_ = v_isSharedCheck_659_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_tail_635_);
lean_inc(v_head_634_);
lean_dec(v_x_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_659_;
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
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_658_; 
v_a_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_658_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_Exception_isInterrupt(v_a_646_);
if (v___x_650_ == 0)
{
uint8_t v___x_651_; 
lean_inc(v_a_646_);
v___x_651_ = l_Lean_Exception_isRuntime(v_a_646_);
if (v___x_651_ == 0)
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
else
{
lean_object* v___x_656_; 
lean_del_object(v___x_637_);
lean_dec(v_tail_635_);
lean_dec(v_head_634_);
lean_dec(v_x_627_);
if (v_isShared_649_ == 0)
{
v___x_656_ = v___x_648_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_646_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_14246__boxed_668_; lean_object* v_res_669_; 
v___x_14246__boxed_668_ = lean_unbox(v___x_660_);
v_res_669_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14246__boxed_668_, v_x_661_, v_x_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_669_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_673_; double v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1000000000u);
v___x_674_ = lean_float_of_nat(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_675_, lean_object* v_g_676_, lean_object* v_e_677_, lean_object* v_cfg_678_, lean_object* v___x_679_, lean_object* v___x_680_, uint8_t v___x_681_, lean_object* v___x_682_, lean_object* v___f_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_toCold_689_; lean_object* v_options_690_; lean_object* v_inheritedTraceOptions_691_; uint8_t v_hasTrace_692_; lean_object* v___y_694_; 
v_toCold_689_ = lean_ctor_get(v___y_686_, 0);
v_options_690_ = lean_ctor_get(v_toCold_689_, 2);
v_inheritedTraceOptions_691_ = lean_ctor_get(v_toCold_689_, 11);
v_hasTrace_692_ = lean_ctor_get_uint8(v_options_690_, sizeof(void*)*1);
if (v_hasTrace_692_ == 0)
{
lean_object* v___x_715_; uint8_t v_transparency_716_; uint8_t v___x_717_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_680_);
v___x_715_ = l_Lean_Meta_Context_config(v___y_684_);
v_transparency_716_ = lean_ctor_get_uint8(v___x_715_, 9);
lean_dec_ref(v___x_715_);
v___x_717_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_716_, v_transparency_675_);
if (v___x_717_ == 0)
{
lean_object* v_keyedConfig_718_; uint8_t v_trackZetaDelta_719_; lean_object* v_zetaDeltaSet_720_; lean_object* v_lctx_721_; lean_object* v_localInstances_722_; lean_object* v_defEqCtx_x3f_723_; lean_object* v_synthPendingDepth_724_; lean_object* v_customCanUnfoldPredicate_x3f_725_; uint8_t v_univApprox_726_; uint8_t v_inTypeClassResolution_727_; uint8_t v_cacheInferType_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_keyedConfig_718_ = lean_ctor_get(v___y_684_, 0);
v_trackZetaDelta_719_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_720_ = lean_ctor_get(v___y_684_, 1);
v_lctx_721_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_722_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_723_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_724_ = lean_ctor_get(v___y_684_, 5);
v_customCanUnfoldPredicate_x3f_725_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_726_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_727_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_728_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_718_);
v___x_729_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_675_, v_keyedConfig_718_);
lean_inc(v_customCanUnfoldPredicate_x3f_725_);
lean_inc(v_synthPendingDepth_724_);
lean_inc(v_defEqCtx_x3f_723_);
lean_inc_ref(v_localInstances_722_);
lean_inc_ref(v_lctx_721_);
lean_inc(v_zetaDeltaSet_720_);
v___x_730_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_zetaDeltaSet_720_);
lean_ctor_set(v___x_730_, 2, v_lctx_721_);
lean_ctor_set(v___x_730_, 3, v_localInstances_722_);
lean_ctor_set(v___x_730_, 4, v_defEqCtx_x3f_723_);
lean_ctor_set(v___x_730_, 5, v_synthPendingDepth_724_);
lean_ctor_set(v___x_730_, 6, v_customCanUnfoldPredicate_x3f_725_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*7, v_trackZetaDelta_719_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*7 + 1, v_univApprox_726_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*7 + 2, v_inTypeClassResolution_727_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*7 + 3, v_cacheInferType_728_);
v___x_731_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_730_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref_known(v___x_730_, 7);
v___y_694_ = v___x_731_;
goto v___jp_693_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v___y_694_ = v___x_732_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v_a_739_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v_a_778_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_a_790_; lean_object* v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; 
v___x_733_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_680_);
v___x_734_ = l_Lean_Name_append(v___x_733_, v___x_680_);
v___x_735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_691_, v_options_690_, v___x_734_);
lean_dec(v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___y_857_; 
v___x_854_ = l_Lean_trace_profiler;
v___x_855_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_690_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_878_; uint8_t v_transparency_879_; uint8_t v___x_880_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_680_);
v___x_878_ = l_Lean_Meta_Context_config(v___y_684_);
v_transparency_879_ = lean_ctor_get_uint8(v___x_878_, 9);
lean_dec_ref(v___x_878_);
v___x_880_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_879_, v_transparency_675_);
if (v___x_880_ == 0)
{
lean_object* v_keyedConfig_881_; uint8_t v_trackZetaDelta_882_; lean_object* v_zetaDeltaSet_883_; lean_object* v_lctx_884_; lean_object* v_localInstances_885_; lean_object* v_defEqCtx_x3f_886_; lean_object* v_synthPendingDepth_887_; lean_object* v_customCanUnfoldPredicate_x3f_888_; uint8_t v_univApprox_889_; uint8_t v_inTypeClassResolution_890_; uint8_t v_cacheInferType_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_keyedConfig_881_ = lean_ctor_get(v___y_684_, 0);
v_trackZetaDelta_882_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_883_ = lean_ctor_get(v___y_684_, 1);
v_lctx_884_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_885_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_886_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_887_ = lean_ctor_get(v___y_684_, 5);
v_customCanUnfoldPredicate_x3f_888_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_889_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_890_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_891_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_881_);
v___x_892_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_675_, v_keyedConfig_881_);
lean_inc(v_customCanUnfoldPredicate_x3f_888_);
lean_inc(v_synthPendingDepth_887_);
lean_inc(v_defEqCtx_x3f_886_);
lean_inc_ref(v_localInstances_885_);
lean_inc_ref(v_lctx_884_);
lean_inc(v_zetaDeltaSet_883_);
v___x_893_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_zetaDeltaSet_883_);
lean_ctor_set(v___x_893_, 2, v_lctx_884_);
lean_ctor_set(v___x_893_, 3, v_localInstances_885_);
lean_ctor_set(v___x_893_, 4, v_defEqCtx_x3f_886_);
lean_ctor_set(v___x_893_, 5, v_synthPendingDepth_887_);
lean_ctor_set(v___x_893_, 6, v_customCanUnfoldPredicate_x3f_888_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7, v_trackZetaDelta_882_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7 + 1, v_univApprox_889_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7 + 2, v_inTypeClassResolution_890_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7 + 3, v_cacheInferType_891_);
v___x_894_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_893_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref_known(v___x_893_, 7);
v___y_857_ = v___x_894_;
goto v___jp_856_;
}
else
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v___y_857_ = v___x_895_;
goto v___jp_856_;
}
}
else
{
goto v___jp_811_;
}
v___jp_856_:
{
if (lean_obj_tag(v___y_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_a_858_ = lean_ctor_get(v___y_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___y_857_, 1);
v___x_859_ = lean_box(0);
v___x_860_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_855_, v_hasTrace_692_, v_a_858_, v___x_859_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___y_684_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_List_reverse___redArg(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
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
return v___x_860_;
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v___y_684_);
v_a_870_ = lean_ctor_get(v___y_857_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___y_857_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___y_857_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___y_857_);
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
else
{
goto v___jp_811_;
}
v___jp_736_:
{
lean_object* v___x_740_; double v___x_741_; double v___x_742_; double v___x_743_; double v___x_744_; double v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_740_ = lean_io_mono_nanos_now();
v___x_741_ = lean_float_of_nat(v___y_737_);
v___x_742_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_743_ = lean_float_div(v___x_741_, v___x_742_);
v___x_744_ = lean_float_of_nat(v___x_740_);
v___x_745_ = lean_float_div(v___x_744_, v___x_742_);
v___x_746_ = lean_box_float(v___x_743_);
v___x_747_ = lean_box_float(v___x_745_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_a_739_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_680_, v___x_681_, v___x_682_, v_options_690_, v___x_735_, v___y_738_, v___f_683_, v___x_749_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___y_684_);
return v___x_750_;
}
v___jp_751_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_a_754_);
v___y_737_ = v___y_752_;
v___y_738_ = v___y_753_;
v_a_739_ = v___x_755_;
goto v___jp_736_;
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
v___x_763_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_759_, v_hasTrace_692_, v_a_761_, v___x_762_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_772_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_772_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = l_List_reverse___redArg(v_a_764_);
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 1);
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v___y_737_ = v___y_757_;
v___y_738_ = v___y_758_;
v_a_739_ = v___x_770_;
goto v___jp_736_;
}
}
}
else
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_763_, 1);
v___y_752_ = v___y_757_;
v___y_753_ = v___y_758_;
v_a_754_ = v_a_773_;
goto v___jp_751_;
}
}
else
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___y_760_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___y_760_, 1);
v___y_752_ = v___y_757_;
v___y_753_ = v___y_758_;
v_a_754_ = v_a_774_;
goto v___jp_751_;
}
}
v___jp_775_:
{
lean_object* v___x_779_; double v___x_780_; double v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_779_ = lean_io_get_num_heartbeats();
v___x_780_ = lean_float_of_nat(v___y_777_);
v___x_781_ = lean_float_of_nat(v___x_779_);
v___x_782_ = lean_box_float(v___x_780_);
v___x_783_ = lean_box_float(v___x_781_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_778_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_680_, v___x_681_, v___x_682_, v_options_690_, v___x_735_, v___y_776_, v___f_683_, v___x_785_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___y_684_);
return v___x_786_;
}
v___jp_787_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_a_790_);
v___y_776_ = v___y_788_;
v___y_777_ = v___y_789_;
v_a_778_ = v___x_791_;
goto v___jp_775_;
}
v___jp_792_:
{
if (lean_obj_tag(v___y_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v___y_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___y_796_, 1);
v___x_798_ = lean_box(0);
v___x_799_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_794_, v_a_797_, v___x_798_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = l_List_reverse___redArg(v_a_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 1);
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_776_ = v___y_793_;
v___y_777_ = v___y_795_;
v_a_778_ = v___x_806_;
goto v___jp_775_;
}
}
}
else
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_799_, 1);
v___y_788_ = v___y_793_;
v___y_789_ = v___y_795_;
v_a_790_ = v_a_809_;
goto v___jp_787_;
}
}
else
{
lean_object* v_a_810_; 
v_a_810_ = lean_ctor_get(v___y_796_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___y_796_, 1);
v___y_788_ = v___y_793_;
v___y_789_ = v___y_795_;
v_a_790_ = v_a_810_;
goto v___jp_787_;
}
}
v___jp_811_:
{
lean_object* v___x_812_; lean_object* v_a_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_812_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_687_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = l_Lean_trace_profiler_useHeartbeats;
v___x_815_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_690_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v_transparency_818_; uint8_t v___x_819_; 
v___x_816_ = lean_io_mono_nanos_now();
v___x_817_ = l_Lean_Meta_Context_config(v___y_684_);
v_transparency_818_ = lean_ctor_get_uint8(v___x_817_, 9);
lean_dec_ref(v___x_817_);
v___x_819_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_818_, v_transparency_675_);
if (v___x_819_ == 0)
{
lean_object* v_keyedConfig_820_; uint8_t v_trackZetaDelta_821_; lean_object* v_zetaDeltaSet_822_; lean_object* v_lctx_823_; lean_object* v_localInstances_824_; lean_object* v_defEqCtx_x3f_825_; lean_object* v_synthPendingDepth_826_; lean_object* v_customCanUnfoldPredicate_x3f_827_; uint8_t v_univApprox_828_; uint8_t v_inTypeClassResolution_829_; uint8_t v_cacheInferType_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_keyedConfig_820_ = lean_ctor_get(v___y_684_, 0);
v_trackZetaDelta_821_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_822_ = lean_ctor_get(v___y_684_, 1);
v_lctx_823_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_824_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_825_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_826_ = lean_ctor_get(v___y_684_, 5);
v_customCanUnfoldPredicate_x3f_827_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_828_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_829_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_830_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_820_);
v___x_831_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_675_, v_keyedConfig_820_);
lean_inc(v_customCanUnfoldPredicate_x3f_827_);
lean_inc(v_synthPendingDepth_826_);
lean_inc(v_defEqCtx_x3f_825_);
lean_inc_ref(v_localInstances_824_);
lean_inc_ref(v_lctx_823_);
lean_inc(v_zetaDeltaSet_822_);
v___x_832_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_zetaDeltaSet_822_);
lean_ctor_set(v___x_832_, 2, v_lctx_823_);
lean_ctor_set(v___x_832_, 3, v_localInstances_824_);
lean_ctor_set(v___x_832_, 4, v_defEqCtx_x3f_825_);
lean_ctor_set(v___x_832_, 5, v_synthPendingDepth_826_);
lean_ctor_set(v___x_832_, 6, v_customCanUnfoldPredicate_x3f_827_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*7, v_trackZetaDelta_821_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*7 + 1, v_univApprox_828_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*7 + 2, v_inTypeClassResolution_829_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*7 + 3, v_cacheInferType_830_);
v___x_833_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_832_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref_known(v___x_832_, 7);
v___y_757_ = v___x_816_;
v___y_758_ = v_a_813_;
v___y_759_ = v___x_815_;
v___y_760_ = v___x_833_;
goto v___jp_756_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v___y_757_ = v___x_816_;
v___y_758_ = v_a_813_;
v___y_759_ = v___x_815_;
v___y_760_ = v___x_834_;
goto v___jp_756_;
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v_transparency_837_; uint8_t v___x_838_; 
v___x_835_ = lean_io_get_num_heartbeats();
v___x_836_ = l_Lean_Meta_Context_config(v___y_684_);
v_transparency_837_ = lean_ctor_get_uint8(v___x_836_, 9);
lean_dec_ref(v___x_836_);
v___x_838_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_837_, v_transparency_675_);
if (v___x_838_ == 0)
{
lean_object* v_keyedConfig_839_; uint8_t v_trackZetaDelta_840_; lean_object* v_zetaDeltaSet_841_; lean_object* v_lctx_842_; lean_object* v_localInstances_843_; lean_object* v_defEqCtx_x3f_844_; lean_object* v_synthPendingDepth_845_; lean_object* v_customCanUnfoldPredicate_x3f_846_; uint8_t v_univApprox_847_; uint8_t v_inTypeClassResolution_848_; uint8_t v_cacheInferType_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_keyedConfig_839_ = lean_ctor_get(v___y_684_, 0);
v_trackZetaDelta_840_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_841_ = lean_ctor_get(v___y_684_, 1);
v_lctx_842_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_843_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_844_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_845_ = lean_ctor_get(v___y_684_, 5);
v_customCanUnfoldPredicate_x3f_846_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_847_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_848_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_849_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_839_);
v___x_850_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_675_, v_keyedConfig_839_);
lean_inc(v_customCanUnfoldPredicate_x3f_846_);
lean_inc(v_synthPendingDepth_845_);
lean_inc(v_defEqCtx_x3f_844_);
lean_inc_ref(v_localInstances_843_);
lean_inc_ref(v_lctx_842_);
lean_inc(v_zetaDeltaSet_841_);
v___x_851_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_zetaDeltaSet_841_);
lean_ctor_set(v___x_851_, 2, v_lctx_842_);
lean_ctor_set(v___x_851_, 3, v_localInstances_843_);
lean_ctor_set(v___x_851_, 4, v_defEqCtx_x3f_844_);
lean_ctor_set(v___x_851_, 5, v_synthPendingDepth_845_);
lean_ctor_set(v___x_851_, 6, v_customCanUnfoldPredicate_x3f_846_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7, v_trackZetaDelta_840_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7 + 1, v_univApprox_847_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7 + 2, v_inTypeClassResolution_848_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*7 + 3, v_cacheInferType_849_);
v___x_852_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_851_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref_known(v___x_851_, 7);
v___y_793_ = v_a_813_;
v___y_794_ = v___x_815_;
v___y_795_ = v___x_835_;
v___y_796_ = v___x_852_;
goto v___jp_792_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v___y_793_ = v_a_813_;
v___y_794_ = v___x_815_;
v___y_795_ = v___x_835_;
v___y_796_ = v___x_853_;
goto v___jp_792_;
}
}
}
}
v___jp_693_:
{
if (lean_obj_tag(v___y_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_695_ = lean_ctor_get(v___y_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___y_694_, 1);
v___x_696_ = lean_box(0);
v___x_697_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_692_, v_a_695_, v___x_696_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___y_684_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_706_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_706_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = l_List_reverse___redArg(v_a_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
return v___x_697_;
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v___y_684_);
v_a_707_ = lean_ctor_get(v___y_694_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___y_694_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___y_694_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___y_694_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_896_, lean_object* v_g_897_, lean_object* v_e_898_, lean_object* v_cfg_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___f_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v_transparency_boxed_910_; uint8_t v___x_14336__boxed_911_; lean_object* v_res_912_; 
v_transparency_boxed_910_ = lean_unbox(v_transparency_896_);
v___x_14336__boxed_911_ = lean_unbox(v___x_902_);
v_res_912_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_910_, v_g_897_, v_e_898_, v_cfg_899_, v___x_900_, v___x_901_, v___x_14336__boxed_911_, v___x_903_, v___f_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_914_, lean_object* v_g_915_, lean_object* v_cfg_916_, lean_object* v_e_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___f_930_; lean_object* v___x_931_; 
lean_inc_ref(v_e_917_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_923_, 0, v_e_917_);
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_925_ = lean_box(0);
v___x_926_ = 1;
v___x_927_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_928_ = lean_box(v_transparency_914_);
v___x_929_ = lean_box(v___x_926_);
v___f_930_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_930_, 0, v___x_928_);
lean_closure_set(v___f_930_, 1, v_g_915_);
lean_closure_set(v___f_930_, 2, v_e_917_);
lean_closure_set(v___f_930_, 3, v_cfg_916_);
lean_closure_set(v___f_930_, 4, v___x_925_);
lean_closure_set(v___f_930_, 5, v___x_924_);
lean_closure_set(v___f_930_, 6, v___x_929_);
lean_closure_set(v___f_930_, 7, v___x_927_);
lean_closure_set(v___f_930_, 8, v___f_923_);
v___x_931_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_930_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_932_, lean_object* v_g_933_, lean_object* v_cfg_934_, lean_object* v_e_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v_transparency_boxed_941_; lean_object* v_res_942_; 
v_transparency_boxed_941_ = lean_unbox(v_transparency_932_);
v_res_942_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_941_, v_g_933_, v_cfg_934_, v_e_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_943_, uint8_t v_transparency_944_, lean_object* v_lemmas_945_, lean_object* v_g_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(v_transparency_944_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_951_, 0, v___x_950_);
lean_closure_set(v___f_951_, 1, v_g_946_);
lean_closure_set(v___f_951_, 2, v_cfg_943_);
v___x_952_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_945_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_957_, 0, lean_box(0));
lean_closure_set(v___x_957_, 1, lean_box(0));
lean_closure_set(v___x_957_, 2, v___f_951_);
lean_closure_set(v___x_957_, 3, v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v___f_951_);
v_a_962_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_952_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_970_, lean_object* v_transparency_971_, lean_object* v_lemmas_972_, lean_object* v_g_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
uint8_t v_transparency_boxed_977_; lean_object* v_res_978_; 
v_transparency_boxed_977_ = lean_unbox(v_transparency_971_);
v_res_978_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_970_, v_transparency_boxed_977_, v_lemmas_972_, v_g_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec(v_a_974_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_979_, uint8_t v_transparency_980_, lean_object* v_lemmas_981_, lean_object* v_g_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_979_, v_transparency_980_, v_lemmas_981_, v_g_982_, v_a_984_, v_a_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_989_, lean_object* v_transparency_990_, lean_object* v_lemmas_991_, lean_object* v_g_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
uint8_t v_transparency_boxed_998_; lean_object* v_res_999_; 
v_transparency_boxed_998_ = lean_unbox(v_transparency_990_);
v_res_999_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_989_, v_transparency_boxed_998_, v_lemmas_991_, v_g_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_1001_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1008_, v_x_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1016_, uint8_t v_transparency_1017_, lean_object* v_lemmas_1018_, lean_object* v_g_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1016_, v_transparency_1017_, v_lemmas_1018_, v_g_1019_, v_a_1021_, v_a_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = l_Lean_Meta_Iterator_head___redArg(v_a_1026_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1027_;
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1025_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1036_, lean_object* v_transparency_1037_, lean_object* v_lemmas_1038_, lean_object* v_g_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
uint8_t v_transparency_boxed_1045_; lean_object* v_res_1046_; 
v_transparency_boxed_1045_ = lean_unbox(v_transparency_1037_);
v_res_1046_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1036_, v_transparency_boxed_1045_, v_lemmas_1038_, v_g_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1047_){
_start:
{
lean_object* v_toApplyRulesConfig_1048_; lean_object* v_toBacktrackConfig_1049_; 
v_toApplyRulesConfig_1048_ = lean_ctor_get(v_x_1047_, 0);
v_toBacktrackConfig_1049_ = lean_ctor_get(v_toApplyRulesConfig_1048_, 0);
lean_inc_ref(v_toBacktrackConfig_1049_);
return v_toBacktrackConfig_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1050_);
lean_dec_ref(v_x_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1054_, lean_object* v_discharge_1055_, lean_object* v_g_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v_g_1056_);
v___x_1062_ = lean_apply_6(v_test_1054_, v_g_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1073_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_unbox(v_a_1063_);
lean_dec(v_a_1063_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_del_object(v___x_1065_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
v___x_1068_ = lean_apply_6(v_discharge_1055_, v_g_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_dec(v_g_1056_);
lean_dec_ref(v_discharge_1055_);
v___x_1069_ = lean_box(0);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_g_1056_);
lean_dec_ref(v_discharge_1055_);
v_a_1074_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1062_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1062_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1082_, lean_object* v_discharge_1083_, lean_object* v_g_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1082_, v_discharge_1083_, v_g_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1091_, lean_object* v_test_1092_){
_start:
{
lean_object* v_toApplyRulesConfig_1093_; lean_object* v_toBacktrackConfig_1094_; uint8_t v_backtracking_1095_; uint8_t v_intro_1096_; uint8_t v_constructor_1097_; uint8_t v_suggestions_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1130_; 
v_toApplyRulesConfig_1093_ = lean_ctor_get(v_cfg_1091_, 0);
lean_inc_ref(v_toApplyRulesConfig_1093_);
v_toBacktrackConfig_1094_ = lean_ctor_get(v_toApplyRulesConfig_1093_, 0);
lean_inc_ref(v_toBacktrackConfig_1094_);
v_backtracking_1095_ = lean_ctor_get_uint8(v_cfg_1091_, sizeof(void*)*1);
v_intro_1096_ = lean_ctor_get_uint8(v_cfg_1091_, sizeof(void*)*1 + 1);
v_constructor_1097_ = lean_ctor_get_uint8(v_cfg_1091_, sizeof(void*)*1 + 2);
v_suggestions_1098_ = lean_ctor_get_uint8(v_cfg_1091_, sizeof(void*)*1 + 3);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_cfg_1091_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_cfg_1091_, 0);
lean_dec(v_unused_1131_);
v___x_1100_ = v_cfg_1091_;
v_isShared_1101_ = v_isSharedCheck_1130_;
goto v_resetjp_1099_;
}
else
{
lean_dec(v_cfg_1091_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1130_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_toApplyConfig_1102_; uint8_t v_transparency_1103_; uint8_t v_symm_1104_; uint8_t v_exfalso_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1128_; 
v_toApplyConfig_1102_ = lean_ctor_get(v_toApplyRulesConfig_1093_, 1);
v_transparency_1103_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1093_, sizeof(void*)*2);
v_symm_1104_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1093_, sizeof(void*)*2 + 1);
v_exfalso_1105_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1093_, sizeof(void*)*2 + 2);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_toApplyRulesConfig_1093_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_toApplyRulesConfig_1093_, 0);
lean_dec(v_unused_1129_);
v___x_1107_ = v_toApplyRulesConfig_1093_;
v_isShared_1108_ = v_isSharedCheck_1128_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_toApplyConfig_1102_);
lean_dec(v_toApplyRulesConfig_1093_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1128_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_maxDepth_1109_; lean_object* v_proc_1110_; lean_object* v_suspend_1111_; lean_object* v_discharge_1112_; uint8_t v_commitIndependentGoals_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1127_; 
v_maxDepth_1109_ = lean_ctor_get(v_toBacktrackConfig_1094_, 0);
v_proc_1110_ = lean_ctor_get(v_toBacktrackConfig_1094_, 1);
v_suspend_1111_ = lean_ctor_get(v_toBacktrackConfig_1094_, 2);
v_discharge_1112_ = lean_ctor_get(v_toBacktrackConfig_1094_, 3);
v_commitIndependentGoals_1113_ = lean_ctor_get_uint8(v_toBacktrackConfig_1094_, sizeof(void*)*4);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_toBacktrackConfig_1094_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1115_ = v_toBacktrackConfig_1094_;
v_isShared_1116_ = v_isSharedCheck_1127_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_discharge_1112_);
lean_inc(v_suspend_1111_);
lean_inc(v_proc_1110_);
lean_inc(v_maxDepth_1109_);
lean_dec(v_toBacktrackConfig_1094_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1127_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___f_1117_; lean_object* v___x_1119_; 
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1117_, 0, v_test_1092_);
lean_closure_set(v___f_1117_, 1, v_discharge_1112_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 3, v___f_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_maxDepth_1109_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_proc_1110_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_suspend_1111_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v___f_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*4, v_commitIndependentGoals_1113_);
v___x_1119_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1119_);
v___x_1121_ = v___x_1107_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_toApplyConfig_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*2, v_transparency_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*2 + 1, v_symm_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*2 + 2, v_exfalso_1105_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1121_);
v___x_1123_ = v___x_1100_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*1, v_backtracking_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*1 + 1, v_intro_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*1 + 2, v_constructor_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*1 + 3, v_suggestions_1098_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1132_, lean_object* v_proc_1133_, lean_object* v_orig_1134_, lean_object* v_goals_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
if (lean_obj_tag(v_goals_1135_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v_proc_1133_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
v___x_1141_ = lean_apply_7(v_proc_1132_, v_orig_1134_, v_goals_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1141_;
}
else
{
lean_object* v_head_1142_; lean_object* v_tail_1143_; lean_object* v___x_1144_; 
v_head_1142_ = lean_ctor_get(v_goals_1135_, 0);
v_tail_1143_ = lean_ctor_get(v_goals_1135_, 1);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v_head_1142_);
v___x_1144_ = lean_apply_6(v_proc_1133_, v_head_1142_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1154_; 
lean_inc(v_tail_1143_);
lean_dec_ref_known(v_goals_1135_, 2);
lean_dec(v_orig_1134_);
lean_dec_ref(v_proc_1132_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1154_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1154_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = l_List_appendTR___redArg(v_a_1145_, v_tail_1143_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1168_; 
v_a_1155_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1157_ = v___x_1144_;
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1144_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1159_; 
v___x_1159_ = l_Lean_Exception_isInterrupt(v_a_1155_);
if (v___x_1159_ == 0)
{
uint8_t v___x_1160_; 
lean_inc(v_a_1155_);
v___x_1160_ = l_Lean_Exception_isRuntime(v_a_1155_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_del_object(v___x_1157_);
lean_dec(v_a_1155_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
v___x_1161_ = lean_apply_7(v_proc_1132_, v_orig_1134_, v_goals_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1161_;
}
else
{
lean_object* v___x_1163_; 
lean_dec_ref_known(v_goals_1135_, 2);
lean_dec(v_orig_1134_);
lean_dec_ref(v_proc_1132_);
if (v_isShared_1158_ == 0)
{
v___x_1163_ = v___x_1157_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1155_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v___x_1166_; 
lean_dec_ref_known(v_goals_1135_, 2);
lean_dec(v_orig_1134_);
lean_dec_ref(v_proc_1132_);
if (v_isShared_1158_ == 0)
{
v___x_1166_ = v___x_1157_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1155_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1169_, lean_object* v_proc_1170_, lean_object* v_orig_1171_, lean_object* v_goals_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1169_, v_proc_1170_, v_orig_1171_, v_goals_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1179_, lean_object* v_proc_1180_){
_start:
{
lean_object* v_toApplyRulesConfig_1181_; lean_object* v_toBacktrackConfig_1182_; uint8_t v_backtracking_1183_; uint8_t v_intro_1184_; uint8_t v_constructor_1185_; uint8_t v_suggestions_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1218_; 
v_toApplyRulesConfig_1181_ = lean_ctor_get(v_cfg_1179_, 0);
lean_inc_ref(v_toApplyRulesConfig_1181_);
v_toBacktrackConfig_1182_ = lean_ctor_get(v_toApplyRulesConfig_1181_, 0);
lean_inc_ref(v_toBacktrackConfig_1182_);
v_backtracking_1183_ = lean_ctor_get_uint8(v_cfg_1179_, sizeof(void*)*1);
v_intro_1184_ = lean_ctor_get_uint8(v_cfg_1179_, sizeof(void*)*1 + 1);
v_constructor_1185_ = lean_ctor_get_uint8(v_cfg_1179_, sizeof(void*)*1 + 2);
v_suggestions_1186_ = lean_ctor_get_uint8(v_cfg_1179_, sizeof(void*)*1 + 3);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_cfg_1179_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_cfg_1179_, 0);
lean_dec(v_unused_1219_);
v___x_1188_ = v_cfg_1179_;
v_isShared_1189_ = v_isSharedCheck_1218_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_cfg_1179_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1218_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_toApplyConfig_1190_; uint8_t v_transparency_1191_; uint8_t v_symm_1192_; uint8_t v_exfalso_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1216_; 
v_toApplyConfig_1190_ = lean_ctor_get(v_toApplyRulesConfig_1181_, 1);
v_transparency_1191_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1181_, sizeof(void*)*2);
v_symm_1192_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1181_, sizeof(void*)*2 + 1);
v_exfalso_1193_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1181_, sizeof(void*)*2 + 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_toApplyRulesConfig_1181_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v_toApplyRulesConfig_1181_, 0);
lean_dec(v_unused_1217_);
v___x_1195_ = v_toApplyRulesConfig_1181_;
v_isShared_1196_ = v_isSharedCheck_1216_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_toApplyConfig_1190_);
lean_dec(v_toApplyRulesConfig_1181_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1216_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_maxDepth_1197_; lean_object* v_proc_1198_; lean_object* v_suspend_1199_; lean_object* v_discharge_1200_; uint8_t v_commitIndependentGoals_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1215_; 
v_maxDepth_1197_ = lean_ctor_get(v_toBacktrackConfig_1182_, 0);
v_proc_1198_ = lean_ctor_get(v_toBacktrackConfig_1182_, 1);
v_suspend_1199_ = lean_ctor_get(v_toBacktrackConfig_1182_, 2);
v_discharge_1200_ = lean_ctor_get(v_toBacktrackConfig_1182_, 3);
v_commitIndependentGoals_1201_ = lean_ctor_get_uint8(v_toBacktrackConfig_1182_, sizeof(void*)*4);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_toBacktrackConfig_1182_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1203_ = v_toBacktrackConfig_1182_;
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_discharge_1200_);
lean_inc(v_suspend_1199_);
lean_inc(v_proc_1198_);
lean_inc(v_maxDepth_1197_);
lean_dec(v_toBacktrackConfig_1182_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___f_1205_; lean_object* v___x_1207_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1205_, 0, v_proc_1198_);
lean_closure_set(v___f_1205_, 1, v_proc_1180_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___f_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_maxDepth_1197_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___f_1205_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_suspend_1199_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_discharge_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*4, v_commitIndependentGoals_1201_);
v___x_1207_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1207_);
v___x_1209_ = v___x_1195_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_toApplyConfig_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*2, v_transparency_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*2 + 1, v_symm_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*2 + 2, v_exfalso_1193_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1209_);
v___x_1211_ = v___x_1188_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*1, v_backtracking_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*1 + 1, v_intro_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*1 + 2, v_constructor_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*1 + 3, v_suggestions_1186_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = 1;
v___x_1227_ = l_Lean_Meta_intro1Core(v_g_1220_, v___x_1226_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1245_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1245_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1245_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_snd_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
v_snd_1232_ = lean_ctor_get(v_a_1228_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_a_1228_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_a_1228_, 0);
lean_dec(v_unused_1244_);
v___x_1234_ = v_a_1228_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snd_1232_);
lean_dec(v_a_1228_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_box(0);
if (v_isShared_1235_ == 0)
{
lean_ctor_set_tag(v___x_1234_, 1);
lean_ctor_set(v___x_1234_, 1, v___x_1236_);
lean_ctor_set(v___x_1234_, 0, v_snd_1232_);
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_snd_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1238_);
v___x_1240_ = v___x_1230_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1227_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1227_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1262_){
_start:
{
lean_object* v___f_1263_; lean_object* v___x_1264_; 
v___f_1263_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1264_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1262_, v___f_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_ks_1269_; lean_object* v_vs_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1294_; 
v_ks_1269_ = lean_ctor_get(v_x_1265_, 0);
v_vs_1270_ = lean_ctor_get(v_x_1265_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1272_ = v_x_1265_;
v_isShared_1273_ = v_isSharedCheck_1294_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_vs_1270_);
lean_inc(v_ks_1269_);
lean_dec(v_x_1265_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1294_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_array_get_size(v_ks_1269_);
v___x_1275_ = lean_nat_dec_lt(v_x_1266_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec(v_x_1266_);
v___x_1276_ = lean_array_push(v_ks_1269_, v_x_1267_);
v___x_1277_ = lean_array_push(v_vs_1270_, v_x_1268_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1277_);
lean_ctor_set(v___x_1272_, 0, v___x_1276_);
v___x_1279_ = v___x_1272_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
else
{
lean_object* v_k_x27_1281_; uint8_t v___x_1282_; 
v_k_x27_1281_ = lean_array_fget_borrowed(v_ks_1269_, v_x_1266_);
v___x_1282_ = l_Lean_instBEqMVarId_beq(v_x_1267_, v_k_x27_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1284_; 
if (v_isShared_1273_ == 0)
{
v___x_1284_ = v___x_1272_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_ks_1269_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_vs_1270_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_add(v_x_1266_, v___x_1285_);
lean_dec(v_x_1266_);
v_x_1265_ = v___x_1284_;
v_x_1266_ = v___x_1286_;
goto _start;
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = lean_array_fset(v_ks_1269_, v_x_1266_, v_x_1267_);
v___x_1290_ = lean_array_fset(v_vs_1270_, v_x_1266_, v_x_1268_);
lean_dec(v_x_1266_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1290_);
lean_ctor_set(v___x_1272_, 0, v___x_1289_);
v___x_1292_ = v___x_1272_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1295_, lean_object* v_k_1296_, lean_object* v_v_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1295_, v___x_1298_, v_k_1296_, v_v_1297_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1301_, size_t v_x_1302_, size_t v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 0)
{
lean_object* v_es_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v_j_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_es_1306_ = lean_ctor_get(v_x_1301_, 0);
v___x_1307_ = ((size_t)31ULL);
v___x_1308_ = lean_usize_land(v_x_1302_, v___x_1307_);
v_j_1309_ = lean_usize_to_nat(v___x_1308_);
v___x_1310_ = lean_array_get_size(v_es_1306_);
v___x_1311_ = lean_nat_dec_lt(v_j_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec(v_j_1309_);
lean_dec(v_x_1305_);
lean_dec(v_x_1304_);
return v_x_1301_;
}
else
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1350_; 
lean_inc_ref(v_es_1306_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v_x_1301_, 0);
lean_dec(v_unused_1351_);
v___x_1313_ = v_x_1301_;
v_isShared_1314_ = v_isSharedCheck_1350_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v_x_1301_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1350_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_v_1315_; lean_object* v___x_1316_; lean_object* v_xs_x27_1317_; lean_object* v___y_1319_; 
v_v_1315_ = lean_array_fget(v_es_1306_, v_j_1309_);
v___x_1316_ = lean_box(0);
v_xs_x27_1317_ = lean_array_fset(v_es_1306_, v_j_1309_, v___x_1316_);
switch(lean_obj_tag(v_v_1315_))
{
case 0:
{
lean_object* v_key_1324_; lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1335_; 
v_key_1324_ = lean_ctor_get(v_v_1315_, 0);
v_val_1325_ = lean_ctor_get(v_v_1315_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_v_1315_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1327_ = v_v_1315_;
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_inc(v_key_1324_);
lean_dec(v_v_1315_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
uint8_t v___x_1329_; 
v___x_1329_ = l_Lean_instBEqMVarId_beq(v_x_1304_, v_key_1324_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_del_object(v___x_1327_);
v___x_1330_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1324_, v_val_1325_, v_x_1304_, v_x_1305_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
v___y_1319_ = v___x_1331_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_val_1325_);
lean_dec(v_key_1324_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_x_1305_);
lean_ctor_set(v___x_1327_, 0, v_x_1304_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_x_1304_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_x_1305_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
v___y_1319_ = v___x_1333_;
goto v___jp_1318_;
}
}
}
}
case 1:
{
lean_object* v_node_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1348_; 
v_node_1336_ = lean_ctor_get(v_v_1315_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_v_1315_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1338_ = v_v_1315_;
v_isShared_1339_ = v_isSharedCheck_1348_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_node_1336_);
lean_dec(v_v_1315_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1348_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1340_ = ((size_t)5ULL);
v___x_1341_ = lean_usize_shift_right(v_x_1302_, v___x_1340_);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_x_1303_, v___x_1342_);
v___x_1344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1336_, v___x_1341_, v___x_1343_, v_x_1304_, v_x_1305_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1344_);
v___x_1346_ = v___x_1338_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v___y_1319_ = v___x_1346_;
goto v___jp_1318_;
}
}
}
default: 
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_x_1304_);
lean_ctor_set(v___x_1349_, 1, v_x_1305_);
v___y_1319_ = v___x_1349_;
goto v___jp_1318_;
}
}
v___jp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_array_fset(v_xs_x27_1317_, v_j_1309_, v___y_1319_);
lean_dec(v_j_1309_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1320_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_ks_1352_; lean_object* v_vs_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1371_; 
v_ks_1352_ = lean_ctor_get(v_x_1301_, 0);
v_vs_1353_ = lean_ctor_get(v_x_1301_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1355_ = v_x_1301_;
v_isShared_1356_ = v_isSharedCheck_1371_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_vs_1353_);
lean_inc(v_ks_1352_);
lean_dec(v_x_1301_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1371_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_ks_1352_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_vs_1353_);
v___x_1358_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v_newNode_1359_; size_t v___x_1360_; uint8_t v___x_1361_; 
v_newNode_1359_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1358_, v_x_1304_, v_x_1305_);
v___x_1360_ = ((size_t)7ULL);
v___x_1361_ = lean_usize_dec_le(v___x_1360_, v_x_1303_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1359_);
v___x_1363_ = lean_unsigned_to_nat(4u);
v___x_1364_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
if (v___x_1364_ == 0)
{
lean_object* v_ks_1365_; lean_object* v_vs_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_ks_1365_ = lean_ctor_get(v_newNode_1359_, 0);
lean_inc_ref(v_ks_1365_);
v_vs_1366_ = lean_ctor_get(v_newNode_1359_, 1);
lean_inc_ref(v_vs_1366_);
lean_dec_ref(v_newNode_1359_);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1303_, v_ks_1365_, v_vs_1366_, v___x_1367_, v___x_1368_);
lean_dec_ref(v_vs_1366_);
lean_dec_ref(v_ks_1365_);
return v___x_1369_;
}
else
{
return v_newNode_1359_;
}
}
else
{
return v_newNode_1359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1372_, lean_object* v_keys_1373_, lean_object* v_vals_1374_, lean_object* v_i_1375_, lean_object* v_entries_1376_){
_start:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_keys_1373_);
v___x_1378_ = lean_nat_dec_lt(v_i_1375_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec(v_i_1375_);
return v_entries_1376_;
}
else
{
lean_object* v_k_1379_; lean_object* v_v_1380_; uint64_t v___x_1381_; size_t v_h_1382_; size_t v___x_1383_; lean_object* v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; size_t v_h_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_k_1379_ = lean_array_fget_borrowed(v_keys_1373_, v_i_1375_);
v_v_1380_ = lean_array_fget_borrowed(v_vals_1374_, v_i_1375_);
v___x_1381_ = l_Lean_instHashableMVarId_hash(v_k_1379_);
v_h_1382_ = lean_uint64_to_usize(v___x_1381_);
v___x_1383_ = ((size_t)5ULL);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_sub(v_depth_1372_, v___x_1385_);
v___x_1387_ = lean_usize_mul(v___x_1383_, v___x_1386_);
v_h_1388_ = lean_usize_shift_right(v_h_1382_, v___x_1387_);
v___x_1389_ = lean_nat_add(v_i_1375_, v___x_1384_);
lean_dec(v_i_1375_);
lean_inc(v_v_1380_);
lean_inc(v_k_1379_);
v___x_1390_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1376_, v_h_1388_, v_depth_1372_, v_k_1379_, v_v_1380_);
v_i_1375_ = v___x_1389_;
v_entries_1376_ = v___x_1390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1392_, lean_object* v_keys_1393_, lean_object* v_vals_1394_, lean_object* v_i_1395_, lean_object* v_entries_1396_){
_start:
{
size_t v_depth_boxed_1397_; lean_object* v_res_1398_; 
v_depth_boxed_1397_ = lean_unbox_usize(v_depth_1392_);
lean_dec(v_depth_1392_);
v_res_1398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1397_, v_keys_1393_, v_vals_1394_, v_i_1395_, v_entries_1396_);
lean_dec_ref(v_vals_1394_);
lean_dec_ref(v_keys_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
size_t v_x_839__boxed_1404_; size_t v_x_840__boxed_1405_; lean_object* v_res_1406_; 
v_x_839__boxed_1404_ = lean_unbox_usize(v_x_1400_);
lean_dec(v_x_1400_);
v_x_840__boxed_1405_ = lean_unbox_usize(v_x_1401_);
lean_dec(v_x_1401_);
v_res_1406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1399_, v_x_839__boxed_1404_, v_x_840__boxed_1405_, v_x_1402_, v_x_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
uint64_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = l_Lean_instHashableMVarId_hash(v_x_1408_);
v___x_1411_ = lean_uint64_to_usize(v___x_1410_);
v___x_1412_ = ((size_t)1ULL);
v___x_1413_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1407_, v___x_1411_, v___x_1412_, v_x_1408_, v_x_1409_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1414_, lean_object* v_val_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; lean_object* v_mctx_1419_; lean_object* v_cache_1420_; lean_object* v_zetaDeltaFVarIds_1421_; lean_object* v_postponed_1422_; lean_object* v_diag_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1453_; 
v___x_1418_ = lean_st_ref_take(v___y_1416_);
v_mctx_1419_ = lean_ctor_get(v___x_1418_, 0);
v_cache_1420_ = lean_ctor_get(v___x_1418_, 1);
v_zetaDeltaFVarIds_1421_ = lean_ctor_get(v___x_1418_, 2);
v_postponed_1422_ = lean_ctor_get(v___x_1418_, 3);
v_diag_1423_ = lean_ctor_get(v___x_1418_, 4);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1425_ = v___x_1418_;
v_isShared_1426_ = v_isSharedCheck_1453_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_diag_1423_);
lean_inc(v_postponed_1422_);
lean_inc(v_zetaDeltaFVarIds_1421_);
lean_inc(v_cache_1420_);
lean_inc(v_mctx_1419_);
lean_dec(v___x_1418_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1453_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_depth_1427_; lean_object* v_levelAssignDepth_1428_; lean_object* v_lmvarCounter_1429_; lean_object* v_mvarCounter_1430_; lean_object* v_lDecls_1431_; lean_object* v_decls_1432_; lean_object* v_userNames_1433_; lean_object* v_lAssignment_1434_; lean_object* v_eAssignment_1435_; lean_object* v_dAssignment_1436_; lean_object* v_instanceTypedMVars_1437_; lean_object* v_synthNormMemo_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1452_; 
v_depth_1427_ = lean_ctor_get(v_mctx_1419_, 0);
v_levelAssignDepth_1428_ = lean_ctor_get(v_mctx_1419_, 1);
v_lmvarCounter_1429_ = lean_ctor_get(v_mctx_1419_, 2);
v_mvarCounter_1430_ = lean_ctor_get(v_mctx_1419_, 3);
v_lDecls_1431_ = lean_ctor_get(v_mctx_1419_, 4);
v_decls_1432_ = lean_ctor_get(v_mctx_1419_, 5);
v_userNames_1433_ = lean_ctor_get(v_mctx_1419_, 6);
v_lAssignment_1434_ = lean_ctor_get(v_mctx_1419_, 7);
v_eAssignment_1435_ = lean_ctor_get(v_mctx_1419_, 8);
v_dAssignment_1436_ = lean_ctor_get(v_mctx_1419_, 9);
v_instanceTypedMVars_1437_ = lean_ctor_get(v_mctx_1419_, 10);
v_synthNormMemo_1438_ = lean_ctor_get(v_mctx_1419_, 11);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_mctx_1419_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1440_ = v_mctx_1419_;
v_isShared_1441_ = v_isSharedCheck_1452_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_synthNormMemo_1438_);
lean_inc(v_instanceTypedMVars_1437_);
lean_inc(v_dAssignment_1436_);
lean_inc(v_eAssignment_1435_);
lean_inc(v_lAssignment_1434_);
lean_inc(v_userNames_1433_);
lean_inc(v_decls_1432_);
lean_inc(v_lDecls_1431_);
lean_inc(v_mvarCounter_1430_);
lean_inc(v_lmvarCounter_1429_);
lean_inc(v_levelAssignDepth_1428_);
lean_inc(v_depth_1427_);
lean_dec(v_mctx_1419_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1452_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1442_ = lean_box(0);
v___x_1443_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1435_, v_mvarId_1414_, v_val_1415_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 8, v___x_1443_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_depth_1427_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_levelAssignDepth_1428_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_lmvarCounter_1429_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_mvarCounter_1430_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_lDecls_1431_);
lean_ctor_set(v_reuseFailAlloc_1451_, 5, v_decls_1432_);
lean_ctor_set(v_reuseFailAlloc_1451_, 6, v_userNames_1433_);
lean_ctor_set(v_reuseFailAlloc_1451_, 7, v_lAssignment_1434_);
lean_ctor_set(v_reuseFailAlloc_1451_, 8, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1451_, 9, v_dAssignment_1436_);
lean_ctor_set(v_reuseFailAlloc_1451_, 10, v_instanceTypedMVars_1437_);
lean_ctor_set(v_reuseFailAlloc_1451_, 11, v_synthNormMemo_1438_);
v___x_1445_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1445_);
v___x_1447_ = v___x_1425_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_cache_1420_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_zetaDeltaFVarIds_1421_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_postponed_1422_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_diag_1423_);
v___x_1447_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_st_ref_put(v___y_1416_, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1442_);
return v___x_1449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1454_, lean_object* v_val_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1454_, v_val_1455_, v___y_1456_);
lean_dec(v___y_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
lean_inc(v_g_1459_);
v___x_1465_ = l_Lean_MVarId_getType(v_g_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Lean_Meta_synthInstance(v_a_1466_, v___x_1467_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1459_, v_a_1469_, v___y_1461_);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1479_);
v___x_1472_ = v___x_1470_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v___x_1470_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_g_1459_);
v_a_1480_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1468_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1468_);
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
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_g_1459_);
v_a_1488_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1465_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1465_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1504_){
_start:
{
lean_object* v___f_1505_; lean_object* v___x_1506_; 
v___f_1505_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1506_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1504_, v___f_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1507_, lean_object* v_val_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1507_, v_val_1508_, v___y_1510_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1515_, lean_object* v_val_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1515_, v_val_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1524_, v_x_1525_, v_x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1528_, lean_object* v_x_1529_, size_t v_x_1530_, size_t v_x_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1529_, v_x_1530_, v_x_1531_, v_x_1532_, v_x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
size_t v_x_1160__boxed_1541_; size_t v_x_1161__boxed_1542_; lean_object* v_res_1543_; 
v_x_1160__boxed_1541_ = lean_unbox_usize(v_x_1537_);
lean_dec(v_x_1537_);
v_x_1161__boxed_1542_ = lean_unbox_usize(v_x_1538_);
lean_dec(v_x_1538_);
v_res_1543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1535_, v_x_1536_, v_x_1160__boxed_1541_, v_x_1161__boxed_1542_, v_x_1539_, v_x_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1544_, lean_object* v_n_1545_, lean_object* v_k_1546_, lean_object* v_v_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1545_, v_k_1546_, v_v_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1549_, size_t v_depth_1550_, lean_object* v_keys_1551_, lean_object* v_vals_1552_, lean_object* v_heq_1553_, lean_object* v_i_1554_, lean_object* v_entries_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1550_, v_keys_1551_, v_vals_1552_, v_i_1554_, v_entries_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_depth_1558_, lean_object* v_keys_1559_, lean_object* v_vals_1560_, lean_object* v_heq_1561_, lean_object* v_i_1562_, lean_object* v_entries_1563_){
_start:
{
size_t v_depth_boxed_1564_; lean_object* v_res_1565_; 
v_depth_boxed_1564_ = lean_unbox_usize(v_depth_1558_);
lean_dec(v_depth_1558_);
v_res_1565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1557_, v_depth_boxed_1564_, v_keys_1559_, v_vals_1560_, v_heq_1561_, v_i_1562_, v_entries_1563_);
lean_dec_ref(v_vals_1560_);
lean_dec_ref(v_keys_1559_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1567_, v_x_1568_, v_x_1569_, v_x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1572_, lean_object* v_discharge_1573_, lean_object* v_g_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v_g_1574_);
v___x_1580_ = lean_apply_6(v_discharge_1572_, v_g_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, lean_box(0));
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec(v_g_1574_);
lean_dec_ref(v_discharge_1573_);
return v___x_1580_;
}
else
{
lean_object* v_a_1581_; uint8_t v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
v___x_1582_ = l_Lean_Exception_isInterrupt(v_a_1581_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; 
v___x_1583_ = l_Lean_Exception_isRuntime(v_a_1581_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref_known(v___x_1580_, 1);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
v___x_1584_ = lean_apply_6(v_discharge_1573_, v_g_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, lean_box(0));
return v___x_1584_;
}
else
{
lean_dec(v_g_1574_);
lean_dec_ref(v_discharge_1573_);
return v___x_1580_;
}
}
else
{
lean_dec(v_a_1581_);
lean_dec(v_g_1574_);
lean_dec_ref(v_discharge_1573_);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1585_, lean_object* v_discharge_1586_, lean_object* v_g_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1585_, v_discharge_1586_, v_g_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1594_, lean_object* v_discharge_1595_){
_start:
{
lean_object* v_toApplyRulesConfig_1596_; lean_object* v_toBacktrackConfig_1597_; uint8_t v_backtracking_1598_; uint8_t v_intro_1599_; uint8_t v_constructor_1600_; uint8_t v_suggestions_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1633_; 
v_toApplyRulesConfig_1596_ = lean_ctor_get(v_cfg_1594_, 0);
lean_inc_ref(v_toApplyRulesConfig_1596_);
v_toBacktrackConfig_1597_ = lean_ctor_get(v_toApplyRulesConfig_1596_, 0);
lean_inc_ref(v_toBacktrackConfig_1597_);
v_backtracking_1598_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*1);
v_intro_1599_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*1 + 1);
v_constructor_1600_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*1 + 2);
v_suggestions_1601_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*1 + 3);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_cfg_1594_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v_cfg_1594_, 0);
lean_dec(v_unused_1634_);
v___x_1603_ = v_cfg_1594_;
v_isShared_1604_ = v_isSharedCheck_1633_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v_cfg_1594_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1633_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_toApplyConfig_1605_; uint8_t v_transparency_1606_; uint8_t v_symm_1607_; uint8_t v_exfalso_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1631_; 
v_toApplyConfig_1605_ = lean_ctor_get(v_toApplyRulesConfig_1596_, 1);
v_transparency_1606_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1596_, sizeof(void*)*2);
v_symm_1607_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1596_, sizeof(void*)*2 + 1);
v_exfalso_1608_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1596_, sizeof(void*)*2 + 2);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_toApplyRulesConfig_1596_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v_toApplyRulesConfig_1596_, 0);
lean_dec(v_unused_1632_);
v___x_1610_ = v_toApplyRulesConfig_1596_;
v_isShared_1611_ = v_isSharedCheck_1631_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_toApplyConfig_1605_);
lean_dec(v_toApplyRulesConfig_1596_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1631_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_maxDepth_1612_; lean_object* v_proc_1613_; lean_object* v_suspend_1614_; lean_object* v_discharge_1615_; uint8_t v_commitIndependentGoals_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1630_; 
v_maxDepth_1612_ = lean_ctor_get(v_toBacktrackConfig_1597_, 0);
v_proc_1613_ = lean_ctor_get(v_toBacktrackConfig_1597_, 1);
v_suspend_1614_ = lean_ctor_get(v_toBacktrackConfig_1597_, 2);
v_discharge_1615_ = lean_ctor_get(v_toBacktrackConfig_1597_, 3);
v_commitIndependentGoals_1616_ = lean_ctor_get_uint8(v_toBacktrackConfig_1597_, sizeof(void*)*4);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_toBacktrackConfig_1597_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1618_ = v_toBacktrackConfig_1597_;
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_discharge_1615_);
lean_inc(v_suspend_1614_);
lean_inc(v_proc_1613_);
lean_inc(v_maxDepth_1612_);
lean_dec(v_toBacktrackConfig_1597_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___f_1620_; lean_object* v___x_1622_; 
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1620_, 0, v_discharge_1595_);
lean_closure_set(v___f_1620_, 1, v_discharge_1615_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 3, v___f_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_maxDepth_1612_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_proc_1613_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_suspend_1614_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v___f_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, sizeof(void*)*4, v_commitIndependentGoals_1616_);
v___x_1622_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1624_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1622_);
v___x_1624_ = v___x_1610_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_toApplyConfig_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*2, v_transparency_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*2 + 1, v_symm_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*2 + 2, v_exfalso_1608_);
v___x_1624_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1624_);
v___x_1626_ = v___x_1603_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*1, v_backtracking_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*1 + 1, v_intro_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*1 + 2, v_constructor_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*1 + 3, v_suggestions_1601_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = 1;
v___x_1642_ = l_Lean_Meta_intro1Core(v_g_1635_, v___x_1641_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1661_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1661_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1661_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_snd_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1659_; 
v_snd_1647_ = lean_ctor_get(v_a_1643_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1643_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_a_1643_, 0);
lean_dec(v_unused_1660_);
v___x_1649_ = v_a_1643_;
v_isShared_1650_ = v_isSharedCheck_1659_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_snd_1647_);
lean_dec(v_a_1643_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1659_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_box(0);
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 1);
lean_ctor_set(v___x_1649_, 1, v___x_1651_);
lean_ctor_set(v___x_1649_, 0, v_snd_1647_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_snd_1647_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1654_);
v___x_1656_ = v___x_1645_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1642_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1642_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1678_){
_start:
{
lean_object* v___f_1679_; lean_object* v___x_1680_; 
v___f_1679_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1680_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1678_, v___f_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1692_ = l_Lean_MVarId_constructor(v_g_1685_, v___x_1691_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1692_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1692_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1718_){
_start:
{
lean_object* v___f_1719_; lean_object* v___x_1720_; 
v___f_1719_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1720_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1718_, v___f_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
lean_inc(v_g_1723_);
v___x_1729_ = l_Lean_MVarId_getType(v_g_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = lean_box(0);
v___x_1732_ = l_Lean_Meta_synthInstance(v_a_1730_, v___x_1731_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1723_, v_a_1733_, v___y_1725_);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1734_, 0);
lean_dec(v_unused_1743_);
v___x_1736_ = v___x_1734_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v___x_1734_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_g_1723_);
v_a_1744_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1732_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1732_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_g_1723_);
v_a_1752_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1729_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1729_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1768_){
_start:
{
lean_object* v___f_1769_; lean_object* v___x_1770_; 
v___f_1769_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1770_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1768_, v___f_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v___x_1774_; 
v___x_1774_ = l_Lean_Expr_hasMVar(v_e_1771_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_e_1771_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v_mctx_1777_; lean_object* v___x_1778_; lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1781_; lean_object* v_cache_1782_; lean_object* v_zetaDeltaFVarIds_1783_; lean_object* v_postponed_1784_; lean_object* v_diag_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1794_; 
v___x_1776_ = lean_st_ref_get(v___y_1772_);
v_mctx_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_mctx_1777_);
lean_dec(v___x_1776_);
v___x_1778_ = l_Lean_instantiateMVarsCore(v_mctx_1777_, v_e_1771_);
v_fst_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_fst_1779_);
v_snd_1780_ = lean_ctor_get(v___x_1778_, 1);
lean_inc(v_snd_1780_);
lean_dec_ref(v___x_1778_);
v___x_1781_ = lean_st_ref_take(v___y_1772_);
v_cache_1782_ = lean_ctor_get(v___x_1781_, 1);
v_zetaDeltaFVarIds_1783_ = lean_ctor_get(v___x_1781_, 2);
v_postponed_1784_ = lean_ctor_get(v___x_1781_, 3);
v_diag_1785_ = lean_ctor_get(v___x_1781_, 4);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v___x_1781_, 0);
lean_dec(v_unused_1795_);
v___x_1787_ = v___x_1781_;
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_diag_1785_);
lean_inc(v_postponed_1784_);
lean_inc(v_zetaDeltaFVarIds_1783_);
lean_inc(v_cache_1782_);
lean_dec(v___x_1781_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v_snd_1780_);
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_snd_1780_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_cache_1782_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_zetaDeltaFVarIds_1783_);
lean_ctor_set(v_reuseFailAlloc_1793_, 3, v_postponed_1784_);
lean_ctor_set(v_reuseFailAlloc_1793_, 4, v_diag_1785_);
v___x_1790_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_st_ref_put(v___y_1772_, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_fst_1779_);
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1796_, v___y_1797_);
lean_dec(v___y_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1800_, v___y_1802_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1814_, lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1814_, v_x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1821_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1821_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1838_, lean_object* v_x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1838_, v_x_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1846_, lean_object* v_mvarId_1847_, lean_object* v_x_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1847_, v_x_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1855_, lean_object* v_mvarId_1856_, lean_object* v_x_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1855_, v_mvarId_1856_, v_x_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_ref_1870_; lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
v_ref_1870_ = lean_ctor_get(v___y_1867_, 2);
v___x_1871_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_inc(v_ref_1870_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_ref_1870_);
lean_ctor_set(v___x_1876_, 1, v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 1);
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = l_List_reverse___redArg(v_x_1889_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v_head_1897_; lean_object* v_tail_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1918_; 
v_head_1897_ = lean_ctor_get(v_x_1888_, 0);
v_tail_1898_ = lean_ctor_get(v_x_1888_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1900_ = v_x_1888_;
v_isShared_1901_ = v_isSharedCheck_1918_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_tail_1898_);
lean_inc(v_head_1897_);
lean_dec(v_x_1888_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1918_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_inc(v_head_1897_);
v___x_1902_ = l_Lean_Expr_mvar___override(v_head_1897_);
v___x_1903_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1903_, 0, v___x_1902_);
v___x_1904_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1897_, v___x_1903_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v_x_1889_);
lean_ctor_set(v___x_1900_, 0, v_a_1905_);
v___x_1907_ = v___x_1900_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1905_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_x_1889_);
v___x_1907_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v_x_1888_ = v_tail_1898_;
v_x_1889_ = v___x_1907_;
goto _start;
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1900_);
lean_dec(v_tail_1898_);
lean_dec(v_x_1889_);
v_a_1910_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1904_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1904_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1919_, v_x_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1926_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1930_, lean_object* v_proc_1931_, lean_object* v_orig_1932_, lean_object* v_goals_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_box(0);
lean_inc(v_orig_1932_);
v___x_1940_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1932_, v___x_1939_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
v___x_1942_ = lean_apply_6(v_test_1930_, v_a_1941_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, lean_box(0));
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; uint8_t v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_goals_1933_);
lean_dec(v_orig_1932_);
lean_dec_ref(v_proc_1931_);
v___x_1945_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1946_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1945_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
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
else
{
lean_object* v___x_1955_; 
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
v___x_1955_ = lean_apply_7(v_proc_1931_, v_orig_1932_, v_goals_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, lean_box(0));
return v___x_1955_;
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_goals_1933_);
lean_dec(v_orig_1932_);
lean_dec_ref(v_proc_1931_);
v_a_1956_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1942_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1942_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_goals_1933_);
lean_dec(v_orig_1932_);
lean_dec_ref(v_proc_1931_);
lean_dec_ref(v_test_1930_);
v_a_1964_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1940_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1940_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1972_, lean_object* v_proc_1973_, lean_object* v_orig_1974_, lean_object* v_goals_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1972_, v_proc_1973_, v_orig_1974_, v_goals_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1982_, lean_object* v_test_1983_){
_start:
{
lean_object* v_toApplyRulesConfig_1984_; lean_object* v_toBacktrackConfig_1985_; uint8_t v_backtracking_1986_; uint8_t v_intro_1987_; uint8_t v_constructor_1988_; uint8_t v_suggestions_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2021_; 
v_toApplyRulesConfig_1984_ = lean_ctor_get(v_cfg_1982_, 0);
lean_inc_ref(v_toApplyRulesConfig_1984_);
v_toBacktrackConfig_1985_ = lean_ctor_get(v_toApplyRulesConfig_1984_, 0);
lean_inc_ref(v_toBacktrackConfig_1985_);
v_backtracking_1986_ = lean_ctor_get_uint8(v_cfg_1982_, sizeof(void*)*1);
v_intro_1987_ = lean_ctor_get_uint8(v_cfg_1982_, sizeof(void*)*1 + 1);
v_constructor_1988_ = lean_ctor_get_uint8(v_cfg_1982_, sizeof(void*)*1 + 2);
v_suggestions_1989_ = lean_ctor_get_uint8(v_cfg_1982_, sizeof(void*)*1 + 3);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_cfg_1982_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v_cfg_1982_, 0);
lean_dec(v_unused_2022_);
v___x_1991_ = v_cfg_1982_;
v_isShared_1992_ = v_isSharedCheck_2021_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_cfg_1982_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2021_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_toApplyConfig_1993_; uint8_t v_transparency_1994_; uint8_t v_symm_1995_; uint8_t v_exfalso_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2019_; 
v_toApplyConfig_1993_ = lean_ctor_get(v_toApplyRulesConfig_1984_, 1);
v_transparency_1994_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1984_, sizeof(void*)*2);
v_symm_1995_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1984_, sizeof(void*)*2 + 1);
v_exfalso_1996_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1984_, sizeof(void*)*2 + 2);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_toApplyRulesConfig_1984_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_toApplyRulesConfig_1984_, 0);
lean_dec(v_unused_2020_);
v___x_1998_ = v_toApplyRulesConfig_1984_;
v_isShared_1999_ = v_isSharedCheck_2019_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_toApplyConfig_1993_);
lean_dec(v_toApplyRulesConfig_1984_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2019_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_maxDepth_2000_; lean_object* v_proc_2001_; lean_object* v_suspend_2002_; lean_object* v_discharge_2003_; uint8_t v_commitIndependentGoals_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2018_; 
v_maxDepth_2000_ = lean_ctor_get(v_toBacktrackConfig_1985_, 0);
v_proc_2001_ = lean_ctor_get(v_toBacktrackConfig_1985_, 1);
v_suspend_2002_ = lean_ctor_get(v_toBacktrackConfig_1985_, 2);
v_discharge_2003_ = lean_ctor_get(v_toBacktrackConfig_1985_, 3);
v_commitIndependentGoals_2004_ = lean_ctor_get_uint8(v_toBacktrackConfig_1985_, sizeof(void*)*4);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_toBacktrackConfig_1985_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2006_ = v_toBacktrackConfig_1985_;
v_isShared_2007_ = v_isSharedCheck_2018_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_discharge_2003_);
lean_inc(v_suspend_2002_);
lean_inc(v_proc_2001_);
lean_inc(v_maxDepth_2000_);
lean_dec(v_toBacktrackConfig_1985_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2018_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___f_2008_; lean_object* v___x_2010_; 
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2008_, 0, v_test_1983_);
lean_closure_set(v___f_2008_, 1, v_proc_2001_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___f_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_maxDepth_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___f_2008_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_suspend_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_discharge_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*4, v_commitIndependentGoals_2004_);
v___x_2010_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2010_);
v___x_2012_ = v___x_1998_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_toApplyConfig_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*2, v_transparency_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*2 + 1, v_symm_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*2 + 2, v_exfalso_1996_);
v___x_2012_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2012_);
v___x_2014_ = v___x_1991_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*1, v_backtracking_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*1 + 1, v_intro_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*1 + 2, v_constructor_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*1 + 3, v_suggestions_1989_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2023_, lean_object* v_msg_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2031_, lean_object* v_msg_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2031_, v_msg_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2038_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2039_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
uint8_t v___x_2040_; 
v___x_2040_ = 0;
return v___x_2040_;
}
else
{
lean_object* v_head_2041_; lean_object* v_tail_2042_; uint8_t v___x_2043_; 
v_head_2041_ = lean_ctor_get(v_x_2039_, 0);
v_tail_2042_ = lean_ctor_get(v_x_2039_, 1);
v___x_2043_ = l_Lean_Expr_hasMVar(v_head_2041_);
if (v___x_2043_ == 0)
{
v_x_2039_ = v_tail_2042_;
goto _start;
}
else
{
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2045_){
_start:
{
uint8_t v_res_2046_; lean_object* v_r_2047_; 
v_res_2046_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2045_);
lean_dec(v_x_2045_);
v_r_2047_ = lean_box(v_res_2046_);
return v_r_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2048_, lean_object* v_sols_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2049_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_inc(v___y_2053_);
lean_inc_ref(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
v___x_2056_ = lean_apply_6(v_test_2048_, v_sols_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, lean_box(0));
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v_sols_2049_);
lean_dec_ref(v_test_2048_);
v___x_2057_ = lean_box(v___x_2055_);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2059_, lean_object* v_sols_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2059_, v_sols_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2067_, lean_object* v_test_2068_){
_start:
{
lean_object* v___f_2069_; lean_object* v___x_2070_; 
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2069_, 0, v_test_2068_);
v___x_2070_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2067_, v___f_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
uint8_t v___x_2073_; 
lean_dec_ref(v_e_2071_);
v___x_2073_ = 0;
return v___x_2073_;
}
else
{
lean_object* v_head_2074_; lean_object* v_tail_2075_; uint8_t v___x_2076_; 
v_head_2074_ = lean_ctor_get(v_x_2072_, 0);
v_tail_2075_ = lean_ctor_get(v_x_2072_, 1);
lean_inc_ref(v_e_2071_);
v___x_2076_ = l_Lean_Expr_occurs(v_e_2071_, v_head_2074_);
if (v___x_2076_ == 0)
{
v_x_2072_ = v_tail_2075_;
goto _start;
}
else
{
lean_dec_ref(v_e_2071_);
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2078_, lean_object* v_x_2079_){
_start:
{
uint8_t v_res_2080_; lean_object* v_r_2081_; 
v_res_2080_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2078_, v_x_2079_);
lean_dec(v_x_2079_);
v_r_2081_ = lean_box(v_res_2080_);
return v_r_2081_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2082_, lean_object* v_x_2083_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
uint8_t v___x_2084_; 
v___x_2084_ = 1;
return v___x_2084_;
}
else
{
lean_object* v_head_2085_; lean_object* v_tail_2086_; uint8_t v___x_2087_; 
v_head_2085_ = lean_ctor_get(v_x_2083_, 0);
lean_inc(v_head_2085_);
v_tail_2086_ = lean_ctor_get(v_x_2083_, 1);
lean_inc(v_tail_2086_);
lean_dec_ref_known(v_x_2083_, 2);
v___x_2087_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2085_, v_sols_2082_);
if (v___x_2087_ == 0)
{
lean_dec(v_tail_2086_);
return v___x_2087_;
}
else
{
v_x_2083_ = v_tail_2086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2089_, lean_object* v_x_2090_){
_start:
{
uint8_t v_res_2091_; lean_object* v_r_2092_; 
v_res_2091_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2089_, v_x_2090_);
lean_dec(v_sols_2089_);
v_r_2092_ = lean_box(v_res_2091_);
return v_r_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2093_, lean_object* v_sols_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2094_, v_use_2093_);
v___x_2101_ = lean_box(v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2103_, lean_object* v_sols_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2103_, v_sols_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v_sols_2104_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2111_, lean_object* v_use_2112_){
_start:
{
lean_object* v___f_2113_; lean_object* v___x_2114_; 
v___f_2113_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2113_, 0, v_use_2112_);
v___x_2114_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2111_, v___f_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2115_){
_start:
{
lean_object* v___y_2117_; lean_object* v_toApplyRulesConfig_2118_; uint8_t v_backtracking_2119_; uint8_t v_intro_2120_; uint8_t v_constructor_2121_; uint8_t v_suggestions_2122_; uint8_t v_intro_2126_; 
v_intro_2126_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1 + 1);
if (v_intro_2126_ == 0)
{
lean_object* v_toApplyRulesConfig_2127_; uint8_t v_backtracking_2128_; uint8_t v_constructor_2129_; uint8_t v_suggestions_2130_; 
v_toApplyRulesConfig_2127_ = lean_ctor_get(v_cfg_2115_, 0);
lean_inc_ref(v_toApplyRulesConfig_2127_);
v_backtracking_2128_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1);
v_constructor_2129_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1 + 2);
v_suggestions_2130_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1 + 3);
v___y_2117_ = v_cfg_2115_;
v_toApplyRulesConfig_2118_ = v_toApplyRulesConfig_2127_;
v_backtracking_2119_ = v_backtracking_2128_;
v_intro_2120_ = v_intro_2126_;
v_constructor_2121_ = v_constructor_2129_;
v_suggestions_2122_ = v_suggestions_2130_;
goto v___jp_2116_;
}
else
{
lean_object* v_toApplyRulesConfig_2131_; uint8_t v_backtracking_2132_; uint8_t v_constructor_2133_; uint8_t v_suggestions_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2148_; 
v_toApplyRulesConfig_2131_ = lean_ctor_get(v_cfg_2115_, 0);
v_backtracking_2132_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1);
v_constructor_2133_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1 + 2);
v_suggestions_2134_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*1 + 3);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_cfg_2115_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2136_ = v_cfg_2115_;
v_isShared_2137_ = v_isSharedCheck_2148_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_toApplyRulesConfig_2131_);
lean_dec(v_cfg_2115_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2148_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = 0;
if (v_isShared_2137_ == 0)
{
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_toApplyRulesConfig_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2147_, sizeof(void*)*1, v_backtracking_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2147_, sizeof(void*)*1 + 2, v_constructor_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2147_, sizeof(void*)*1 + 3, v_suggestions_2134_);
v___x_2140_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v_toApplyRulesConfig_2142_; uint8_t v_backtracking_2143_; uint8_t v_intro_2144_; uint8_t v_constructor_2145_; uint8_t v_suggestions_2146_; 
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*1 + 1, v___x_2138_);
v___x_2141_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2140_);
v_toApplyRulesConfig_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_ref(v_toApplyRulesConfig_2142_);
v_backtracking_2143_ = lean_ctor_get_uint8(v___x_2141_, sizeof(void*)*1);
v_intro_2144_ = lean_ctor_get_uint8(v___x_2141_, sizeof(void*)*1 + 1);
v_constructor_2145_ = lean_ctor_get_uint8(v___x_2141_, sizeof(void*)*1 + 2);
v_suggestions_2146_ = lean_ctor_get_uint8(v___x_2141_, sizeof(void*)*1 + 3);
v___y_2117_ = v___x_2141_;
v_toApplyRulesConfig_2118_ = v_toApplyRulesConfig_2142_;
v_backtracking_2119_ = v_backtracking_2143_;
v_intro_2120_ = v_intro_2144_;
v_constructor_2121_ = v_constructor_2145_;
v_suggestions_2122_ = v_suggestions_2146_;
goto v___jp_2116_;
}
}
}
v___jp_2116_:
{
if (v_constructor_2121_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2118_);
return v___y_2117_;
}
else
{
uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref(v___y_2117_);
v___x_2123_ = 0;
v___x_2124_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2124_, 0, v_toApplyRulesConfig_2118_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1, v_backtracking_2119_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1 + 1, v_intro_2120_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1 + 2, v___x_2123_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1 + 3, v_suggestions_2122_);
v___x_2125_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2124_);
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
if (lean_obj_tag(v_x_2149_) == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = l_List_reverse___redArg(v_x_2150_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
else
{
lean_object* v_head_2160_; lean_object* v_tail_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2179_; 
v_head_2160_ = lean_ctor_get(v_x_2149_, 0);
v_tail_2161_ = lean_ctor_get(v_x_2149_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_x_2149_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2163_ = v_x_2149_;
v_isShared_2164_ = v_isSharedCheck_2179_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_tail_2161_);
lean_inc(v_head_2160_);
lean_dec(v_x_2149_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2179_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; 
lean_inc(v___y_2156_);
lean_inc_ref(v___y_2155_);
lean_inc(v___y_2154_);
lean_inc_ref(v___y_2153_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2151_);
v___x_2165_ = lean_apply_7(v_head_2160_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v_x_2150_);
lean_ctor_set(v___x_2163_, 0, v_a_2166_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2166_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_x_2150_);
v___x_2168_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_x_2149_ = v_tail_2161_;
v_x_2150_ = v___x_2168_;
goto _start;
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_del_object(v___x_2163_);
lean_dec(v_tail_2161_);
lean_dec(v_x_2150_);
v_a_2171_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2165_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2180_, lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2180_, v_x_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2190_, lean_object* v_cfg_2191_, lean_object* v_lemmas_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
v___x_2200_ = lean_apply_8(v_ctx_2190_, v_cfg_2191_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, lean_box(0));
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = lean_box(0);
v___x_2203_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2192_, v___x_2202_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = l_List_appendTR___redArg(v_a_2201_, v_a_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_dec(v_a_2201_);
return v___x_2203_;
}
}
else
{
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_lemmas_2192_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2213_, lean_object* v_cfg_2214_, lean_object* v_lemmas_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2213_, v_cfg_2214_, v_lemmas_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = 0;
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2226_){
_start:
{
uint8_t v_res_2227_; lean_object* v_r_2228_; 
v_res_2227_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2226_);
lean_dec(v_x_2226_);
v_r_2228_ = lean_box(v_res_2227_);
return v_r_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2229_, lean_object* v___x_2230_, lean_object* v___x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2229_, v___x_2230_, v___x_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_fst_2242_; lean_object* v___x_2244_; 
v_fst_2242_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_fst_2242_);
lean_dec(v_a_2238_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_fst_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_fst_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2237_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2255_, lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2255_, v___x_2256_, v___x_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2278_, lean_object* v_g_2279_, lean_object* v_lemmas_2280_, lean_object* v_ctx_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; 
v___f_2287_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2287_, 0, v_ctx_2281_);
lean_closure_set(v___f_2287_, 1, v_cfg_2278_);
lean_closure_set(v___f_2287_, 2, v_lemmas_2280_);
v___x_2288_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2289_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2290_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2290_, 0, v___f_2287_);
lean_closure_set(v___f_2290_, 1, v___x_2288_);
lean_closure_set(v___f_2290_, 2, v___x_2289_);
v___x_2291_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2279_, v___f_2290_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2292_, lean_object* v_g_2293_, lean_object* v_lemmas_2294_, lean_object* v_ctx_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2292_, v_g_2293_, v_lemmas_2294_, v_ctx_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2302_, lean_object* v_lemmas_2303_, lean_object* v_ctx_2304_, lean_object* v_g_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; 
lean_inc(v_g_2305_);
lean_inc_ref(v_cfg_2302_);
v___x_2311_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2302_, v_g_2305_, v_lemmas_2303_, v_ctx_2304_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_toApplyRulesConfig_2312_; lean_object* v_a_2313_; lean_object* v_toApplyConfig_2314_; uint8_t v_transparency_2315_; lean_object* v___x_2316_; 
v_toApplyRulesConfig_2312_ = lean_ctor_get(v_cfg_2302_, 0);
lean_inc_ref(v_toApplyRulesConfig_2312_);
lean_dec_ref(v_cfg_2302_);
v_a_2313_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2311_, 1);
v_toApplyConfig_2314_ = lean_ctor_get(v_toApplyRulesConfig_2312_, 1);
lean_inc_ref(v_toApplyConfig_2314_);
v_transparency_2315_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2312_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2312_);
v___x_2316_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2314_, v_transparency_2315_, v_a_2313_, v_g_2305_, v_a_2307_, v_a_2309_);
return v___x_2316_;
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_g_2305_);
lean_dec_ref(v_cfg_2302_);
v_a_2317_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2311_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2311_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2325_, lean_object* v_lemmas_2326_, lean_object* v_ctx_2327_, lean_object* v_g_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2325_, v_lemmas_2326_, v_ctx_2327_, v_g_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2335_, lean_object* v_lemmas_2336_, lean_object* v_ctx_2337_, lean_object* v_g_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; 
lean_inc(v_g_2338_);
lean_inc_ref(v_cfg_2335_);
v___x_2344_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2335_, v_g_2338_, v_lemmas_2336_, v_ctx_2337_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_toApplyRulesConfig_2345_; lean_object* v_a_2346_; lean_object* v_toApplyConfig_2347_; uint8_t v_transparency_2348_; lean_object* v___x_2349_; 
v_toApplyRulesConfig_2345_ = lean_ctor_get(v_cfg_2335_, 0);
lean_inc_ref(v_toApplyRulesConfig_2345_);
lean_dec_ref(v_cfg_2335_);
v_a_2346_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2344_, 1);
v_toApplyConfig_2347_ = lean_ctor_get(v_toApplyRulesConfig_2345_, 1);
lean_inc_ref(v_toApplyConfig_2347_);
v_transparency_2348_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2345_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2345_);
v___x_2349_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2347_, v_transparency_2348_, v_a_2346_, v_g_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
return v___x_2349_;
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_g_2338_);
lean_dec_ref(v_cfg_2335_);
v_a_2350_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2344_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2344_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2358_, lean_object* v_lemmas_2359_, lean_object* v_ctx_2360_, lean_object* v_g_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2358_, v_lemmas_2359_, v_ctx_2360_, v_g_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2367_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2368_, lean_object* v_i_2369_, lean_object* v_k_2370_){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = lean_array_get_size(v_keys_2368_);
v___x_2372_ = lean_nat_dec_lt(v_i_2369_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_dec(v_i_2369_);
return v___x_2372_;
}
else
{
lean_object* v_k_x27_2373_; uint8_t v___x_2374_; 
v_k_x27_2373_ = lean_array_fget_borrowed(v_keys_2368_, v_i_2369_);
v___x_2374_ = l_Lean_instBEqMVarId_beq(v_k_2370_, v_k_x27_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_nat_add(v_i_2369_, v___x_2375_);
lean_dec(v_i_2369_);
v_i_2369_ = v___x_2376_;
goto _start;
}
else
{
lean_dec(v_i_2369_);
return v___x_2372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2378_, lean_object* v_i_2379_, lean_object* v_k_2380_){
_start:
{
uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_res_2381_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2378_, v_i_2379_, v_k_2380_);
lean_dec(v_k_2380_);
lean_dec_ref(v_keys_2378_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2383_, size_t v_x_2384_, lean_object* v_x_2385_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
lean_object* v_es_2386_; lean_object* v___x_2387_; size_t v___x_2388_; size_t v___x_2389_; lean_object* v_j_2390_; lean_object* v___x_2391_; 
v_es_2386_ = lean_ctor_get(v_x_2383_, 0);
v___x_2387_ = lean_box(2);
v___x_2388_ = ((size_t)31ULL);
v___x_2389_ = lean_usize_land(v_x_2384_, v___x_2388_);
v_j_2390_ = lean_usize_to_nat(v___x_2389_);
v___x_2391_ = lean_array_get_borrowed(v___x_2387_, v_es_2386_, v_j_2390_);
lean_dec(v_j_2390_);
switch(lean_obj_tag(v___x_2391_))
{
case 0:
{
lean_object* v_key_2392_; uint8_t v___x_2393_; 
v_key_2392_ = lean_ctor_get(v___x_2391_, 0);
v___x_2393_ = l_Lean_instBEqMVarId_beq(v_x_2385_, v_key_2392_);
return v___x_2393_;
}
case 1:
{
lean_object* v_node_2394_; size_t v___x_2395_; size_t v___x_2396_; 
v_node_2394_ = lean_ctor_get(v___x_2391_, 0);
v___x_2395_ = ((size_t)5ULL);
v___x_2396_ = lean_usize_shift_right(v_x_2384_, v___x_2395_);
v_x_2383_ = v_node_2394_;
v_x_2384_ = v___x_2396_;
goto _start;
}
default: 
{
uint8_t v___x_2398_; 
v___x_2398_ = 0;
return v___x_2398_;
}
}
}
else
{
lean_object* v_ks_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v_ks_2399_ = lean_ctor_get(v_x_2383_, 0);
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2399_, v___x_2400_, v_x_2385_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_){
_start:
{
size_t v_x_1980__boxed_2405_; uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_x_1980__boxed_2405_ = lean_unbox_usize(v_x_2403_);
lean_dec(v_x_2403_);
v_res_2406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2402_, v_x_1980__boxed_2405_, v_x_2404_);
lean_dec(v_x_2404_);
lean_dec_ref(v_x_2402_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
uint64_t v___x_2410_; size_t v___x_2411_; uint8_t v___x_2412_; 
v___x_2410_ = l_Lean_instHashableMVarId_hash(v_x_2409_);
v___x_2411_ = lean_uint64_to_usize(v___x_2410_);
v___x_2412_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2408_, v___x_2411_, v_x_2409_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
uint8_t v_res_2415_; lean_object* v_r_2416_; 
v_res_2415_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2413_, v_x_2414_);
lean_dec(v_x_2414_);
lean_dec_ref(v_x_2413_);
v_r_2416_ = lean_box(v_res_2415_);
return v_r_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v_mctx_2421_; lean_object* v_eAssignment_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2420_ = lean_st_ref_get(v___y_2418_);
v_mctx_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc_ref(v_mctx_2421_);
lean_dec(v___x_2420_);
v_eAssignment_2422_ = lean_ctor_get(v_mctx_2421_, 8);
lean_inc_ref(v_eAssignment_2422_);
lean_dec_ref(v_mctx_2421_);
v___x_2423_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2422_, v_mvarId_2417_);
lean_dec_ref(v_eAssignment_2422_);
v___x_2424_ = lean_box(v___x_2423_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec(v_mvarId_2426_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
if (lean_obj_tag(v_x_2431_) == 0)
{
return v_x_2430_;
}
else
{
lean_object* v_head_2432_; lean_object* v_tail_2433_; lean_object* v___x_2434_; 
v_head_2432_ = lean_ctor_get(v_x_2431_, 0);
lean_inc(v_head_2432_);
v_tail_2433_ = lean_ctor_get(v_x_2431_, 1);
lean_inc(v_tail_2433_);
lean_dec_ref_known(v_x_2431_, 2);
v___x_2434_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2430_, v_head_2432_);
v_x_2430_ = v___x_2434_;
v_x_2431_ = v_tail_2433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2436_, lean_object* v_a_2437_, uint8_t v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
if (lean_obj_tag(v_a_2439_) == 0)
{
if (lean_obj_tag(v_a_2440_) == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec(v_a_2437_);
lean_dec_ref(v_f_2436_);
v___x_2447_ = lean_box(v_a_2438_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_a_2441_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
else
{
lean_object* v_head_2450_; lean_object* v_tail_2451_; 
v_head_2450_ = lean_ctor_get(v_a_2440_, 0);
lean_inc(v_head_2450_);
v_tail_2451_ = lean_ctor_get(v_a_2440_, 1);
lean_inc(v_tail_2451_);
lean_dec_ref_known(v_a_2440_, 2);
v_a_2439_ = v_head_2450_;
v_a_2440_ = v_tail_2451_;
goto _start;
}
}
else
{
lean_object* v_head_2453_; lean_object* v_tail_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2497_; 
v_head_2453_ = lean_ctor_get(v_a_2439_, 0);
v_tail_2454_ = lean_ctor_get(v_a_2439_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_a_2439_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2456_ = v_a_2439_;
v_isShared_2457_ = v_isSharedCheck_2497_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_tail_2454_);
lean_inc(v_head_2453_);
lean_dec(v_a_2439_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2497_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2496_; 
v___x_2458_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2453_, v___y_2443_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2496_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2496_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
if (v___x_2463_ == 0)
{
lean_object* v_zero_2464_; uint8_t v_isZero_2465_; 
v_zero_2464_ = lean_unsigned_to_nat(0u);
v_isZero_2465_ = lean_nat_dec_eq(v_a_2437_, v_zero_2464_);
if (v_isZero_2465_ == 1)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_del_object(v___x_2456_);
lean_dec(v_a_2437_);
lean_dec_ref(v_f_2436_);
v___x_2466_ = lean_array_push(v_a_2441_, v_head_2453_);
v___x_2467_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2466_, v_tail_2454_);
v___x_2468_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2467_, v_a_2440_);
v___x_2469_ = lean_box(v_a_2438_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2468_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2470_);
v___x_2472_ = v___x_2461_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
else
{
lean_object* v_one_2474_; lean_object* v_n_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_del_object(v___x_2461_);
v_one_2474_ = lean_unsigned_to_nat(1u);
v_n_2475_ = lean_nat_sub(v_a_2437_, v_one_2474_);
lean_dec(v_a_2437_);
v___x_2476_ = 1;
lean_inc_ref(v_f_2436_);
lean_inc(v_head_2453_);
v___x_2477_ = lean_apply_1(v_f_2436_, v_head_2453_);
v___x_2478_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2477_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
if (lean_obj_tag(v_a_2479_) == 0)
{
lean_object* v___x_2480_; 
lean_del_object(v___x_2456_);
v___x_2480_ = lean_array_push(v_a_2441_, v_head_2453_);
v_a_2437_ = v_n_2475_;
v_a_2439_ = v_tail_2454_;
v_a_2441_ = v___x_2480_;
goto _start;
}
else
{
lean_object* v_val_2482_; lean_object* v___x_2484_; 
lean_dec(v_head_2453_);
v_val_2482_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v_a_2479_, 1);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v_a_2440_);
lean_ctor_set(v___x_2456_, 0, v_tail_2454_);
v___x_2484_ = v___x_2456_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_tail_2454_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_a_2440_);
v___x_2484_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
v_a_2437_ = v_n_2475_;
v_a_2438_ = v___x_2476_;
v_a_2439_ = v_val_2482_;
v_a_2440_ = v___x_2484_;
goto _start;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_n_2475_);
lean_del_object(v___x_2456_);
lean_dec(v_tail_2454_);
lean_dec(v_head_2453_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_f_2436_);
v_a_2487_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2478_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2478_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
else
{
lean_del_object(v___x_2461_);
lean_del_object(v___x_2456_);
lean_dec(v_head_2453_);
v_a_2439_ = v_tail_2454_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v_a_2059__boxed_2509_; lean_object* v_res_2510_; 
v_a_2059__boxed_2509_ = lean_unbox(v_a_2500_);
v_res_2510_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2498_, v_a_2499_, v_a_2059__boxed_2509_, v_a_2501_, v_a_2502_, v_a_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2511_, size_t v_i_2512_, size_t v_stop_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_a_2521_; uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_eq(v_i_2512_, v_stop_2513_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_array_uget_borrowed(v_as_2511_, v_i_2512_);
v___x_2527_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2526_, v___y_2516_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; uint8_t v___x_2529_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = lean_unbox(v_a_2528_);
lean_dec(v_a_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
lean_inc(v___x_2526_);
v___x_2530_ = lean_array_push(v_b_2514_, v___x_2526_);
v_a_2521_ = v___x_2530_;
goto v___jp_2520_;
}
else
{
v_a_2521_ = v_b_2514_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_b_2514_);
v_a_2531_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2527_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2527_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_b_2514_);
return v___x_2539_;
}
v___jp_2520_:
{
size_t v___x_2522_; size_t v___x_2523_; 
v___x_2522_ = ((size_t)1ULL);
v___x_2523_ = lean_usize_add(v_i_2512_, v___x_2522_);
v_i_2512_ = v___x_2523_;
v_b_2514_ = v_a_2521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2540_, lean_object* v_i_2541_, lean_object* v_stop_2542_, lean_object* v_b_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_i_boxed_2549_; size_t v_stop_boxed_2550_; lean_object* v_res_2551_; 
v_i_boxed_2549_ = lean_unbox_usize(v_i_2541_);
lean_dec(v_i_2541_);
v_stop_boxed_2550_ = lean_unbox_usize(v_stop_2542_);
lean_dec(v_stop_2542_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2540_, v_i_boxed_2549_, v_stop_boxed_2550_, v_b_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_as_2540_);
return v_res_2551_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2555_ = lean_array_to_list(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2556_, lean_object* v_goals_2557_, lean_object* v_maxIters_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2564_ = 0;
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2568_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2556_, v_maxIters_2558_, v___x_2564_, v_goals_2557_, v___x_2565_, v___x_2567_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2611_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2611_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2611_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_fst_2573_; lean_object* v_snd_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2610_; 
v_fst_2573_ = lean_ctor_get(v_a_2569_, 0);
v_snd_2574_ = lean_ctor_get(v_a_2569_, 1);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_a_2569_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2576_ = v_a_2569_;
v_isShared_2577_ = v_isSharedCheck_2610_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_snd_2574_);
lean_inc(v_fst_2573_);
lean_dec(v_a_2569_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2610_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = lean_array_get_size(v_snd_2574_);
v___x_2579_ = lean_nat_dec_lt(v___x_2566_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_dec(v_snd_2574_);
v___x_2580_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v___x_2580_);
v___x_2582_ = v___x_2576_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_fst_2573_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2582_);
v___x_2584_ = v___x_2571_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
lean_del_object(v___x_2571_);
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = lean_usize_of_nat(v___x_2578_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2574_, v___x_2587_, v___x_2588_, v___x_2567_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v_snd_2574_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2601_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2601_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2601_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_array_to_list(v_a_2590_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v___x_2594_);
v___x_2596_ = v___x_2576_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_fst_2573_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2596_);
v___x_2598_ = v___x_2592_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_del_object(v___x_2576_);
lean_dec(v_fst_2573_);
v_a_2602_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2589_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2589_);
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
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
v_a_2612_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2568_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2568_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2620_, lean_object* v_goals_2621_, lean_object* v_maxIters_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2620_, v_goals_2621_, v_maxIters_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2628_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2632_, lean_object* v_goals_2633_, lean_object* v_maxIters_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2632_, v_goals_2633_, v_maxIters_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2653_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2653_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2653_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_fst_2645_; uint8_t v___x_2646_; 
v_fst_2645_ = lean_ctor_get(v_a_2641_, 0);
v___x_2646_ = lean_unbox(v_fst_2645_);
if (v___x_2646_ == 1)
{
lean_object* v_snd_2647_; lean_object* v___x_2649_; 
v_snd_2647_ = lean_ctor_get(v_a_2641_, 1);
lean_inc(v_snd_2647_);
lean_dec(v_a_2641_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v_snd_2647_);
v___x_2649_ = v___x_2643_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_snd_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_del_object(v___x_2643_);
lean_dec(v_a_2641_);
v___x_2651_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2652_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2651_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2652_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2640_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2640_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2662_, lean_object* v_goals_2663_, lean_object* v_maxIters_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2662_, v_goals_2663_, v_maxIters_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2671_, lean_object* v_ctx_2672_, lean_object* v_cfg_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
uint8_t v_backtracking_2680_; 
v_backtracking_2680_ = lean_ctor_get_uint8(v_cfg_2673_, sizeof(void*)*1);
if (v_backtracking_2680_ == 0)
{
lean_object* v_toApplyRulesConfig_2681_; lean_object* v_toBacktrackConfig_2682_; lean_object* v_maxDepth_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_toApplyRulesConfig_2681_ = lean_ctor_get(v_cfg_2673_, 0);
v_toBacktrackConfig_2682_ = lean_ctor_get(v_toApplyRulesConfig_2681_, 0);
v_maxDepth_2683_ = lean_ctor_get(v_toBacktrackConfig_2682_, 0);
lean_inc(v_maxDepth_2683_);
v___x_2684_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2684_, 0, v_cfg_2673_);
lean_closure_set(v___x_2684_, 1, v_lemmas_2671_);
lean_closure_set(v___x_2684_, 2, v_ctx_2672_);
v___x_2685_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2684_, v_a_2674_, v_maxDepth_2683_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
return v___x_2685_;
}
else
{
lean_object* v_toApplyRulesConfig_2686_; lean_object* v_toBacktrackConfig_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_toApplyRulesConfig_2686_ = lean_ctor_get(v_cfg_2673_, 0);
v_toBacktrackConfig_2687_ = lean_ctor_get(v_toApplyRulesConfig_2686_, 0);
lean_inc_ref(v_toBacktrackConfig_2687_);
v___x_2688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2689_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2689_, 0, v_cfg_2673_);
lean_closure_set(v___x_2689_, 1, v_lemmas_2671_);
lean_closure_set(v___x_2689_, 2, v_ctx_2672_);
v___x_2690_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2687_, v___x_2688_, v___x_2689_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2691_, lean_object* v_ctx_2692_, lean_object* v_cfg_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2691_, v_ctx_2692_, v_cfg_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2701_, v___y_2703_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_mvarId_2708_);
return v_res_2714_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
uint8_t v___x_2718_; 
v___x_2718_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2716_, v_x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_){
_start:
{
uint8_t v_res_2722_; lean_object* v_r_2723_; 
v_res_2722_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2719_, v_x_2720_, v_x_2721_);
lean_dec(v_x_2721_);
lean_dec_ref(v_x_2720_);
v_r_2723_ = lean_box(v_res_2722_);
return v_r_2723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2724_, lean_object* v_x_2725_, size_t v_x_2726_, lean_object* v_x_2727_){
_start:
{
uint8_t v___x_2728_; 
v___x_2728_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2725_, v_x_2726_, v_x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
size_t v_x_2499__boxed_2733_; uint8_t v_res_2734_; lean_object* v_r_2735_; 
v_x_2499__boxed_2733_ = lean_unbox_usize(v_x_2731_);
lean_dec(v_x_2731_);
v_res_2734_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2729_, v_x_2730_, v_x_2499__boxed_2733_, v_x_2732_);
lean_dec(v_x_2732_);
lean_dec_ref(v_x_2730_);
v_r_2735_ = lean_box(v_res_2734_);
return v_r_2735_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2736_, lean_object* v_keys_2737_, lean_object* v_vals_2738_, lean_object* v_heq_2739_, lean_object* v_i_2740_, lean_object* v_k_2741_){
_start:
{
uint8_t v___x_2742_; 
v___x_2742_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2737_, v_i_2740_, v_k_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2743_, lean_object* v_keys_2744_, lean_object* v_vals_2745_, lean_object* v_heq_2746_, lean_object* v_i_2747_, lean_object* v_k_2748_){
_start:
{
uint8_t v_res_2749_; lean_object* v_r_2750_; 
v_res_2749_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2743_, v_keys_2744_, v_vals_2745_, v_heq_2746_, v_i_2747_, v_k_2748_);
lean_dec(v_k_2748_);
lean_dec_ref(v_vals_2745_);
lean_dec_ref(v_keys_2744_);
v_r_2750_ = lean_box(v_res_2749_);
return v_r_2750_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec_ref(v_x_2762_);
return v_res_2768_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2771_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2772_ = l_Lean_Name_append(v___x_2771_, v___x_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2773_, lean_object* v_lemmas_2774_, lean_object* v_ctx_2775_, lean_object* v_goals_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___f_2782_; lean_object* v_cfg_2783_; lean_object* v___x_2784_; 
v___f_2782_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v_cfg_2783_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2773_);
lean_inc(v_goals_2776_);
lean_inc_ref(v_cfg_2783_);
lean_inc_ref(v_ctx_2775_);
lean_inc(v_lemmas_2774_);
v___x_2784_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2774_, v_ctx_2775_, v_cfg_2783_, v_goals_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref(v_cfg_2783_);
lean_dec(v_goals_2776_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
return v___x_2784_;
}
else
{
lean_object* v_a_2785_; uint8_t v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v___x_2786_ = l_Lean_Exception_isInterrupt(v_a_2785_);
if (v___x_2786_ == 0)
{
uint8_t v___x_2787_; 
lean_inc(v_a_2785_);
v___x_2787_ = l_Lean_Exception_isRuntime(v_a_2785_);
if (v___x_2787_ == 0)
{
if (lean_obj_tag(v_goals_2776_) == 1)
{
lean_object* v_tail_2788_; 
v_tail_2788_ = lean_ctor_get(v_goals_2776_, 1);
lean_inc(v_tail_2788_);
if (lean_obj_tag(v_tail_2788_) == 0)
{
lean_object* v_toApplyRulesConfig_2789_; uint8_t v_exfalso_2790_; 
v_toApplyRulesConfig_2789_ = lean_ctor_get(v_cfg_2783_, 0);
v_exfalso_2790_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2789_, sizeof(void*)*2 + 2);
if (v_exfalso_2790_ == 1)
{
lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2784_, 0);
lean_dec(v_unused_2921_);
v___x_2792_ = v___x_2784_;
v_isShared_2793_ = v_isSharedCheck_2920_;
goto v_resetjp_2791_;
}
else
{
lean_dec(v___x_2784_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2920_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v_toCold_2794_; lean_object* v_options_2795_; uint8_t v_hasTrace_2796_; 
v_toCold_2794_ = lean_ctor_get(v_a_2779_, 0);
v_options_2795_ = lean_ctor_get(v_toCold_2794_, 2);
v_hasTrace_2796_ = lean_ctor_get_uint8(v_options_2795_, sizeof(void*)*1);
if (v_hasTrace_2796_ == 0)
{
lean_object* v_head_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2815_; 
lean_del_object(v___x_2792_);
v_head_2797_ = lean_ctor_get(v_goals_2776_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_goals_2776_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v_goals_2776_, 1);
lean_dec(v_unused_2816_);
v___x_2799_ = v_goals_2776_;
v_isShared_2800_ = v_isSharedCheck_2815_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_head_2797_);
lean_dec(v_goals_2776_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2815_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_MVarId_exfalso(v_head_2797_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v_a_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2802_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_tail_2788_);
v___x_2804_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2774_, v_ctx_2775_, v_cfg_2783_, v___x_2804_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2805_;
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_del_object(v___x_2799_);
lean_dec_ref(v_cfg_2783_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
v_a_2807_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2801_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2801_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
else
{
lean_object* v_head_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2918_; 
v_head_2817_ = lean_ctor_get(v_goals_2776_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_goals_2776_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v_goals_2776_, 1);
lean_dec(v_unused_2919_);
v___x_2819_ = v_goals_2776_;
v_isShared_2820_ = v_isSharedCheck_2918_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_head_2817_);
lean_dec(v_goals_2776_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2918_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_inheritedTraceOptions_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v_a_2829_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v_a_2844_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v_a_2851_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v_a_2863_; 
v_inheritedTraceOptions_2821_ = lean_ctor_get(v_toCold_2794_, 11);
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2823_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2824_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2825_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2821_, v_options_2795_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = l_Lean_trace_profiler;
v___x_2905_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2795_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_del_object(v___x_2819_);
lean_del_object(v___x_2792_);
v___x_2906_ = l_Lean_MVarId_exfalso(v_head_2817_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 1);
v___x_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2907_);
lean_ctor_set(v___x_2908_, 1, v_tail_2788_);
v___x_2909_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2774_, v_ctx_2775_, v_cfg_2783_, v___x_2908_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2909_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_cfg_2783_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
v_a_2910_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2906_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2906_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
goto v___jp_2865_;
}
}
else
{
goto v___jp_2865_;
}
v___jp_2826_:
{
lean_object* v___x_2830_; double v___x_2831_; double v___x_2832_; double v___x_2833_; double v___x_2834_; double v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2830_ = lean_io_mono_nanos_now();
v___x_2831_ = lean_float_of_nat(v___y_2828_);
v___x_2832_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2833_ = lean_float_div(v___x_2831_, v___x_2832_);
v___x_2834_ = lean_float_of_nat(v___x_2830_);
v___x_2835_ = lean_float_div(v___x_2834_, v___x_2832_);
v___x_2836_ = lean_box_float(v___x_2833_);
v___x_2837_ = lean_box_float(v___x_2835_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_a_2829_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_2822_, v_exfalso_2790_, v___x_2823_, v_options_2795_, v___x_2825_, v___y_2827_, v___f_2782_, v___x_2839_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2840_;
}
v___jp_2841_:
{
lean_object* v___x_2846_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2844_);
v___x_2846_ = v___x_2792_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v___y_2827_ = v___y_2842_;
v___y_2828_ = v___y_2843_;
v_a_2829_ = v___x_2846_;
goto v___jp_2826_;
}
}
v___jp_2848_:
{
lean_object* v___x_2852_; double v___x_2853_; double v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2852_ = lean_io_get_num_heartbeats();
v___x_2853_ = lean_float_of_nat(v___y_2850_);
v___x_2854_ = lean_float_of_nat(v___x_2852_);
v___x_2855_ = lean_box_float(v___x_2853_);
v___x_2856_ = lean_box_float(v___x_2854_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_a_2851_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_2822_, v_exfalso_2790_, v___x_2823_, v_options_2795_, v___x_2825_, v___y_2849_, v___f_2782_, v___x_2858_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2859_;
}
v___jp_2860_:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_a_2863_);
v___y_2849_ = v___y_2861_;
v___y_2850_ = v___y_2862_;
v_a_2851_ = v___x_2864_;
goto v___jp_2848_;
}
v___jp_2865_:
{
lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2866_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2780_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2869_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2795_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_io_mono_nanos_now();
v___x_2871_ = l_Lean_MVarId_exfalso(v_head_2817_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v_a_2872_);
v___x_2874_ = v___x_2819_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2872_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_tail_2788_);
v___x_2874_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2774_, v_ctx_2775_, v_cfg_2783_, v___x_2874_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_del_object(v___x_2792_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 1);
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
v___y_2827_ = v_a_2867_;
v___y_2828_ = v___x_2870_;
v_a_2829_ = v___x_2881_;
goto v___jp_2826_;
}
}
}
else
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2875_, 1);
v___y_2842_ = v_a_2867_;
v___y_2843_ = v___x_2870_;
v_a_2844_ = v_a_2884_;
goto v___jp_2841_;
}
}
}
else
{
lean_object* v_a_2886_; 
lean_del_object(v___x_2819_);
lean_dec_ref(v_cfg_2783_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
v_a_2886_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2871_, 1);
v___y_2842_ = v_a_2867_;
v___y_2843_ = v___x_2870_;
v_a_2844_ = v_a_2886_;
goto v___jp_2841_;
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_del_object(v___x_2792_);
v___x_2887_ = lean_io_get_num_heartbeats();
v___x_2888_ = l_Lean_MVarId_exfalso(v_head_2817_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v_a_2889_);
v___x_2891_ = v___x_2819_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2889_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_tail_2788_);
v___x_2891_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2774_, v_ctx_2775_, v_cfg_2783_, v___x_2891_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 1);
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
v___y_2849_ = v_a_2867_;
v___y_2850_ = v___x_2887_;
v_a_2851_ = v___x_2898_;
goto v___jp_2848_;
}
}
}
else
{
lean_object* v_a_2901_; 
v_a_2901_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2892_, 1);
v___y_2861_ = v_a_2867_;
v___y_2862_ = v___x_2887_;
v_a_2863_ = v_a_2901_;
goto v___jp_2860_;
}
}
}
else
{
lean_object* v_a_2903_; 
lean_del_object(v___x_2819_);
lean_dec_ref(v_cfg_2783_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
v_a_2903_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2888_, 1);
v___y_2861_ = v_a_2867_;
v___y_2862_ = v___x_2887_;
v_a_2863_ = v_a_2903_;
goto v___jp_2860_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2776_, 2);
lean_dec_ref(v_cfg_2783_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
return v___x_2784_;
}
}
else
{
lean_dec(v_tail_2788_);
lean_dec_ref_known(v_goals_2776_, 2);
lean_dec_ref(v_cfg_2783_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
return v___x_2784_;
}
}
else
{
lean_dec_ref(v_cfg_2783_);
lean_dec(v_goals_2776_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
return v___x_2784_;
}
}
else
{
lean_dec_ref(v_cfg_2783_);
lean_dec(v_goals_2776_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
return v___x_2784_;
}
}
else
{
lean_dec_ref(v_cfg_2783_);
lean_dec(v_goals_2776_);
lean_dec_ref(v_ctx_2775_);
lean_dec(v_lemmas_2774_);
return v___x_2784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2922_, lean_object* v_lemmas_2923_, lean_object* v_ctx_2924_, lean_object* v_goals_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2922_, v_lemmas_2923_, v_ctx_2924_, v_goals_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2932_, lean_object* v_x_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
if (lean_obj_tag(v_x_2932_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = l_List_reverse___redArg(v_x_2933_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
else
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2966_; 
v_head_2941_ = lean_ctor_get(v_x_2932_, 0);
v_tail_2942_ = lean_ctor_get(v_x_2932_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_x_2932_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2944_ = v_x_2932_;
v_isShared_2945_ = v_isSharedCheck_2966_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_head_2941_);
lean_dec(v_x_2932_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2966_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Expr_applySymm(v_head_2941_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_x_2933_);
lean_ctor_set(v___x_2944_, 0, v_a_2947_);
v___x_2949_ = v___x_2944_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2947_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_x_2933_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
v_x_2932_ = v_tail_2942_;
v_x_2933_ = v___x_2949_;
goto _start;
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2965_; 
lean_del_object(v___x_2944_);
v_a_2952_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2954_ = v___x_2946_;
v_isShared_2955_ = v_isSharedCheck_2965_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2946_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2965_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
uint8_t v___x_2956_; 
v___x_2956_ = l_Lean_Exception_isInterrupt(v_a_2952_);
if (v___x_2956_ == 0)
{
uint8_t v___x_2957_; 
lean_inc(v_a_2952_);
v___x_2957_ = l_Lean_Exception_isRuntime(v_a_2952_);
if (v___x_2957_ == 0)
{
lean_del_object(v___x_2954_);
lean_dec(v_a_2952_);
v_x_2932_ = v_tail_2942_;
goto _start;
}
else
{
lean_object* v___x_2960_; 
lean_dec(v_tail_2942_);
lean_dec(v_x_2933_);
if (v_isShared_2955_ == 0)
{
v___x_2960_ = v___x_2954_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2952_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
lean_object* v___x_2963_; 
lean_dec(v_tail_2942_);
lean_dec(v_x_2933_);
if (v_isShared_2955_ == 0)
{
v___x_2963_ = v___x_2954_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2952_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2967_, lean_object* v_x_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2967_, v_x_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2975_, lean_object* v_hyps_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
if (v_symm_2975_ == 0)
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_hyps_2976_);
return v___x_2982_;
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_box(0);
lean_inc(v_hyps_2976_);
v___x_2984_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2976_, v___x_2983_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2993_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = l_List_appendTR___redArg(v_hyps_2976_, v_a_2985_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2989_);
v___x_2991_ = v___x_2987_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_dec(v_hyps_2976_);
return v___x_2984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_2994_, lean_object* v_hyps_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
uint8_t v_symm_boxed_3001_; lean_object* v_res_3002_; 
v_symm_boxed_3001_ = lean_unbox(v_symm_2994_);
v_res_3002_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3001_, v_hyps_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3003_, size_t v_sz_3004_, size_t v_i_3005_, lean_object* v_b_3006_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_usize_dec_lt(v_i_3005_, v_sz_3004_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_b_3006_);
return v___x_3009_;
}
else
{
lean_object* v_snd_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3028_; 
v_snd_3010_ = lean_ctor_get(v_b_3006_, 1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_b_3006_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v_b_3006_, 0);
lean_dec(v_unused_3029_);
v___x_3012_ = v_b_3006_;
v_isShared_3013_ = v_isSharedCheck_3028_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_snd_3010_);
lean_dec(v_b_3006_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3028_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v_a_3016_; lean_object* v_a_3023_; 
v___x_3014_ = lean_box(0);
v_a_3023_ = lean_array_uget_borrowed(v_as_3003_, v_i_3005_);
if (lean_obj_tag(v_a_3023_) == 0)
{
v_a_3016_ = v_snd_3010_;
goto v___jp_3015_;
}
else
{
lean_object* v_val_3024_; uint8_t v___x_3025_; 
v_val_3024_ = lean_ctor_get(v_a_3023_, 0);
v___x_3025_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_inc(v_val_3024_);
v___x_3026_ = l_Lean_LocalDecl_toExpr(v_val_3024_);
v___x_3027_ = lean_array_push(v_snd_3010_, v___x_3026_);
v_a_3016_ = v___x_3027_;
goto v___jp_3015_;
}
else
{
v_a_3016_ = v_snd_3010_;
goto v___jp_3015_;
}
}
v___jp_3015_:
{
lean_object* v___x_3018_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v_a_3016_);
lean_ctor_set(v___x_3012_, 0, v___x_3014_);
v___x_3018_ = v___x_3012_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_a_3016_);
v___x_3018_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
size_t v___x_3019_; size_t v___x_3020_; 
v___x_3019_ = ((size_t)1ULL);
v___x_3020_ = lean_usize_add(v_i_3005_, v___x_3019_);
v_i_3005_ = v___x_3020_;
v_b_3006_ = v___x_3018_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3030_, lean_object* v_sz_3031_, lean_object* v_i_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_){
_start:
{
size_t v_sz_boxed_3035_; size_t v_i_boxed_3036_; lean_object* v_res_3037_; 
v_sz_boxed_3035_ = lean_unbox_usize(v_sz_3031_);
lean_dec(v_sz_3031_);
v_i_boxed_3036_ = lean_unbox_usize(v_i_3032_);
lean_dec(v_i_3032_);
v_res_3037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3030_, v_sz_boxed_3035_, v_i_boxed_3036_, v_b_3033_);
lean_dec_ref(v_as_3030_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3038_, size_t v_sz_3039_, size_t v_i_3040_, lean_object* v_b_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_usize_dec_lt(v_i_3040_, v_sz_3039_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_b_3041_);
return v___x_3050_;
}
else
{
lean_object* v_snd_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3069_; 
v_snd_3051_ = lean_ctor_get(v_b_3041_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_b_3041_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v_b_3041_, 0);
lean_dec(v_unused_3070_);
v___x_3053_ = v_b_3041_;
v_isShared_3054_ = v_isSharedCheck_3069_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_snd_3051_);
lean_dec(v_b_3041_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3069_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; lean_object* v_a_3057_; lean_object* v_a_3064_; 
v___x_3055_ = lean_box(0);
v_a_3064_ = lean_array_uget_borrowed(v_as_3038_, v_i_3040_);
if (lean_obj_tag(v_a_3064_) == 0)
{
v_a_3057_ = v_snd_3051_;
goto v___jp_3056_;
}
else
{
lean_object* v_val_3065_; uint8_t v___x_3066_; 
v_val_3065_ = lean_ctor_get(v_a_3064_, 0);
v___x_3066_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_inc(v_val_3065_);
v___x_3067_ = l_Lean_LocalDecl_toExpr(v_val_3065_);
v___x_3068_ = lean_array_push(v_snd_3051_, v___x_3067_);
v_a_3057_ = v___x_3068_;
goto v___jp_3056_;
}
else
{
v_a_3057_ = v_snd_3051_;
goto v___jp_3056_;
}
}
v___jp_3056_:
{
lean_object* v___x_3059_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 1, v_a_3057_);
lean_ctor_set(v___x_3053_, 0, v___x_3055_);
v___x_3059_ = v___x_3053_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_a_3057_);
v___x_3059_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((size_t)1ULL);
v___x_3061_ = lean_usize_add(v_i_3040_, v___x_3060_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3038_, v_sz_3039_, v___x_3061_, v___x_3059_);
return v___x_3062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3071_, lean_object* v_sz_3072_, lean_object* v_i_3073_, lean_object* v_b_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
size_t v_sz_boxed_3082_; size_t v_i_boxed_3083_; lean_object* v_res_3084_; 
v_sz_boxed_3082_ = lean_unbox_usize(v_sz_3072_);
lean_dec(v_sz_3072_);
v_i_boxed_3083_ = lean_unbox_usize(v_i_3073_);
lean_dec(v_i_3073_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3071_, v_sz_boxed_3082_, v_i_boxed_3083_, v_b_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v_as_3071_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3085_, size_t v_sz_3086_, size_t v_i_3087_, lean_object* v_b_3088_){
_start:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_usize_dec_lt(v_i_3087_, v_sz_3086_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_b_3088_);
return v___x_3091_;
}
else
{
lean_object* v_snd_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3110_; 
v_snd_3092_ = lean_ctor_get(v_b_3088_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_b_3088_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v_b_3088_, 0);
lean_dec(v_unused_3111_);
v___x_3094_ = v_b_3088_;
v_isShared_3095_ = v_isSharedCheck_3110_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_snd_3092_);
lean_dec(v_b_3088_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3110_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v_a_3098_; lean_object* v_a_3105_; 
v___x_3096_ = lean_box(0);
v_a_3105_ = lean_array_uget_borrowed(v_as_3085_, v_i_3087_);
if (lean_obj_tag(v_a_3105_) == 0)
{
v_a_3098_ = v_snd_3092_;
goto v___jp_3097_;
}
else
{
lean_object* v_val_3106_; uint8_t v___x_3107_; 
v_val_3106_ = lean_ctor_get(v_a_3105_, 0);
v___x_3107_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_inc(v_val_3106_);
v___x_3108_ = l_Lean_LocalDecl_toExpr(v_val_3106_);
v___x_3109_ = lean_array_push(v_snd_3092_, v___x_3108_);
v_a_3098_ = v___x_3109_;
goto v___jp_3097_;
}
else
{
v_a_3098_ = v_snd_3092_;
goto v___jp_3097_;
}
}
v___jp_3097_:
{
lean_object* v___x_3100_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 1, v_a_3098_);
lean_ctor_set(v___x_3094_, 0, v___x_3096_);
v___x_3100_ = v___x_3094_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_a_3098_);
v___x_3100_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
size_t v___x_3101_; size_t v___x_3102_; 
v___x_3101_ = ((size_t)1ULL);
v___x_3102_ = lean_usize_add(v_i_3087_, v___x_3101_);
v_i_3087_ = v___x_3102_;
v_b_3088_ = v___x_3100_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3112_, lean_object* v_sz_3113_, lean_object* v_i_3114_, lean_object* v_b_3115_, lean_object* v___y_3116_){
_start:
{
size_t v_sz_boxed_3117_; size_t v_i_boxed_3118_; lean_object* v_res_3119_; 
v_sz_boxed_3117_ = lean_unbox_usize(v_sz_3113_);
lean_dec(v_sz_3113_);
v_i_boxed_3118_ = lean_unbox_usize(v_i_3114_);
lean_dec(v_i_3114_);
v_res_3119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3112_, v_sz_boxed_3117_, v_i_boxed_3118_, v_b_3115_);
lean_dec_ref(v_as_3112_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3120_, size_t v_sz_3121_, size_t v_i_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_usize_dec_lt(v_i_3122_, v_sz_3121_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_b_3123_);
return v___x_3132_;
}
else
{
lean_object* v_snd_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3151_; 
v_snd_3133_ = lean_ctor_get(v_b_3123_, 1);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_b_3123_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_b_3123_, 0);
lean_dec(v_unused_3152_);
v___x_3135_ = v_b_3123_;
v_isShared_3136_ = v_isSharedCheck_3151_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_snd_3133_);
lean_dec(v_b_3123_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3151_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v_a_3139_; lean_object* v_a_3146_; 
v___x_3137_ = lean_box(0);
v_a_3146_ = lean_array_uget_borrowed(v_as_3120_, v_i_3122_);
if (lean_obj_tag(v_a_3146_) == 0)
{
v_a_3139_ = v_snd_3133_;
goto v___jp_3138_;
}
else
{
lean_object* v_val_3147_; uint8_t v___x_3148_; 
v_val_3147_ = lean_ctor_get(v_a_3146_, 0);
v___x_3148_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_inc(v_val_3147_);
v___x_3149_ = l_Lean_LocalDecl_toExpr(v_val_3147_);
v___x_3150_ = lean_array_push(v_snd_3133_, v___x_3149_);
v_a_3139_ = v___x_3150_;
goto v___jp_3138_;
}
else
{
v_a_3139_ = v_snd_3133_;
goto v___jp_3138_;
}
}
v___jp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 1, v_a_3139_);
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3141_ = v___x_3135_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_a_3139_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3122_, v___x_3142_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3120_, v_sz_3121_, v___x_3143_, v___x_3141_);
return v___x_3144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3153_, lean_object* v_sz_3154_, lean_object* v_i_3155_, lean_object* v_b_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
size_t v_sz_boxed_3164_; size_t v_i_boxed_3165_; lean_object* v_res_3166_; 
v_sz_boxed_3164_ = lean_unbox_usize(v_sz_3154_);
lean_dec(v_sz_3154_);
v_i_boxed_3165_ = lean_unbox_usize(v_i_3155_);
lean_dec(v_i_3155_);
v_res_3166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3153_, v_sz_boxed_3164_, v_i_boxed_3165_, v_b_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec_ref(v_as_3153_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3167_, lean_object* v_n_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
if (lean_obj_tag(v_n_3168_) == 0)
{
lean_object* v_cs_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; size_t v_sz_3180_; size_t v___x_3181_; lean_object* v___x_3182_; 
v_cs_3177_ = lean_ctor_get(v_n_3168_, 0);
v___x_3178_ = lean_box(0);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v_b_3169_);
v_sz_3180_ = lean_array_size(v_cs_3177_);
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3167_, v_cs_3177_, v_sz_3180_, v___x_3181_, v___x_3179_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3197_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3197_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3197_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_fst_3187_; 
v_fst_3187_ = lean_ctor_get(v_a_3183_, 0);
if (lean_obj_tag(v_fst_3187_) == 0)
{
lean_object* v_snd_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
v_snd_3188_ = lean_ctor_get(v_a_3183_, 1);
lean_inc(v_snd_3188_);
lean_dec(v_a_3183_);
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_snd_3188_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3189_);
v___x_3191_ = v___x_3185_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
else
{
lean_object* v_val_3193_; lean_object* v___x_3195_; 
lean_inc_ref(v_fst_3187_);
lean_dec(v_a_3183_);
v_val_3193_ = lean_ctor_get(v_fst_3187_, 0);
lean_inc(v_val_3193_);
lean_dec_ref_known(v_fst_3187_, 1);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_val_3193_);
v___x_3195_ = v___x_3185_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_val_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v_a_3198_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3182_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3182_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_vs_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; size_t v_sz_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v_vs_3206_ = lean_ctor_get(v_n_3168_, 0);
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set(v___x_3208_, 1, v_b_3169_);
v_sz_3209_ = lean_array_size(v_vs_3206_);
v___x_3210_ = ((size_t)0ULL);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3206_, v_sz_3209_, v___x_3210_, v___x_3208_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3226_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3226_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3226_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_fst_3216_; 
v_fst_3216_ = lean_ctor_get(v_a_3212_, 0);
if (lean_obj_tag(v_fst_3216_) == 0)
{
lean_object* v_snd_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
v_snd_3217_ = lean_ctor_get(v_a_3212_, 1);
lean_inc(v_snd_3217_);
lean_dec(v_a_3212_);
v___x_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_snd_3217_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3218_);
v___x_3220_ = v___x_3214_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
else
{
lean_object* v_val_3222_; lean_object* v___x_3224_; 
lean_inc_ref(v_fst_3216_);
lean_dec(v_a_3212_);
v_val_3222_ = lean_ctor_get(v_fst_3216_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v_fst_3216_, 1);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_val_3222_);
v___x_3224_ = v___x_3214_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_val_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
v_a_3227_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3211_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3211_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3235_, lean_object* v_as_3236_, size_t v_sz_3237_, size_t v_i_3238_, lean_object* v_b_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_usize_dec_lt(v_i_3238_, v_sz_3237_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_b_3239_);
return v___x_3248_;
}
else
{
lean_object* v_snd_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3283_; 
v_snd_3249_ = lean_ctor_get(v_b_3239_, 1);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_b_3239_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; 
v_unused_3284_ = lean_ctor_get(v_b_3239_, 0);
lean_dec(v_unused_3284_);
v___x_3251_ = v_b_3239_;
v_isShared_3252_ = v_isSharedCheck_3283_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_snd_3249_);
lean_dec(v_b_3239_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3283_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v_a_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_box(0);
v_a_3254_ = lean_array_uget_borrowed(v_as_3236_, v_i_3238_);
lean_inc(v_snd_3249_);
v___x_3255_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3235_, v_a_3254_, v_snd_3249_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3274_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3274_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3274_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
if (lean_obj_tag(v_a_3256_) == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_a_3256_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3260_);
v___x_3262_ = v___x_3251_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_snd_3249_);
v___x_3262_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3264_; 
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v___x_3262_);
v___x_3264_ = v___x_3258_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; 
lean_del_object(v___x_3258_);
lean_dec(v_snd_3249_);
v_a_3267_ = lean_ctor_get(v_a_3256_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v_a_3256_, 1);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v_a_3267_);
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3269_ = v___x_3251_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_a_3267_);
v___x_3269_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
size_t v___x_3270_; size_t v___x_3271_; 
v___x_3270_ = ((size_t)1ULL);
v___x_3271_ = lean_usize_add(v_i_3238_, v___x_3270_);
v_i_3238_ = v___x_3271_;
v_b_3239_ = v___x_3269_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_del_object(v___x_3251_);
lean_dec(v_snd_3249_);
v_a_3275_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3255_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3255_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3285_, lean_object* v_as_3286_, lean_object* v_sz_3287_, lean_object* v_i_3288_, lean_object* v_b_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
size_t v_sz_boxed_3297_; size_t v_i_boxed_3298_; lean_object* v_res_3299_; 
v_sz_boxed_3297_ = lean_unbox_usize(v_sz_3287_);
lean_dec(v_sz_3287_);
v_i_boxed_3298_ = lean_unbox_usize(v_i_3288_);
lean_dec(v_i_3288_);
v_res_3299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3285_, v_as_3286_, v_sz_boxed_3297_, v_i_boxed_3298_, v_b_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v_as_3286_);
lean_dec_ref(v_init_3285_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3300_, lean_object* v_n_3301_, lean_object* v_b_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3300_, v_n_3301_, v_b_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v_n_3301_);
lean_dec_ref(v_init_3300_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3311_, lean_object* v_init_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_root_3320_; lean_object* v_tail_3321_; lean_object* v___x_3322_; 
v_root_3320_ = lean_ctor_get(v_t_3311_, 0);
v_tail_3321_ = lean_ctor_get(v_t_3311_, 1);
lean_inc_ref(v_init_3312_);
v___x_3322_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3312_, v_root_3320_, v_init_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec_ref(v_init_3312_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3359_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3359_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3359_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
if (lean_obj_tag(v_a_3323_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; 
v_a_3327_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v_a_3323_, 1);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v_a_3327_);
v___x_3329_ = v___x_3325_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; size_t v_sz_3334_; size_t v___x_3335_; lean_object* v___x_3336_; 
lean_del_object(v___x_3325_);
v_a_3331_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v_a_3323_, 1);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v_a_3331_);
v_sz_3334_ = lean_array_size(v_tail_3321_);
v___x_3335_ = ((size_t)0ULL);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3321_, v_sz_3334_, v___x_3335_, v___x_3333_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3350_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_fst_3341_; 
v_fst_3341_ = lean_ctor_get(v_a_3337_, 0);
if (lean_obj_tag(v_fst_3341_) == 0)
{
lean_object* v_snd_3342_; lean_object* v___x_3344_; 
v_snd_3342_ = lean_ctor_get(v_a_3337_, 1);
lean_inc(v_snd_3342_);
lean_dec(v_a_3337_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v_snd_3342_);
v___x_3344_ = v___x_3339_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_snd_3342_);
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
lean_object* v_val_3346_; lean_object* v___x_3348_; 
lean_inc_ref(v_fst_3341_);
lean_dec(v_a_3337_);
v_val_3346_ = lean_ctor_get(v_fst_3341_, 0);
lean_inc(v_val_3346_);
lean_dec_ref_known(v_fst_3341_, 1);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v_val_3346_);
v___x_3348_ = v___x_3339_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_val_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
v_a_3351_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3336_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3336_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
v_a_3360_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3322_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3322_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3368_, lean_object* v_init_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3368_, v_init_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec_ref(v_t_3368_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_lctx_3387_; lean_object* v_decls_3388_; lean_object* v_hs_3389_; lean_object* v___x_3390_; 
v_lctx_3387_ = lean_ctor_get(v___y_3382_, 2);
v_decls_3388_ = lean_ctor_get(v_lctx_3387_, 1);
v_hs_3389_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3390_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3388_, v_hs_3389_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3399_, lean_object* v_cfg_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
if (v_only_3399_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_toApplyRulesConfig_3409_; lean_object* v_a_3410_; uint8_t v_symm_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_toApplyRulesConfig_3409_ = lean_ctor_get(v_cfg_3400_, 0);
v_a_3410_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3408_, 1);
v_symm_3411_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3409_, sizeof(void*)*2 + 1);
v___x_3412_ = lean_array_to_list(v_a_3410_);
v___x_3413_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3411_, v___x_3412_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3413_;
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_a_3414_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3408_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3408_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3424_, lean_object* v_cfg_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v_only_boxed_3433_; lean_object* v_res_3434_; 
v_only_boxed_3433_ = lean_unbox(v_only_3424_);
v_res_3434_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3433_, v_cfg_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec_ref(v_cfg_3425_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3435_, lean_object* v_lemmas_3436_, uint8_t v_only_3437_, lean_object* v_g_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_toApplyRulesConfig_3444_; uint8_t v_intro_3445_; uint8_t v_constructor_3446_; uint8_t v_suggestions_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3460_; 
v_toApplyRulesConfig_3444_ = lean_ctor_get(v_cfg_3435_, 0);
v_intro_3445_ = lean_ctor_get_uint8(v_cfg_3435_, sizeof(void*)*1 + 1);
v_constructor_3446_ = lean_ctor_get_uint8(v_cfg_3435_, sizeof(void*)*1 + 2);
v_suggestions_3447_ = lean_ctor_get_uint8(v_cfg_3435_, sizeof(void*)*1 + 3);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_cfg_3435_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3449_ = v_cfg_3435_;
v_isShared_3450_ = v_isSharedCheck_3460_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_toApplyRulesConfig_3444_);
lean_dec(v_cfg_3435_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3460_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v_ctx_3452_; uint8_t v___x_3453_; lean_object* v___x_3455_; 
v___x_3451_ = lean_box(v_only_3437_);
v_ctx_3452_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3452_, 0, v___x_3451_);
v___x_3453_ = 0;
if (v_isShared_3450_ == 0)
{
v___x_3455_ = v___x_3449_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_toApplyRulesConfig_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3459_, sizeof(void*)*1 + 1, v_intro_3445_);
lean_ctor_set_uint8(v_reuseFailAlloc_3459_, sizeof(void*)*1 + 2, v_constructor_3446_);
lean_ctor_set_uint8(v_reuseFailAlloc_3459_, sizeof(void*)*1 + 3, v_suggestions_3447_);
v___x_3455_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_ctor_set_uint8(v___x_3455_, sizeof(void*)*1, v___x_3453_);
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_g_3438_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3455_, v_lemmas_3436_, v_ctx_3452_, v___x_3457_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3461_, lean_object* v_lemmas_3462_, lean_object* v_only_3463_, lean_object* v_g_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
uint8_t v_only_boxed_3470_; lean_object* v_res_3471_; 
v_only_boxed_3470_ = lean_unbox(v_only_3463_);
v_res_3471_ = l_Lean_MVarId_applyRules(v_cfg_3461_, v_lemmas_3462_, v_only_boxed_3470_, v_g_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3472_, size_t v_sz_3473_, size_t v_i_3474_, lean_object* v_b_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3472_, v_sz_3473_, v_i_3474_, v_b_3475_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3484_, lean_object* v_sz_3485_, lean_object* v_i_3486_, lean_object* v_b_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3485_);
lean_dec(v_sz_3485_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3486_);
lean_dec(v_i_3486_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3484_, v_sz_boxed_3495_, v_i_boxed_3496_, v_b_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_as_3484_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3498_, size_t v_sz_3499_, size_t v_i_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3498_, v_sz_3499_, v_i_3500_, v_b_3501_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3510_, lean_object* v_sz_3511_, lean_object* v_i_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
size_t v_sz_boxed_3521_; size_t v_i_boxed_3522_; lean_object* v_res_3523_; 
v_sz_boxed_3521_ = lean_unbox_usize(v_sz_3511_);
lean_dec(v_sz_3511_);
v_i_boxed_3522_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3510_, v_sz_boxed_3521_, v_i_boxed_3522_, v_b_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v_as_3510_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v___x_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_box(0);
v___x_3533_ = 1;
v___x_3534_ = l_Lean_Elab_Term_elabTerm(v_t_3524_, v___x_3532_, v___x_3533_, v___x_3533_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_ref_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v_ref_3549_ = lean_ctor_get(v___y_3546_, 2);
v___x_3550_ = 0;
v___x_3551_ = l_Lean_SourceInfo_fromRef(v_ref_3549_, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
return v_res_3558_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object* v_a_3559_, lean_object* v_x_3560_){
_start:
{
if (lean_obj_tag(v_x_3560_) == 0)
{
uint8_t v___x_3561_; 
v___x_3561_ = 0;
return v___x_3561_;
}
else
{
lean_object* v_head_3562_; lean_object* v_tail_3563_; uint8_t v___x_3564_; 
v_head_3562_ = lean_ctor_get(v_x_3560_, 0);
v_tail_3563_ = lean_ctor_get(v_x_3560_, 1);
v___x_3564_ = lean_expr_eqv(v_a_3559_, v_head_3562_);
if (v___x_3564_ == 0)
{
v_x_3560_ = v_tail_3563_;
goto _start;
}
else
{
return v___x_3564_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object* v_a_3566_, lean_object* v_x_3567_){
_start:
{
uint8_t v_res_3568_; lean_object* v_r_3569_; 
v_res_3568_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3566_, v_x_3567_);
lean_dec(v_x_3567_);
lean_dec_ref(v_a_3566_);
v_r_3569_ = lean_box(v_res_3568_);
return v_r_3569_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(lean_object* v_ys_3570_, lean_object* v_x_3571_){
_start:
{
uint8_t v___x_3572_; 
v___x_3572_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_x_3571_, v_ys_3570_);
if (v___x_3572_ == 0)
{
uint8_t v___x_3573_; 
v___x_3573_ = 1;
return v___x_3573_;
}
else
{
uint8_t v___x_3574_; 
v___x_3574_ = 0;
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed(lean_object* v_ys_3575_, lean_object* v_x_3576_){
_start:
{
uint8_t v_res_3577_; lean_object* v_r_3578_; 
v_res_3577_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0(v_ys_3575_, v_x_3576_);
lean_dec_ref(v_x_3576_);
lean_dec(v_ys_3575_);
v_r_3578_ = lean_box(v_res_3577_);
return v_r_3578_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_xs_3579_, lean_object* v_ys_3580_){
_start:
{
lean_object* v___f_3581_; lean_object* v___x_3582_; 
v___f_3581_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3581_, 0, v_ys_3580_);
v___x_3582_ = l_List_filter___redArg(v___f_3581_, v_xs_3579_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object* v_x_3583_, lean_object* v_x_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = l_List_reverse___redArg(v_x_3584_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
else
{
lean_object* v_head_3594_; lean_object* v_tail_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3613_; 
v_head_3594_ = lean_ctor_get(v_x_3583_, 0);
v_tail_3595_ = lean_ctor_get(v_x_3583_, 1);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_x_3583_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3597_ = v_x_3583_;
v_isShared_3598_ = v_isSharedCheck_3613_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_tail_3595_);
lean_inc(v_head_3594_);
lean_dec(v_x_3583_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3613_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; 
v___x_3599_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3594_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v_x_3584_);
lean_ctor_set(v___x_3597_, 0, v_a_3600_);
v___x_3602_ = v___x_3597_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3600_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_x_3584_);
v___x_3602_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
v_x_3583_ = v_tail_3595_;
v_x_3584_ = v___x_3602_;
goto _start;
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_del_object(v___x_3597_);
lean_dec(v_tail_3595_);
lean_dec(v_x_3584_);
v_a_3605_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3599_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3599_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_x_3614_, lean_object* v_x_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3614_, v_x_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3624_, uint8_t v_noDefaults_3625_, uint8_t v_star_3626_, lean_object* v_cfg_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
if (v_noDefaults_3625_ == 0)
{
goto v___jp_3635_;
}
else
{
if (v_star_3626_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_remove_3624_);
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
else
{
goto v___jp_3635_;
}
}
v___jp_3635_:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = lean_box(0);
v___x_3639_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_remove_3624_, v___x_3638_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_toApplyRulesConfig_3640_; lean_object* v_a_3641_; uint8_t v_symm_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_toApplyRulesConfig_3640_ = lean_ctor_get(v_cfg_3627_, 0);
v_a_3641_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3639_, 1);
v_symm_3642_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3640_, sizeof(void*)*2 + 1);
v___x_3643_ = lean_array_to_list(v_a_3637_);
v___x_3644_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v___x_3643_, v_a_3641_);
v___x_3645_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3642_, v___x_3644_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3645_;
}
else
{
lean_dec(v_a_3637_);
return v___x_3639_;
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec(v_remove_3624_);
v_a_3646_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3636_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3636_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3656_, lean_object* v_noDefaults_3657_, lean_object* v_star_3658_, lean_object* v_cfg_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
uint8_t v_noDefaults_boxed_3667_; uint8_t v_star_boxed_3668_; lean_object* v_res_3669_; 
v_noDefaults_boxed_3667_ = lean_unbox(v_noDefaults_3657_);
v_star_boxed_3668_ = lean_unbox(v_star_3658_);
v_res_3669_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3656_, v_noDefaults_boxed_3667_, v_star_boxed_3668_, v_cfg_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec_ref(v_cfg_3659_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t v_sz_3670_, size_t v_i_3671_, lean_object* v_bs_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
uint8_t v___x_3676_; 
v___x_3676_ = lean_usize_dec_lt(v_i_3671_, v_sz_3670_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3677_, 0, v_bs_3672_);
return v___x_3677_;
}
else
{
lean_object* v_v_3678_; lean_object* v___x_3679_; lean_object* v_bs_x27_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_v_3678_ = lean_array_uget(v_bs_3672_, v_i_3671_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v_bs_x27_3680_ = lean_array_uset(v_bs_3672_, v_i_3671_, v___x_3679_);
v___x_3681_ = l_Lean_Syntax_getId(v_v_3678_);
lean_dec(v_v_3678_);
v___x_3682_ = l_Lean_labelled(v___x_3681_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; size_t v___x_3684_; size_t v___x_3685_; lean_object* v___x_3686_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = ((size_t)1ULL);
v___x_3685_ = lean_usize_add(v_i_3671_, v___x_3684_);
v___x_3686_ = lean_array_uset(v_bs_x27_3680_, v_i_3671_, v_a_3683_);
v_i_3671_ = v___x_3685_;
v_bs_3672_ = v___x_3686_;
goto _start;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v_bs_x27_3680_);
v_a_3688_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3682_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3682_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_bs_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
size_t v_sz_boxed_3702_; size_t v_i_boxed_3703_; lean_object* v_res_3704_; 
v_sz_boxed_3702_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3703_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_boxed_3702_, v_i_boxed_3703_, v_bs_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3705_, size_t v_i_3706_, size_t v_stop_3707_, lean_object* v_b_3708_){
_start:
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_usize_dec_eq(v_i_3706_, v_stop_3707_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; lean_object* v___x_3711_; size_t v___x_3712_; size_t v___x_3713_; 
v___x_3710_ = lean_array_uget_borrowed(v_as_3705_, v_i_3706_);
v___x_3711_ = l_Array_append___redArg(v_b_3708_, v___x_3710_);
v___x_3712_ = ((size_t)1ULL);
v___x_3713_ = lean_usize_add(v_i_3706_, v___x_3712_);
v_i_3706_ = v___x_3713_;
v_b_3708_ = v___x_3711_;
goto _start;
}
else
{
return v_b_3708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3715_, lean_object* v_i_3716_, lean_object* v_stop_3717_, lean_object* v_b_3718_){
_start:
{
size_t v_i_boxed_3719_; size_t v_stop_boxed_3720_; lean_object* v_res_3721_; 
v_i_boxed_3719_ = lean_unbox_usize(v_i_3716_);
lean_dec(v_i_3716_);
v_stop_boxed_3720_ = lean_unbox_usize(v_stop_3717_);
lean_dec(v_stop_3717_);
v_res_3721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3715_, v_i_boxed_3719_, v_stop_boxed_3720_, v_b_3718_);
lean_dec_ref(v_as_3715_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3722_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
if (lean_obj_tag(v_a_3740_) == 0)
{
lean_object* v___x_3742_; 
v___x_3742_ = l_List_reverse___redArg(v_a_3741_);
return v___x_3742_;
}
else
{
lean_object* v_head_3743_; lean_object* v_tail_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3753_; 
v_head_3743_ = lean_ctor_get(v_a_3740_, 0);
v_tail_3744_ = lean_ctor_get(v_a_3740_, 1);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_a_3740_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3746_ = v_a_3740_;
v_isShared_3747_ = v_isSharedCheck_3753_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_tail_3744_);
lean_inc(v_head_3743_);
lean_dec(v_a_3740_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3753_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___f_3748_; lean_object* v___x_3750_; 
v___f_3748_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3748_, 0, v_head_3743_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v_a_3741_);
lean_ctor_set(v___x_3746_, 0, v___f_3748_);
v___x_3750_ = v___x_3746_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___f_3748_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_a_3741_);
v___x_3750_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
v_a_3740_ = v_tail_3744_;
v_a_3741_ = v___x_3750_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
if (lean_obj_tag(v_a_3754_) == 0)
{
lean_object* v___x_3756_; 
v___x_3756_ = l_List_reverse___redArg(v_a_3755_);
return v___x_3756_;
}
else
{
lean_object* v_head_3757_; lean_object* v_tail_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3767_; 
v_head_3757_ = lean_ctor_get(v_a_3754_, 0);
v_tail_3758_ = lean_ctor_get(v_a_3754_, 1);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_a_3754_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3760_ = v_a_3754_;
v_isShared_3761_ = v_isSharedCheck_3767_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_tail_3758_);
lean_inc(v_head_3757_);
lean_dec(v_a_3754_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3767_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3762_, 0, v_head_3757_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 1, v_a_3755_);
lean_ctor_set(v___x_3760_, 0, v___x_3762_);
v___x_3764_ = v___x_3760_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3762_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_a_3755_);
v___x_3764_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
v_a_3754_ = v_tail_3758_;
v_a_3755_ = v___x_3764_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3770_ = l_Lean_stringToMessageData(v___x_3769_);
return v___x_3770_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3773_ = l_String_toRawSubstring_x27(v___x_3772_);
return v___x_3773_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3784_ = l_String_toRawSubstring_x27(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12));
v___x_3795_ = l_String_toRawSubstring_x27(v___x_3794_);
return v___x_3795_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3806_ = l_String_toRawSubstring_x27(v___x_3805_);
return v___x_3806_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3819_ = l_Lean_stringToMessageData(v___x_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3820_, uint8_t v_star_3821_, lean_object* v_add_3822_, lean_object* v_remove_3823_, lean_object* v_use_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___f_3855_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; 
v___x_3853_ = lean_box(v_noDefaults_3820_);
v___x_3854_ = lean_box(v_star_3821_);
lean_inc(v_remove_3823_);
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3855_, 0, v_remove_3823_);
lean_closure_set(v___f_3855_, 1, v___x_3853_);
lean_closure_set(v___f_3855_, 2, v___x_3854_);
if (v_star_3821_ == 0)
{
v___y_3872_ = v_a_3825_;
v___y_3873_ = v_a_3826_;
v___y_3874_ = v_a_3827_;
v___y_3875_ = v_a_3828_;
goto v___jp_3871_;
}
else
{
if (v_noDefaults_3820_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v___f_3855_);
lean_dec_ref(v_use_3824_);
lean_dec(v_remove_3823_);
lean_dec(v_add_3822_);
v___x_3932_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3933_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3932_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3933_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
else
{
v___y_3872_ = v_a_3825_;
v___y_3873_ = v_a_3826_;
v___y_3874_ = v_a_3827_;
v___y_3875_ = v_a_3828_;
goto v___jp_3871_;
}
}
v___jp_3830_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___y_3832_);
lean_ctor_set(v___x_3833_, 1, v___y_3831_);
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
v___jp_3835_:
{
uint8_t v___x_3842_; 
v___x_3842_ = l_List_isEmpty___redArg(v_remove_3823_);
lean_dec(v_remove_3823_);
if (v___x_3842_ == 0)
{
if (v_noDefaults_3820_ == 0)
{
v___y_3831_ = v___y_3838_;
v___y_3832_ = v___y_3841_;
goto v___jp_3830_;
}
else
{
if (v_star_3821_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3838_);
v___x_3843_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3844_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3843_, v___y_3837_, v___y_3840_, v___y_3839_, v___y_3836_);
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
else
{
v___y_3831_ = v___y_3838_;
v___y_3832_ = v___y_3841_;
goto v___jp_3830_;
}
}
}
else
{
v___y_3831_ = v___y_3838_;
v___y_3832_ = v___y_3841_;
goto v___jp_3830_;
}
}
v___jp_3856_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_array_to_list(v___y_3863_);
lean_inc(v___y_3860_);
v___x_3865_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3864_, v___y_3860_);
if (v_noDefaults_3820_ == 0)
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3822_, v___y_3860_);
v___x_3867_ = l_List_appendTR___redArg(v___x_3866_, v___x_3865_);
v___x_3868_ = l_List_appendTR___redArg(v___x_3867_, v___y_3859_);
v___y_3836_ = v___y_3858_;
v___y_3837_ = v___y_3857_;
v___y_3838_ = v___f_3855_;
v___y_3839_ = v___y_3861_;
v___y_3840_ = v___y_3862_;
v___y_3841_ = v___x_3868_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_dec(v___y_3859_);
v___x_3869_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3822_, v___y_3860_);
v___x_3870_ = l_List_appendTR___redArg(v___x_3869_, v___x_3865_);
v___y_3836_ = v___y_3858_;
v___y_3837_ = v___y_3857_;
v___y_3838_ = v___f_3855_;
v___y_3839_ = v___y_3861_;
v___y_3840_ = v___y_3862_;
v___y_3841_ = v___x_3870_;
goto v___jp_3835_;
}
}
v___jp_3871_:
{
lean_object* v_toCold_3876_; lean_object* v_ref_3877_; lean_object* v_quotContext_3878_; lean_object* v_currMacroScope_3879_; uint8_t v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v_a_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v_a_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v_a_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; size_t v_sz_3914_; size_t v___x_3915_; lean_object* v___x_3916_; 
v_toCold_3876_ = lean_ctor_get(v___y_3874_, 0);
v_ref_3877_ = lean_ctor_get(v___y_3874_, 2);
v_quotContext_3878_ = lean_ctor_get(v_toCold_3876_, 8);
v_currMacroScope_3879_ = lean_ctor_get(v_toCold_3876_, 9);
v___x_3880_ = 0;
v___x_3881_ = l_Lean_SourceInfo_fromRef(v_ref_3877_, v___x_3880_);
v___x_3882_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3883_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3879_, 4);
lean_inc_n(v_quotContext_3878_, 4);
v___x_3884_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3883_, v_currMacroScope_3879_);
v___x_3885_ = lean_box(0);
v___x_3886_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6));
v___x_3887_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3881_);
lean_ctor_set(v___x_3887_, 1, v___x_3882_);
lean_ctor_set(v___x_3887_, 2, v___x_3884_);
lean_ctor_set(v___x_3887_, 3, v___x_3886_);
v___x_3888_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3888_);
v___x_3890_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8);
v___x_3891_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9));
v___x_3892_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3891_, v_currMacroScope_3879_);
v___x_3893_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3894_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3894_, 0, v_a_3889_);
lean_ctor_set(v___x_3894_, 1, v___x_3890_);
lean_ctor_set(v___x_3894_, 2, v___x_3892_);
lean_ctor_set(v___x_3894_, 3, v___x_3893_);
v___x_3895_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v___x_3897_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13);
v___x_3898_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14));
v___x_3899_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3898_, v_currMacroScope_3879_);
v___x_3900_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16));
v___x_3901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3901_, 0, v_a_3896_);
lean_ctor_set(v___x_3901_, 1, v___x_3897_);
lean_ctor_set(v___x_3901_, 2, v___x_3899_);
lean_ctor_set(v___x_3901_, 3, v___x_3900_);
v___x_3902_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref(v___x_3902_);
v___x_3904_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18);
v___x_3905_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3906_ = l_Lean_addMacroScope(v_quotContext_3878_, v___x_3905_, v_currMacroScope_3879_);
v___x_3907_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3908_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3908_, 0, v_a_3903_);
lean_ctor_set(v___x_3908_, 1, v___x_3904_);
lean_ctor_set(v___x_3908_, 2, v___x_3906_);
lean_ctor_set(v___x_3908_, 3, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
lean_ctor_set(v___x_3909_, 1, v___x_3885_);
v___x_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3901_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3894_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3887_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3912_, v___x_3885_);
v_sz_3914_ = lean_array_size(v_use_3824_);
v___x_3915_ = ((size_t)0ULL);
v___x_3916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3914_, v___x_3915_, v_use_3824_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3920_ = lean_array_get_size(v_a_3917_);
v___x_3921_ = lean_nat_dec_lt(v___x_3918_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_dec(v_a_3917_);
v___y_3857_ = v___y_3872_;
v___y_3858_ = v___y_3875_;
v___y_3859_ = v___x_3913_;
v___y_3860_ = v___x_3885_;
v___y_3861_ = v___y_3874_;
v___y_3862_ = v___y_3873_;
v___y_3863_ = v___x_3919_;
goto v___jp_3856_;
}
else
{
size_t v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_usize_of_nat(v___x_3920_);
v___x_3923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3917_, v___x_3915_, v___x_3922_, v___x_3919_);
lean_dec(v_a_3917_);
v___y_3857_ = v___y_3872_;
v___y_3858_ = v___y_3875_;
v___y_3859_ = v___x_3913_;
v___y_3860_ = v___x_3885_;
v___y_3861_ = v___y_3874_;
v___y_3862_ = v___y_3873_;
v___y_3863_ = v___x_3923_;
goto v___jp_3856_;
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v___x_3913_);
lean_dec_ref(v___f_3855_);
lean_dec(v_remove_3823_);
lean_dec(v_add_3822_);
v_a_3924_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3916_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3916_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3942_, lean_object* v_star_3943_, lean_object* v_add_3944_, lean_object* v_remove_3945_, lean_object* v_use_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
uint8_t v_noDefaults_boxed_3952_; uint8_t v_star_boxed_3953_; lean_object* v_res_3954_; 
v_noDefaults_boxed_3952_ = lean_unbox(v_noDefaults_3942_);
v_star_boxed_3953_ = lean_unbox(v_star_3943_);
v_res_3954_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3952_, v_star_boxed_3953_, v_add_3944_, v_remove_3945_, v_use_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t v_sz_3955_, size_t v_i_3956_, lean_object* v_bs_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3955_, v_i_3956_, v_bs_3957_, v___y_3960_, v___y_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object* v_sz_3964_, lean_object* v_i_3965_, lean_object* v_bs_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
size_t v_sz_boxed_3972_; size_t v_i_boxed_3973_; lean_object* v_res_3974_; 
v_sz_boxed_3972_ = lean_unbox_usize(v_sz_3964_);
lean_dec(v_sz_3964_);
v_i_boxed_3973_ = lean_unbox_usize(v_i_3965_);
lean_dec(v_i_3965_);
v_res_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_boxed_3972_, v_i_boxed_3973_, v_bs_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
return v_res_3974_;
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

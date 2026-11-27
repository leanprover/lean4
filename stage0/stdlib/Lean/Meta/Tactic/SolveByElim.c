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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object*, lean_object*);
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
uint8_t v___x_13746__boxed_300_; uint8_t v___x_13747__boxed_301_; lean_object* v_res_302_; 
v___x_13746__boxed_300_ = lean_unbox(v___x_291_);
v___x_13747__boxed_301_ = lean_unbox(v___x_292_);
v_res_302_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_13746__boxed_300_, v___x_13747__boxed_301_, v_x_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
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
uint8_t v___x_14175__boxed_623_; lean_object* v_res_624_; 
v___x_14175__boxed_623_ = lean_unbox(v___x_615_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14175__boxed_623_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
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
uint8_t v___x_14254__boxed_668_; lean_object* v_res_669_; 
v___x_14254__boxed_668_ = lean_unbox(v___x_660_);
v_res_669_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14254__boxed_668_, v_x_661_, v_x_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
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
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v_a_739_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v_a_778_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_a_790_; lean_object* v___y_793_; lean_object* v___y_794_; uint8_t v___y_795_; lean_object* v___y_796_; 
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
v___x_780_ = lean_float_of_nat(v___y_776_);
v___x_781_ = lean_float_of_nat(v___x_779_);
v___x_782_ = lean_box_float(v___x_780_);
v___x_783_ = lean_box_float(v___x_781_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_778_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_680_, v___x_681_, v___x_682_, v_options_690_, v___x_735_, v___y_777_, v___f_683_, v___x_785_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
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
v___x_799_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_795_, v_a_797_, v___x_798_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
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
v___y_777_ = v___y_794_;
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
v___y_789_ = v___y_794_;
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
v___y_789_ = v___y_794_;
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
v___y_793_ = v___x_835_;
v___y_794_ = v_a_813_;
v___y_795_ = v___x_815_;
v___y_796_ = v___x_852_;
goto v___jp_792_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v___y_793_ = v___x_835_;
v___y_794_ = v_a_813_;
v___y_795_ = v___x_815_;
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
uint8_t v_transparency_boxed_910_; uint8_t v___x_14344__boxed_911_; lean_object* v_res_912_; 
v_transparency_boxed_910_ = lean_unbox(v_transparency_896_);
v___x_14344__boxed_911_ = lean_unbox(v___x_902_);
v_res_912_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_910_, v_g_897_, v_e_898_, v_cfg_899_, v___x_900_, v___x_901_, v___x_14344__boxed_911_, v___x_903_, v___f_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
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
size_t v_x_831__boxed_1404_; size_t v_x_832__boxed_1405_; lean_object* v_res_1406_; 
v_x_831__boxed_1404_ = lean_unbox_usize(v_x_1400_);
lean_dec(v_x_1400_);
v_x_832__boxed_1405_ = lean_unbox_usize(v_x_1401_);
lean_dec(v_x_1401_);
v_res_1406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1399_, v_x_831__boxed_1404_, v_x_832__boxed_1405_, v_x_1402_, v_x_1403_);
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
lean_object* v___x_1418_; lean_object* v_mctx_1419_; lean_object* v_cache_1420_; lean_object* v_zetaDeltaFVarIds_1421_; lean_object* v_postponed_1422_; lean_object* v_diag_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1451_; 
v___x_1418_ = lean_st_ref_take(v___y_1416_);
v_mctx_1419_ = lean_ctor_get(v___x_1418_, 0);
v_cache_1420_ = lean_ctor_get(v___x_1418_, 1);
v_zetaDeltaFVarIds_1421_ = lean_ctor_get(v___x_1418_, 2);
v_postponed_1422_ = lean_ctor_get(v___x_1418_, 3);
v_diag_1423_ = lean_ctor_get(v___x_1418_, 4);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1425_ = v___x_1418_;
v_isShared_1426_ = v_isSharedCheck_1451_;
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
v_isShared_1426_ = v_isSharedCheck_1451_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_depth_1427_; lean_object* v_levelAssignDepth_1428_; lean_object* v_lmvarCounter_1429_; lean_object* v_mvarCounter_1430_; lean_object* v_lDecls_1431_; lean_object* v_decls_1432_; lean_object* v_userNames_1433_; lean_object* v_lAssignment_1434_; lean_object* v_eAssignment_1435_; lean_object* v_dAssignment_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1450_; 
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
v_isSharedCheck_1450_ = !lean_is_exclusive(v_mctx_1419_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1438_ = v_mctx_1419_;
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
else
{
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
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1435_, v_mvarId_1414_, v_val_1415_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 8, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_depth_1427_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_levelAssignDepth_1428_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_lmvarCounter_1429_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_mvarCounter_1430_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_lDecls_1431_);
lean_ctor_set(v_reuseFailAlloc_1449_, 5, v_decls_1432_);
lean_ctor_set(v_reuseFailAlloc_1449_, 6, v_userNames_1433_);
lean_ctor_set(v_reuseFailAlloc_1449_, 7, v_lAssignment_1434_);
lean_ctor_set(v_reuseFailAlloc_1449_, 8, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1449_, 9, v_dAssignment_1436_);
v___x_1443_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1443_);
v___x_1445_ = v___x_1425_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_cache_1420_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_zetaDeltaFVarIds_1421_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_postponed_1422_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_diag_1423_);
v___x_1445_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_st_ref_put(v___y_1416_, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1440_);
return v___x_1447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1452_, lean_object* v_val_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1452_, v_val_1453_, v___y_1454_);
lean_dec(v___y_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
lean_inc(v_g_1457_);
v___x_1463_ = l_Lean_MVarId_getType(v_g_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = lean_box(0);
v___x_1466_ = l_Lean_Meta_synthInstance(v_a_1464_, v___x_1465_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1457_, v_a_1467_, v___y_1459_);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1477_);
v___x_1470_ = v___x_1468_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v___x_1468_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_box(0);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_g_1457_);
v_a_1478_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1466_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1466_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_g_1457_);
v_a_1486_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1463_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1463_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1502_){
_start:
{
lean_object* v___f_1503_; lean_object* v___x_1504_; 
v___f_1503_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1504_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1502_, v___f_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1505_, lean_object* v_val_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1505_, v_val_1506_, v___y_1508_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1513_, lean_object* v_val_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1513_, v_val_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1522_, v_x_1523_, v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1526_, lean_object* v_x_1527_, size_t v_x_1528_, size_t v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1527_, v_x_1528_, v_x_1529_, v_x_1530_, v_x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
size_t v_x_1152__boxed_1539_; size_t v_x_1153__boxed_1540_; lean_object* v_res_1541_; 
v_x_1152__boxed_1539_ = lean_unbox_usize(v_x_1535_);
lean_dec(v_x_1535_);
v_x_1153__boxed_1540_ = lean_unbox_usize(v_x_1536_);
lean_dec(v_x_1536_);
v_res_1541_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1533_, v_x_1534_, v_x_1152__boxed_1539_, v_x_1153__boxed_1540_, v_x_1537_, v_x_1538_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1542_, lean_object* v_n_1543_, lean_object* v_k_1544_, lean_object* v_v_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1543_, v_k_1544_, v_v_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1547_, size_t v_depth_1548_, lean_object* v_keys_1549_, lean_object* v_vals_1550_, lean_object* v_heq_1551_, lean_object* v_i_1552_, lean_object* v_entries_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1548_, v_keys_1549_, v_vals_1550_, v_i_1552_, v_entries_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1555_, lean_object* v_depth_1556_, lean_object* v_keys_1557_, lean_object* v_vals_1558_, lean_object* v_heq_1559_, lean_object* v_i_1560_, lean_object* v_entries_1561_){
_start:
{
size_t v_depth_boxed_1562_; lean_object* v_res_1563_; 
v_depth_boxed_1562_ = lean_unbox_usize(v_depth_1556_);
lean_dec(v_depth_1556_);
v_res_1563_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1555_, v_depth_boxed_1562_, v_keys_1557_, v_vals_1558_, v_heq_1559_, v_i_1560_, v_entries_1561_);
lean_dec_ref(v_vals_1558_);
lean_dec_ref(v_keys_1557_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1565_, v_x_1566_, v_x_1567_, v_x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1570_, lean_object* v_discharge_1571_, lean_object* v_g_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v_g_1572_);
v___x_1578_ = lean_apply_6(v_discharge_1570_, v_g_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, lean_box(0));
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_dec(v_g_1572_);
lean_dec_ref(v_discharge_1571_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; uint8_t v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
v___x_1580_ = l_Lean_Exception_isInterrupt(v_a_1579_);
if (v___x_1580_ == 0)
{
uint8_t v___x_1581_; 
v___x_1581_ = l_Lean_Exception_isRuntime(v_a_1579_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref_known(v___x_1578_, 1);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
v___x_1582_ = lean_apply_6(v_discharge_1571_, v_g_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, lean_box(0));
return v___x_1582_;
}
else
{
lean_dec(v_g_1572_);
lean_dec_ref(v_discharge_1571_);
return v___x_1578_;
}
}
else
{
lean_dec(v_a_1579_);
lean_dec(v_g_1572_);
lean_dec_ref(v_discharge_1571_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1583_, lean_object* v_discharge_1584_, lean_object* v_g_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1583_, v_discharge_1584_, v_g_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1592_, lean_object* v_discharge_1593_){
_start:
{
lean_object* v_toApplyRulesConfig_1594_; lean_object* v_toBacktrackConfig_1595_; uint8_t v_backtracking_1596_; uint8_t v_intro_1597_; uint8_t v_constructor_1598_; uint8_t v_suggestions_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1631_; 
v_toApplyRulesConfig_1594_ = lean_ctor_get(v_cfg_1592_, 0);
lean_inc_ref(v_toApplyRulesConfig_1594_);
v_toBacktrackConfig_1595_ = lean_ctor_get(v_toApplyRulesConfig_1594_, 0);
lean_inc_ref(v_toBacktrackConfig_1595_);
v_backtracking_1596_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*1);
v_intro_1597_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*1 + 1);
v_constructor_1598_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*1 + 2);
v_suggestions_1599_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*1 + 3);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_cfg_1592_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v_cfg_1592_, 0);
lean_dec(v_unused_1632_);
v___x_1601_ = v_cfg_1592_;
v_isShared_1602_ = v_isSharedCheck_1631_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v_cfg_1592_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1631_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_toApplyConfig_1603_; uint8_t v_transparency_1604_; uint8_t v_symm_1605_; uint8_t v_exfalso_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1629_; 
v_toApplyConfig_1603_ = lean_ctor_get(v_toApplyRulesConfig_1594_, 1);
v_transparency_1604_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1594_, sizeof(void*)*2);
v_symm_1605_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1594_, sizeof(void*)*2 + 1);
v_exfalso_1606_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1594_, sizeof(void*)*2 + 2);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_toApplyRulesConfig_1594_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v_toApplyRulesConfig_1594_, 0);
lean_dec(v_unused_1630_);
v___x_1608_ = v_toApplyRulesConfig_1594_;
v_isShared_1609_ = v_isSharedCheck_1629_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_toApplyConfig_1603_);
lean_dec(v_toApplyRulesConfig_1594_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1629_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_maxDepth_1610_; lean_object* v_proc_1611_; lean_object* v_suspend_1612_; lean_object* v_discharge_1613_; uint8_t v_commitIndependentGoals_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1628_; 
v_maxDepth_1610_ = lean_ctor_get(v_toBacktrackConfig_1595_, 0);
v_proc_1611_ = lean_ctor_get(v_toBacktrackConfig_1595_, 1);
v_suspend_1612_ = lean_ctor_get(v_toBacktrackConfig_1595_, 2);
v_discharge_1613_ = lean_ctor_get(v_toBacktrackConfig_1595_, 3);
v_commitIndependentGoals_1614_ = lean_ctor_get_uint8(v_toBacktrackConfig_1595_, sizeof(void*)*4);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_toBacktrackConfig_1595_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1616_ = v_toBacktrackConfig_1595_;
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_discharge_1613_);
lean_inc(v_suspend_1612_);
lean_inc(v_proc_1611_);
lean_inc(v_maxDepth_1610_);
lean_dec(v_toBacktrackConfig_1595_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___f_1618_; lean_object* v___x_1620_; 
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1618_, 0, v_discharge_1593_);
lean_closure_set(v___f_1618_, 1, v_discharge_1613_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 3, v___f_1618_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_maxDepth_1610_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_proc_1611_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_suspend_1612_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v___f_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*4, v_commitIndependentGoals_1614_);
v___x_1620_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1622_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1620_);
v___x_1622_ = v___x_1608_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_toApplyConfig_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*2, v_transparency_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*2 + 1, v_symm_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*2 + 2, v_exfalso_1606_);
v___x_1622_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1624_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1622_);
v___x_1624_ = v___x_1601_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*1, v_backtracking_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*1 + 1, v_intro_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*1 + 2, v_constructor_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*1 + 3, v_suggestions_1599_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = 1;
v___x_1640_ = l_Lean_Meta_intro1Core(v_g_1633_, v___x_1639_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1659_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1659_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1659_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_snd_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1657_; 
v_snd_1645_ = lean_ctor_get(v_a_1641_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_a_1641_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_a_1641_, 0);
lean_dec(v_unused_1658_);
v___x_1647_ = v_a_1641_;
v_isShared_1648_ = v_isSharedCheck_1657_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snd_1645_);
lean_dec(v_a_1641_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1657_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_box(0);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 1, v___x_1649_);
lean_ctor_set(v___x_1647_, 0, v_snd_1645_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_snd_1645_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1652_);
v___x_1654_ = v___x_1643_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
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
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1640_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1640_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1676_){
_start:
{
lean_object* v___f_1677_; lean_object* v___x_1678_; 
v___f_1677_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1678_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1676_, v___f_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1690_ = l_Lean_MVarId_constructor(v_g_1683_, v___x_1689_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_a_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1690_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1690_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1716_){
_start:
{
lean_object* v___f_1717_; lean_object* v___x_1718_; 
v___f_1717_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1718_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1716_, v___f_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
lean_inc(v_g_1721_);
v___x_1727_ = l_Lean_MVarId_getType(v_g_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = lean_box(0);
v___x_1730_ = l_Lean_Meta_synthInstance(v_a_1728_, v___x_1729_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1721_, v_a_1731_, v___y_1723_);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v___x_1732_, 0);
lean_dec(v_unused_1741_);
v___x_1734_ = v___x_1732_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v___x_1732_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_g_1721_);
v_a_1742_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1730_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1730_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_g_1721_);
v_a_1750_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1727_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1727_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1766_){
_start:
{
lean_object* v___f_1767_; lean_object* v___x_1768_; 
v___f_1767_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1768_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1766_, v___f_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1769_, lean_object* v___y_1770_){
_start:
{
uint8_t v___x_1772_; 
v___x_1772_ = l_Lean_Expr_hasMVar(v_e_1769_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_e_1769_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; lean_object* v_mctx_1775_; lean_object* v___x_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1779_; lean_object* v_cache_1780_; lean_object* v_zetaDeltaFVarIds_1781_; lean_object* v_postponed_1782_; lean_object* v_diag_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1792_; 
v___x_1774_ = lean_st_ref_get(v___y_1770_);
v_mctx_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref(v_mctx_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = l_Lean_instantiateMVarsCore(v_mctx_1775_, v_e_1769_);
v_fst_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_fst_1777_);
v_snd_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc(v_snd_1778_);
lean_dec_ref(v___x_1776_);
v___x_1779_ = lean_st_ref_take(v___y_1770_);
v_cache_1780_ = lean_ctor_get(v___x_1779_, 1);
v_zetaDeltaFVarIds_1781_ = lean_ctor_get(v___x_1779_, 2);
v_postponed_1782_ = lean_ctor_get(v___x_1779_, 3);
v_diag_1783_ = lean_ctor_get(v___x_1779_, 4);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1793_);
v___x_1785_ = v___x_1779_;
v_isShared_1786_ = v_isSharedCheck_1792_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_diag_1783_);
lean_inc(v_postponed_1782_);
lean_inc(v_zetaDeltaFVarIds_1781_);
lean_inc(v_cache_1780_);
lean_dec(v___x_1779_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1792_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v_snd_1778_);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_snd_1778_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_cache_1780_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_zetaDeltaFVarIds_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_postponed_1782_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_diag_1783_);
v___x_1788_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_st_ref_put(v___y_1770_, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_fst_1777_);
return v___x_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1794_, v___y_1795_);
lean_dec(v___y_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1798_, v___y_1800_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1812_, lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1812_, v_x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1819_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1819_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1836_, lean_object* v_x_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1836_, v_x_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1844_, lean_object* v_mvarId_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1845_, v_x_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1853_, lean_object* v_mvarId_1854_, lean_object* v_x_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1853_, v_mvarId_1854_, v_x_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_ref_1868_; lean_object* v___x_1869_; lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
v_ref_1868_ = lean_ctor_get(v___y_1865_, 2);
v___x_1869_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_inc(v_ref_1868_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_ref_1868_);
lean_ctor_set(v___x_1874_, 1, v_a_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 1);
lean_ctor_set(v___x_1872_, 0, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = l_List_reverse___redArg(v_x_1887_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v_head_1895_; lean_object* v_tail_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1916_; 
v_head_1895_ = lean_ctor_get(v_x_1886_, 0);
v_tail_1896_ = lean_ctor_get(v_x_1886_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1898_ = v_x_1886_;
v_isShared_1899_ = v_isSharedCheck_1916_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_tail_1896_);
lean_inc(v_head_1895_);
lean_dec(v_x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1916_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_inc(v_head_1895_);
v___x_1900_ = l_Lean_Expr_mvar___override(v_head_1895_);
v___x_1901_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1895_, v___x_1901_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_x_1887_);
lean_ctor_set(v___x_1898_, 0, v_a_1903_);
v___x_1905_ = v___x_1898_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1903_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_x_1887_);
v___x_1905_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
v_x_1886_ = v_tail_1896_;
v_x_1887_ = v___x_1905_;
goto _start;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_del_object(v___x_1898_);
lean_dec(v_tail_1896_);
lean_dec(v_x_1887_);
v_a_1908_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1902_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1902_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1917_, v_x_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1924_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1927_ = l_Lean_stringToMessageData(v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1928_, lean_object* v_proc_1929_, lean_object* v_orig_1930_, lean_object* v_goals_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_box(0);
lean_inc(v_orig_1930_);
v___x_1938_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1930_, v___x_1937_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
v___x_1940_ = lean_apply_6(v_test_1928_, v_a_1939_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, lean_box(0));
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; uint8_t v___x_1942_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_goals_1931_);
lean_dec(v_orig_1930_);
lean_dec_ref(v_proc_1929_);
v___x_1943_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1944_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1943_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
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
else
{
lean_object* v___x_1953_; 
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
v___x_1953_ = lean_apply_7(v_proc_1929_, v_orig_1930_, v_goals_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, lean_box(0));
return v___x_1953_;
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_goals_1931_);
lean_dec(v_orig_1930_);
lean_dec_ref(v_proc_1929_);
v_a_1954_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1940_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1940_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_goals_1931_);
lean_dec(v_orig_1930_);
lean_dec_ref(v_proc_1929_);
lean_dec_ref(v_test_1928_);
v_a_1962_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1938_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1938_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1970_, lean_object* v_proc_1971_, lean_object* v_orig_1972_, lean_object* v_goals_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1970_, v_proc_1971_, v_orig_1972_, v_goals_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1980_, lean_object* v_test_1981_){
_start:
{
lean_object* v_toApplyRulesConfig_1982_; lean_object* v_toBacktrackConfig_1983_; uint8_t v_backtracking_1984_; uint8_t v_intro_1985_; uint8_t v_constructor_1986_; uint8_t v_suggestions_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2019_; 
v_toApplyRulesConfig_1982_ = lean_ctor_get(v_cfg_1980_, 0);
lean_inc_ref(v_toApplyRulesConfig_1982_);
v_toBacktrackConfig_1983_ = lean_ctor_get(v_toApplyRulesConfig_1982_, 0);
lean_inc_ref(v_toBacktrackConfig_1983_);
v_backtracking_1984_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*1);
v_intro_1985_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*1 + 1);
v_constructor_1986_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*1 + 2);
v_suggestions_1987_ = lean_ctor_get_uint8(v_cfg_1980_, sizeof(void*)*1 + 3);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_cfg_1980_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_cfg_1980_, 0);
lean_dec(v_unused_2020_);
v___x_1989_ = v_cfg_1980_;
v_isShared_1990_ = v_isSharedCheck_2019_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v_cfg_1980_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2019_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_toApplyConfig_1991_; uint8_t v_transparency_1992_; uint8_t v_symm_1993_; uint8_t v_exfalso_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2017_; 
v_toApplyConfig_1991_ = lean_ctor_get(v_toApplyRulesConfig_1982_, 1);
v_transparency_1992_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1982_, sizeof(void*)*2);
v_symm_1993_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1982_, sizeof(void*)*2 + 1);
v_exfalso_1994_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1982_, sizeof(void*)*2 + 2);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_toApplyRulesConfig_1982_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v_toApplyRulesConfig_1982_, 0);
lean_dec(v_unused_2018_);
v___x_1996_ = v_toApplyRulesConfig_1982_;
v_isShared_1997_ = v_isSharedCheck_2017_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_toApplyConfig_1991_);
lean_dec(v_toApplyRulesConfig_1982_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2017_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_maxDepth_1998_; lean_object* v_proc_1999_; lean_object* v_suspend_2000_; lean_object* v_discharge_2001_; uint8_t v_commitIndependentGoals_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2016_; 
v_maxDepth_1998_ = lean_ctor_get(v_toBacktrackConfig_1983_, 0);
v_proc_1999_ = lean_ctor_get(v_toBacktrackConfig_1983_, 1);
v_suspend_2000_ = lean_ctor_get(v_toBacktrackConfig_1983_, 2);
v_discharge_2001_ = lean_ctor_get(v_toBacktrackConfig_1983_, 3);
v_commitIndependentGoals_2002_ = lean_ctor_get_uint8(v_toBacktrackConfig_1983_, sizeof(void*)*4);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_toBacktrackConfig_1983_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2004_ = v_toBacktrackConfig_1983_;
v_isShared_2005_ = v_isSharedCheck_2016_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_discharge_2001_);
lean_inc(v_suspend_2000_);
lean_inc(v_proc_1999_);
lean_inc(v_maxDepth_1998_);
lean_dec(v_toBacktrackConfig_1983_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2016_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___f_2006_; lean_object* v___x_2008_; 
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2006_, 0, v_test_1981_);
lean_closure_set(v___f_2006_, 1, v_proc_1999_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___f_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_maxDepth_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___f_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_suspend_2000_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_discharge_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*4, v_commitIndependentGoals_2002_);
v___x_2008_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2008_);
v___x_2010_ = v___x_1996_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_toApplyConfig_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*2, v_transparency_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*2 + 1, v_symm_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*2 + 2, v_exfalso_1994_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2010_);
v___x_2012_ = v___x_1989_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*1, v_backtracking_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*1 + 1, v_intro_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*1 + 2, v_constructor_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*1 + 3, v_suggestions_1987_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2021_, lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2029_, lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2029_, v_msg_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
uint8_t v___x_2038_; 
v___x_2038_ = 0;
return v___x_2038_;
}
else
{
lean_object* v_head_2039_; lean_object* v_tail_2040_; uint8_t v___x_2041_; 
v_head_2039_ = lean_ctor_get(v_x_2037_, 0);
v_tail_2040_ = lean_ctor_get(v_x_2037_, 1);
v___x_2041_ = l_Lean_Expr_hasMVar(v_head_2039_);
if (v___x_2041_ == 0)
{
v_x_2037_ = v_tail_2040_;
goto _start;
}
else
{
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2043_){
_start:
{
uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_res_2044_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2043_);
lean_dec(v_x_2043_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2046_, lean_object* v_sols_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
uint8_t v___x_2053_; 
v___x_2053_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2047_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
v___x_2054_ = lean_apply_6(v_test_2046_, v_sols_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, lean_box(0));
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v_sols_2047_);
lean_dec_ref(v_test_2046_);
v___x_2055_ = lean_box(v___x_2053_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2057_, lean_object* v_sols_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2057_, v_sols_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2065_, lean_object* v_test_2066_){
_start:
{
lean_object* v___f_2067_; lean_object* v___x_2068_; 
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2067_, 0, v_test_2066_);
v___x_2068_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2065_, v___f_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
uint8_t v___x_2071_; 
lean_dec_ref(v_e_2069_);
v___x_2071_ = 0;
return v___x_2071_;
}
else
{
lean_object* v_head_2072_; lean_object* v_tail_2073_; uint8_t v___x_2074_; 
v_head_2072_ = lean_ctor_get(v_x_2070_, 0);
v_tail_2073_ = lean_ctor_get(v_x_2070_, 1);
lean_inc_ref(v_e_2069_);
v___x_2074_ = l_Lean_Expr_occurs(v_e_2069_, v_head_2072_);
if (v___x_2074_ == 0)
{
v_x_2070_ = v_tail_2073_;
goto _start;
}
else
{
lean_dec_ref(v_e_2069_);
return v___x_2074_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2076_, lean_object* v_x_2077_){
_start:
{
uint8_t v_res_2078_; lean_object* v_r_2079_; 
v_res_2078_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2076_, v_x_2077_);
lean_dec(v_x_2077_);
v_r_2079_ = lean_box(v_res_2078_);
return v_r_2079_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2080_, lean_object* v_x_2081_){
_start:
{
if (lean_obj_tag(v_x_2081_) == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = 1;
return v___x_2082_;
}
else
{
lean_object* v_head_2083_; lean_object* v_tail_2084_; uint8_t v___x_2085_; 
v_head_2083_ = lean_ctor_get(v_x_2081_, 0);
lean_inc(v_head_2083_);
v_tail_2084_ = lean_ctor_get(v_x_2081_, 1);
lean_inc(v_tail_2084_);
lean_dec_ref_known(v_x_2081_, 2);
v___x_2085_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2083_, v_sols_2080_);
if (v___x_2085_ == 0)
{
lean_dec(v_tail_2084_);
return v___x_2085_;
}
else
{
v_x_2081_ = v_tail_2084_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2087_, lean_object* v_x_2088_){
_start:
{
uint8_t v_res_2089_; lean_object* v_r_2090_; 
v_res_2089_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2087_, v_x_2088_);
lean_dec(v_sols_2087_);
v_r_2090_ = lean_box(v_res_2089_);
return v_r_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2091_, lean_object* v_sols_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2092_, v_use_2091_);
v___x_2099_ = lean_box(v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2101_, lean_object* v_sols_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2101_, v_sols_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v_sols_2102_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2109_, lean_object* v_use_2110_){
_start:
{
lean_object* v___f_2111_; lean_object* v___x_2112_; 
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2111_, 0, v_use_2110_);
v___x_2112_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2109_, v___f_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2113_){
_start:
{
lean_object* v___y_2115_; lean_object* v_toApplyRulesConfig_2116_; uint8_t v_backtracking_2117_; uint8_t v_intro_2118_; uint8_t v_constructor_2119_; uint8_t v_suggestions_2120_; uint8_t v_intro_2124_; 
v_intro_2124_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1 + 1);
if (v_intro_2124_ == 0)
{
lean_object* v_toApplyRulesConfig_2125_; uint8_t v_backtracking_2126_; uint8_t v_constructor_2127_; uint8_t v_suggestions_2128_; 
v_toApplyRulesConfig_2125_ = lean_ctor_get(v_cfg_2113_, 0);
lean_inc_ref(v_toApplyRulesConfig_2125_);
v_backtracking_2126_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1);
v_constructor_2127_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1 + 2);
v_suggestions_2128_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1 + 3);
v___y_2115_ = v_cfg_2113_;
v_toApplyRulesConfig_2116_ = v_toApplyRulesConfig_2125_;
v_backtracking_2117_ = v_backtracking_2126_;
v_intro_2118_ = v_intro_2124_;
v_constructor_2119_ = v_constructor_2127_;
v_suggestions_2120_ = v_suggestions_2128_;
goto v___jp_2114_;
}
else
{
lean_object* v_toApplyRulesConfig_2129_; uint8_t v_backtracking_2130_; uint8_t v_constructor_2131_; uint8_t v_suggestions_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2146_; 
v_toApplyRulesConfig_2129_ = lean_ctor_get(v_cfg_2113_, 0);
v_backtracking_2130_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1);
v_constructor_2131_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1 + 2);
v_suggestions_2132_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*1 + 3);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_cfg_2113_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2134_ = v_cfg_2113_;
v_isShared_2135_ = v_isSharedCheck_2146_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_toApplyRulesConfig_2129_);
lean_dec(v_cfg_2113_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2146_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
uint8_t v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = 0;
if (v_isShared_2135_ == 0)
{
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_toApplyRulesConfig_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*1, v_backtracking_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*1 + 2, v_constructor_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*1 + 3, v_suggestions_2132_);
v___x_2138_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v_toApplyRulesConfig_2140_; uint8_t v_backtracking_2141_; uint8_t v_intro_2142_; uint8_t v_constructor_2143_; uint8_t v_suggestions_2144_; 
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*1 + 1, v___x_2136_);
v___x_2139_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2138_);
v_toApplyRulesConfig_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc_ref(v_toApplyRulesConfig_2140_);
v_backtracking_2141_ = lean_ctor_get_uint8(v___x_2139_, sizeof(void*)*1);
v_intro_2142_ = lean_ctor_get_uint8(v___x_2139_, sizeof(void*)*1 + 1);
v_constructor_2143_ = lean_ctor_get_uint8(v___x_2139_, sizeof(void*)*1 + 2);
v_suggestions_2144_ = lean_ctor_get_uint8(v___x_2139_, sizeof(void*)*1 + 3);
v___y_2115_ = v___x_2139_;
v_toApplyRulesConfig_2116_ = v_toApplyRulesConfig_2140_;
v_backtracking_2117_ = v_backtracking_2141_;
v_intro_2118_ = v_intro_2142_;
v_constructor_2119_ = v_constructor_2143_;
v_suggestions_2120_ = v_suggestions_2144_;
goto v___jp_2114_;
}
}
}
v___jp_2114_:
{
if (v_constructor_2119_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2116_);
return v___y_2115_;
}
else
{
uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v___y_2115_);
v___x_2121_ = 0;
v___x_2122_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2122_, 0, v_toApplyRulesConfig_2116_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1, v_backtracking_2117_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1 + 1, v_intro_2118_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1 + 2, v___x_2121_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1 + 3, v_suggestions_2120_);
v___x_2123_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2122_);
return v___x_2123_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = l_List_reverse___redArg(v_x_2148_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
else
{
lean_object* v_head_2158_; lean_object* v_tail_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2177_; 
v_head_2158_ = lean_ctor_get(v_x_2147_, 0);
v_tail_2159_ = lean_ctor_get(v_x_2147_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2161_ = v_x_2147_;
v_isShared_2162_ = v_isSharedCheck_2177_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_tail_2159_);
lean_inc(v_head_2158_);
lean_dec(v_x_2147_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2177_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; 
lean_inc(v___y_2154_);
lean_inc_ref(v___y_2153_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2151_);
lean_inc(v___y_2150_);
lean_inc_ref(v___y_2149_);
v___x_2163_ = lean_apply_7(v_head_2158_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, lean_box(0));
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_x_2148_);
lean_ctor_set(v___x_2161_, 0, v_a_2164_);
v___x_2166_ = v___x_2161_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2164_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_x_2148_);
v___x_2166_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
v_x_2147_ = v_tail_2159_;
v_x_2148_ = v___x_2166_;
goto _start;
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_del_object(v___x_2161_);
lean_dec(v_tail_2159_);
lean_dec(v_x_2148_);
v_a_2169_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2163_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2163_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2178_, v_x_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2188_, lean_object* v_cfg_2189_, lean_object* v_lemmas_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
v___x_2198_ = lean_apply_8(v_ctx_2188_, v_cfg_2189_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, lean_box(0));
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = lean_box(0);
v___x_2201_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2190_, v___x_2200_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2210_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2210_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2210_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = l_List_appendTR___redArg(v_a_2199_, v_a_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2206_);
v___x_2208_ = v___x_2204_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_dec(v_a_2199_);
return v___x_2201_;
}
}
else
{
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v_lemmas_2190_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2211_, lean_object* v_cfg_2212_, lean_object* v_lemmas_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2211_, v_cfg_2212_, v_lemmas_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2222_){
_start:
{
uint8_t v___x_2223_; 
v___x_2223_ = 0;
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2224_){
_start:
{
uint8_t v_res_2225_; lean_object* v_r_2226_; 
v_res_2225_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2224_);
lean_dec(v_x_2224_);
v_r_2226_ = lean_box(v_res_2225_);
return v_r_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2227_, lean_object* v___x_2228_, lean_object* v___x_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2227_, v___x_2228_, v___x_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_fst_2240_; lean_object* v___x_2242_; 
v_fst_2240_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_fst_2240_);
lean_dec(v_a_2236_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_fst_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_fst_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_a_2245_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2235_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2235_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2253_, v___x_2254_, v___x_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2276_, lean_object* v_g_2277_, lean_object* v_lemmas_2278_, lean_object* v_ctx_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___f_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; 
v___f_2285_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2285_, 0, v_ctx_2279_);
lean_closure_set(v___f_2285_, 1, v_cfg_2276_);
lean_closure_set(v___f_2285_, 2, v_lemmas_2278_);
v___x_2286_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2287_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2288_, 0, v___f_2285_);
lean_closure_set(v___f_2288_, 1, v___x_2286_);
lean_closure_set(v___f_2288_, 2, v___x_2287_);
v___x_2289_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2277_, v___f_2288_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2290_, lean_object* v_g_2291_, lean_object* v_lemmas_2292_, lean_object* v_ctx_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2290_, v_g_2291_, v_lemmas_2292_, v_ctx_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2300_, lean_object* v_lemmas_2301_, lean_object* v_ctx_2302_, lean_object* v_g_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2309_; 
lean_inc(v_g_2303_);
lean_inc_ref(v_cfg_2300_);
v___x_2309_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2300_, v_g_2303_, v_lemmas_2301_, v_ctx_2302_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_toApplyRulesConfig_2310_; lean_object* v_a_2311_; lean_object* v_toApplyConfig_2312_; uint8_t v_transparency_2313_; lean_object* v___x_2314_; 
v_toApplyRulesConfig_2310_ = lean_ctor_get(v_cfg_2300_, 0);
lean_inc_ref(v_toApplyRulesConfig_2310_);
lean_dec_ref(v_cfg_2300_);
v_a_2311_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2309_, 1);
v_toApplyConfig_2312_ = lean_ctor_get(v_toApplyRulesConfig_2310_, 1);
lean_inc_ref(v_toApplyConfig_2312_);
v_transparency_2313_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2310_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2310_);
v___x_2314_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2312_, v_transparency_2313_, v_a_2311_, v_g_2303_, v_a_2305_, v_a_2307_);
return v___x_2314_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_g_2303_);
lean_dec_ref(v_cfg_2300_);
v_a_2315_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2309_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2309_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2323_, lean_object* v_lemmas_2324_, lean_object* v_ctx_2325_, lean_object* v_g_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2323_, v_lemmas_2324_, v_ctx_2325_, v_g_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2333_, lean_object* v_lemmas_2334_, lean_object* v_ctx_2335_, lean_object* v_g_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; 
lean_inc(v_g_2336_);
lean_inc_ref(v_cfg_2333_);
v___x_2342_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2333_, v_g_2336_, v_lemmas_2334_, v_ctx_2335_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_toApplyRulesConfig_2343_; lean_object* v_a_2344_; lean_object* v_toApplyConfig_2345_; uint8_t v_transparency_2346_; lean_object* v___x_2347_; 
v_toApplyRulesConfig_2343_ = lean_ctor_get(v_cfg_2333_, 0);
lean_inc_ref(v_toApplyRulesConfig_2343_);
lean_dec_ref(v_cfg_2333_);
v_a_2344_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2342_, 1);
v_toApplyConfig_2345_ = lean_ctor_get(v_toApplyRulesConfig_2343_, 1);
lean_inc_ref(v_toApplyConfig_2345_);
v_transparency_2346_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2343_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2343_);
v___x_2347_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2345_, v_transparency_2346_, v_a_2344_, v_g_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2347_;
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_g_2336_);
lean_dec_ref(v_cfg_2333_);
v_a_2348_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2342_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2342_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2356_, lean_object* v_lemmas_2357_, lean_object* v_ctx_2358_, lean_object* v_g_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2356_, v_lemmas_2357_, v_ctx_2358_, v_g_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2366_, lean_object* v_i_2367_, lean_object* v_k_2368_){
_start:
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = lean_array_get_size(v_keys_2366_);
v___x_2370_ = lean_nat_dec_lt(v_i_2367_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_dec(v_i_2367_);
return v___x_2370_;
}
else
{
lean_object* v_k_x27_2371_; uint8_t v___x_2372_; 
v_k_x27_2371_ = lean_array_fget_borrowed(v_keys_2366_, v_i_2367_);
v___x_2372_ = l_Lean_instBEqMVarId_beq(v_k_2368_, v_k_x27_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_i_2367_, v___x_2373_);
lean_dec(v_i_2367_);
v_i_2367_ = v___x_2374_;
goto _start;
}
else
{
lean_dec(v_i_2367_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2376_, lean_object* v_i_2377_, lean_object* v_k_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2376_, v_i_2377_, v_k_2378_);
lean_dec(v_k_2378_);
lean_dec_ref(v_keys_2376_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2381_, size_t v_x_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
lean_object* v_es_2384_; lean_object* v___x_2385_; size_t v___x_2386_; size_t v___x_2387_; lean_object* v_j_2388_; lean_object* v___x_2389_; 
v_es_2384_ = lean_ctor_get(v_x_2381_, 0);
v___x_2385_ = lean_box(2);
v___x_2386_ = ((size_t)31ULL);
v___x_2387_ = lean_usize_land(v_x_2382_, v___x_2386_);
v_j_2388_ = lean_usize_to_nat(v___x_2387_);
v___x_2389_ = lean_array_get_borrowed(v___x_2385_, v_es_2384_, v_j_2388_);
lean_dec(v_j_2388_);
switch(lean_obj_tag(v___x_2389_))
{
case 0:
{
lean_object* v_key_2390_; uint8_t v___x_2391_; 
v_key_2390_ = lean_ctor_get(v___x_2389_, 0);
v___x_2391_ = l_Lean_instBEqMVarId_beq(v_x_2383_, v_key_2390_);
return v___x_2391_;
}
case 1:
{
lean_object* v_node_2392_; size_t v___x_2393_; size_t v___x_2394_; 
v_node_2392_ = lean_ctor_get(v___x_2389_, 0);
v___x_2393_ = ((size_t)5ULL);
v___x_2394_ = lean_usize_shift_right(v_x_2382_, v___x_2393_);
v_x_2381_ = v_node_2392_;
v_x_2382_ = v___x_2394_;
goto _start;
}
default: 
{
uint8_t v___x_2396_; 
v___x_2396_ = 0;
return v___x_2396_;
}
}
}
else
{
lean_object* v_ks_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_ks_2397_ = lean_ctor_get(v_x_2381_, 0);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2397_, v___x_2398_, v_x_2383_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
size_t v_x_1980__boxed_2403_; uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_x_1980__boxed_2403_ = lean_unbox_usize(v_x_2401_);
lean_dec(v_x_2401_);
v_res_2404_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2400_, v_x_1980__boxed_2403_, v_x_2402_);
lean_dec(v_x_2402_);
lean_dec_ref(v_x_2400_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
uint64_t v___x_2408_; size_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2408_ = l_Lean_instHashableMVarId_hash(v_x_2407_);
v___x_2409_ = lean_uint64_to_usize(v___x_2408_);
v___x_2410_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2406_, v___x_2409_, v_x_2407_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2411_, v_x_2412_);
lean_dec(v_x_2412_);
lean_dec_ref(v_x_2411_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; lean_object* v_mctx_2419_; lean_object* v_eAssignment_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2418_ = lean_st_ref_get(v___y_2416_);
v_mctx_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc_ref(v_mctx_2419_);
lean_dec(v___x_2418_);
v_eAssignment_2420_ = lean_ctor_get(v_mctx_2419_, 8);
lean_inc_ref(v_eAssignment_2420_);
lean_dec_ref(v_mctx_2419_);
v___x_2421_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2420_, v_mvarId_2415_);
lean_dec_ref(v_eAssignment_2420_);
v___x_2422_ = lean_box(v___x_2421_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec(v_mvarId_2424_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 0)
{
return v_x_2428_;
}
else
{
lean_object* v_head_2430_; lean_object* v_tail_2431_; lean_object* v___x_2432_; 
v_head_2430_ = lean_ctor_get(v_x_2429_, 0);
lean_inc(v_head_2430_);
v_tail_2431_ = lean_ctor_get(v_x_2429_, 1);
lean_inc(v_tail_2431_);
lean_dec_ref_known(v_x_2429_, 2);
v___x_2432_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2428_, v_head_2430_);
v_x_2428_ = v___x_2432_;
v_x_2429_ = v_tail_2431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2434_, lean_object* v_a_2435_, uint8_t v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
if (lean_obj_tag(v_a_2437_) == 0)
{
if (lean_obj_tag(v_a_2438_) == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v_a_2435_);
lean_dec_ref(v_f_2434_);
v___x_2445_ = lean_box(v_a_2436_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v_a_2439_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
else
{
lean_object* v_head_2448_; lean_object* v_tail_2449_; 
v_head_2448_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_head_2448_);
v_tail_2449_ = lean_ctor_get(v_a_2438_, 1);
lean_inc(v_tail_2449_);
lean_dec_ref_known(v_a_2438_, 2);
v_a_2437_ = v_head_2448_;
v_a_2438_ = v_tail_2449_;
goto _start;
}
}
else
{
lean_object* v_head_2451_; lean_object* v_tail_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2495_; 
v_head_2451_ = lean_ctor_get(v_a_2437_, 0);
v_tail_2452_ = lean_ctor_get(v_a_2437_, 1);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_a_2437_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2454_ = v_a_2437_;
v_isShared_2455_ = v_isSharedCheck_2495_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_tail_2452_);
lean_inc(v_head_2451_);
lean_dec(v_a_2437_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2495_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2494_; 
v___x_2456_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2451_, v___y_2441_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2494_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2494_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_unbox(v_a_2457_);
lean_dec(v_a_2457_);
if (v___x_2461_ == 0)
{
lean_object* v_zero_2462_; uint8_t v_isZero_2463_; 
v_zero_2462_ = lean_unsigned_to_nat(0u);
v_isZero_2463_ = lean_nat_dec_eq(v_a_2435_, v_zero_2462_);
if (v_isZero_2463_ == 1)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_del_object(v___x_2454_);
lean_dec(v_a_2435_);
lean_dec_ref(v_f_2434_);
v___x_2464_ = lean_array_push(v_a_2439_, v_head_2451_);
v___x_2465_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2464_, v_tail_2452_);
v___x_2466_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2465_, v_a_2438_);
v___x_2467_ = lean_box(v_a_2436_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v___x_2466_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2468_);
v___x_2470_ = v___x_2459_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_object* v_one_2472_; lean_object* v_n_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_del_object(v___x_2459_);
v_one_2472_ = lean_unsigned_to_nat(1u);
v_n_2473_ = lean_nat_sub(v_a_2435_, v_one_2472_);
lean_dec(v_a_2435_);
v___x_2474_ = 1;
lean_inc_ref(v_f_2434_);
lean_inc(v_head_2451_);
v___x_2475_ = lean_apply_1(v_f_2434_, v_head_2451_);
v___x_2476_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2475_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
if (lean_obj_tag(v_a_2477_) == 0)
{
lean_object* v___x_2478_; 
lean_del_object(v___x_2454_);
v___x_2478_ = lean_array_push(v_a_2439_, v_head_2451_);
v_a_2435_ = v_n_2473_;
v_a_2437_ = v_tail_2452_;
v_a_2439_ = v___x_2478_;
goto _start;
}
else
{
lean_object* v_val_2480_; lean_object* v___x_2482_; 
lean_dec(v_head_2451_);
v_val_2480_ = lean_ctor_get(v_a_2477_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v_a_2477_, 1);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v_a_2438_);
lean_ctor_set(v___x_2454_, 0, v_tail_2452_);
v___x_2482_ = v___x_2454_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_tail_2452_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_a_2438_);
v___x_2482_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
v_a_2435_ = v_n_2473_;
v_a_2436_ = v___x_2474_;
v_a_2437_ = v_val_2480_;
v_a_2438_ = v___x_2482_;
goto _start;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_n_2473_);
lean_del_object(v___x_2454_);
lean_dec(v_tail_2452_);
lean_dec(v_head_2451_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_f_2434_);
v_a_2485_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2476_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2476_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
else
{
lean_del_object(v___x_2459_);
lean_del_object(v___x_2454_);
lean_dec(v_head_2451_);
v_a_2437_ = v_tail_2452_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
uint8_t v_a_2059__boxed_2507_; lean_object* v_res_2508_; 
v_a_2059__boxed_2507_ = lean_unbox(v_a_2498_);
v_res_2508_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2496_, v_a_2497_, v_a_2059__boxed_2507_, v_a_2499_, v_a_2500_, v_a_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2509_, size_t v_i_2510_, size_t v_stop_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_a_2519_; uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_eq(v_i_2510_, v_stop_2511_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_array_uget_borrowed(v_as_2509_, v_i_2510_);
v___x_2525_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2524_, v___y_2514_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_inc(v___x_2524_);
v___x_2528_ = lean_array_push(v_b_2512_, v___x_2524_);
v_a_2519_ = v___x_2528_;
goto v___jp_2518_;
}
else
{
v_a_2519_ = v_b_2512_;
goto v___jp_2518_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec_ref(v_b_2512_);
v_a_2529_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2525_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2525_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_b_2512_);
return v___x_2537_;
}
v___jp_2518_:
{
size_t v___x_2520_; size_t v___x_2521_; 
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_add(v_i_2510_, v___x_2520_);
v_i_2510_ = v___x_2521_;
v_b_2512_ = v_a_2519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2538_, lean_object* v_i_2539_, lean_object* v_stop_2540_, lean_object* v_b_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
size_t v_i_boxed_2547_; size_t v_stop_boxed_2548_; lean_object* v_res_2549_; 
v_i_boxed_2547_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_stop_boxed_2548_ = lean_unbox_usize(v_stop_2540_);
lean_dec(v_stop_2540_);
v_res_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2538_, v_i_boxed_2547_, v_stop_boxed_2548_, v_b_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v_as_2538_);
return v_res_2549_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2553_ = lean_array_to_list(v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2554_, lean_object* v_goals_2555_, lean_object* v_maxIters_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2562_ = 0;
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2566_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2554_, v_maxIters_2556_, v___x_2562_, v_goals_2555_, v___x_2563_, v___x_2565_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2609_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2609_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2609_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2608_; 
v_fst_2571_ = lean_ctor_get(v_a_2567_, 0);
v_snd_2572_ = lean_ctor_get(v_a_2567_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_a_2567_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2574_ = v_a_2567_;
v_isShared_2575_ = v_isSharedCheck_2608_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snd_2572_);
lean_inc(v_fst_2571_);
lean_dec(v_a_2567_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2608_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = lean_array_get_size(v_snd_2572_);
v___x_2577_ = lean_nat_dec_lt(v___x_2564_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
lean_dec(v_snd_2572_);
v___x_2578_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v___x_2578_);
v___x_2580_ = v___x_2574_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_fst_2571_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2580_);
v___x_2582_ = v___x_2569_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; 
lean_del_object(v___x_2569_);
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = lean_usize_of_nat(v___x_2576_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2572_, v___x_2585_, v___x_2586_, v___x_2565_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v_snd_2572_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2599_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_array_to_list(v_a_2588_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v___x_2592_);
v___x_2594_ = v___x_2574_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_fst_2571_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2594_);
v___x_2596_ = v___x_2590_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_del_object(v___x_2574_);
lean_dec(v_fst_2571_);
v_a_2600_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2587_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2587_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2566_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2566_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2618_, lean_object* v_goals_2619_, lean_object* v_maxIters_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2618_, v_goals_2619_, v_maxIters_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
return v_res_2626_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2629_ = l_Lean_stringToMessageData(v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2630_, lean_object* v_goals_2631_, lean_object* v_maxIters_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2630_, v_goals_2631_, v_maxIters_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2651_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_fst_2643_; uint8_t v___x_2644_; 
v_fst_2643_ = lean_ctor_get(v_a_2639_, 0);
v___x_2644_ = lean_unbox(v_fst_2643_);
if (v___x_2644_ == 1)
{
lean_object* v_snd_2645_; lean_object* v___x_2647_; 
v_snd_2645_ = lean_ctor_get(v_a_2639_, 1);
lean_inc(v_snd_2645_);
lean_dec(v_a_2639_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v_snd_2645_);
v___x_2647_ = v___x_2641_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_snd_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_del_object(v___x_2641_);
lean_dec(v_a_2639_);
v___x_2649_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2650_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2649_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2650_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2638_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2638_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2660_, lean_object* v_goals_2661_, lean_object* v_maxIters_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2660_, v_goals_2661_, v_maxIters_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2669_, lean_object* v_ctx_2670_, lean_object* v_cfg_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
uint8_t v_backtracking_2678_; 
v_backtracking_2678_ = lean_ctor_get_uint8(v_cfg_2671_, sizeof(void*)*1);
if (v_backtracking_2678_ == 0)
{
lean_object* v_toApplyRulesConfig_2679_; lean_object* v_toBacktrackConfig_2680_; lean_object* v_maxDepth_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_toApplyRulesConfig_2679_ = lean_ctor_get(v_cfg_2671_, 0);
v_toBacktrackConfig_2680_ = lean_ctor_get(v_toApplyRulesConfig_2679_, 0);
v_maxDepth_2681_ = lean_ctor_get(v_toBacktrackConfig_2680_, 0);
lean_inc(v_maxDepth_2681_);
v___x_2682_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2682_, 0, v_cfg_2671_);
lean_closure_set(v___x_2682_, 1, v_lemmas_2669_);
lean_closure_set(v___x_2682_, 2, v_ctx_2670_);
v___x_2683_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2682_, v_a_2672_, v_maxDepth_2681_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
return v___x_2683_;
}
else
{
lean_object* v_toApplyRulesConfig_2684_; lean_object* v_toBacktrackConfig_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_toApplyRulesConfig_2684_ = lean_ctor_get(v_cfg_2671_, 0);
v_toBacktrackConfig_2685_ = lean_ctor_get(v_toApplyRulesConfig_2684_, 0);
lean_inc_ref(v_toBacktrackConfig_2685_);
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2687_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2687_, 0, v_cfg_2671_);
lean_closure_set(v___x_2687_, 1, v_lemmas_2669_);
lean_closure_set(v___x_2687_, 2, v_ctx_2670_);
v___x_2688_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2685_, v___x_2686_, v___x_2687_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2689_, lean_object* v_ctx_2690_, lean_object* v_cfg_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2689_, v_ctx_2690_, v_cfg_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2699_, v___y_2701_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_mvarId_2706_);
return v_res_2712_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2714_, v_x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2717_, v_x_2718_, v_x_2719_);
lean_dec(v_x_2719_);
lean_dec_ref(v_x_2718_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2722_, lean_object* v_x_2723_, size_t v_x_2724_, lean_object* v_x_2725_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2723_, v_x_2724_, v_x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
size_t v_x_2499__boxed_2731_; uint8_t v_res_2732_; lean_object* v_r_2733_; 
v_x_2499__boxed_2731_ = lean_unbox_usize(v_x_2729_);
lean_dec(v_x_2729_);
v_res_2732_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2727_, v_x_2728_, v_x_2499__boxed_2731_, v_x_2730_);
lean_dec(v_x_2730_);
lean_dec_ref(v_x_2728_);
v_r_2733_ = lean_box(v_res_2732_);
return v_r_2733_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2734_, lean_object* v_keys_2735_, lean_object* v_vals_2736_, lean_object* v_heq_2737_, lean_object* v_i_2738_, lean_object* v_k_2739_){
_start:
{
uint8_t v___x_2740_; 
v___x_2740_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2735_, v_i_2738_, v_k_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2741_, lean_object* v_keys_2742_, lean_object* v_vals_2743_, lean_object* v_heq_2744_, lean_object* v_i_2745_, lean_object* v_k_2746_){
_start:
{
uint8_t v_res_2747_; lean_object* v_r_2748_; 
v_res_2747_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2741_, v_keys_2742_, v_vals_2743_, v_heq_2744_, v_i_2745_, v_k_2746_);
lean_dec(v_k_2746_);
lean_dec_ref(v_vals_2743_);
lean_dec_ref(v_keys_2742_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v_x_2760_);
return v_res_2766_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2769_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2770_ = l_Lean_Name_append(v___x_2769_, v___x_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2771_, lean_object* v_lemmas_2772_, lean_object* v_ctx_2773_, lean_object* v_goals_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___f_2780_; lean_object* v_cfg_2781_; lean_object* v___x_2782_; 
v___f_2780_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v_cfg_2781_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2771_);
lean_inc(v_goals_2774_);
lean_inc_ref(v_cfg_2781_);
lean_inc_ref(v_ctx_2773_);
lean_inc(v_lemmas_2772_);
v___x_2782_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2772_, v_ctx_2773_, v_cfg_2781_, v_goals_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_dec_ref(v_cfg_2781_);
lean_dec(v_goals_2774_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
return v___x_2782_;
}
else
{
lean_object* v_a_2783_; uint8_t v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v___x_2784_ = l_Lean_Exception_isInterrupt(v_a_2783_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
lean_inc(v_a_2783_);
v___x_2785_ = l_Lean_Exception_isRuntime(v_a_2783_);
if (v___x_2785_ == 0)
{
if (lean_obj_tag(v_goals_2774_) == 1)
{
lean_object* v_tail_2786_; 
v_tail_2786_ = lean_ctor_get(v_goals_2774_, 1);
lean_inc(v_tail_2786_);
if (lean_obj_tag(v_tail_2786_) == 0)
{
lean_object* v_toApplyRulesConfig_2787_; uint8_t v_exfalso_2788_; 
v_toApplyRulesConfig_2787_ = lean_ctor_get(v_cfg_2781_, 0);
v_exfalso_2788_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2787_, sizeof(void*)*2 + 2);
if (v_exfalso_2788_ == 1)
{
lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2918_; 
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2782_, 0);
lean_dec(v_unused_2919_);
v___x_2790_ = v___x_2782_;
v_isShared_2791_ = v_isSharedCheck_2918_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v___x_2782_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2918_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_toCold_2792_; lean_object* v_options_2793_; uint8_t v_hasTrace_2794_; 
v_toCold_2792_ = lean_ctor_get(v_a_2777_, 0);
v_options_2793_ = lean_ctor_get(v_toCold_2792_, 2);
v_hasTrace_2794_ = lean_ctor_get_uint8(v_options_2793_, sizeof(void*)*1);
if (v_hasTrace_2794_ == 0)
{
lean_object* v_head_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2813_; 
lean_del_object(v___x_2790_);
v_head_2795_ = lean_ctor_get(v_goals_2774_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_goals_2774_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; 
v_unused_2814_ = lean_ctor_get(v_goals_2774_, 1);
lean_dec(v_unused_2814_);
v___x_2797_ = v_goals_2774_;
v_isShared_2798_ = v_isSharedCheck_2813_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_head_2795_);
lean_dec(v_goals_2774_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2813_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_MVarId_exfalso(v_head_2795_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_a_2800_);
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2800_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_tail_2786_);
v___x_2802_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2772_, v_ctx_2773_, v_cfg_2781_, v___x_2802_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
return v___x_2803_;
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_del_object(v___x_2797_);
lean_dec_ref(v_cfg_2781_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
v_a_2805_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2799_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2799_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
else
{
lean_object* v_head_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2916_; 
v_head_2815_ = lean_ctor_get(v_goals_2774_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_goals_2774_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v_goals_2774_, 1);
lean_dec(v_unused_2917_);
v___x_2817_ = v_goals_2774_;
v_isShared_2818_ = v_isSharedCheck_2916_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_head_2815_);
lean_dec(v_goals_2774_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2916_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_inheritedTraceOptions_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v_a_2827_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v_a_2842_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v_a_2849_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v_a_2861_; 
v_inheritedTraceOptions_2819_ = lean_ctor_get(v_toCold_2792_, 11);
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2821_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2822_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2819_, v_options_2793_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = l_Lean_trace_profiler;
v___x_2903_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2793_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
lean_del_object(v___x_2817_);
lean_del_object(v___x_2790_);
v___x_2904_ = l_Lean_MVarId_exfalso(v_head_2815_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v_a_2905_);
lean_ctor_set(v___x_2906_, 1, v_tail_2786_);
v___x_2907_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2772_, v_ctx_2773_, v_cfg_2781_, v___x_2906_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
return v___x_2907_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_cfg_2781_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
v_a_2908_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2904_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2904_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
goto v___jp_2863_;
}
}
else
{
goto v___jp_2863_;
}
v___jp_2824_:
{
lean_object* v___x_2828_; double v___x_2829_; double v___x_2830_; double v___x_2831_; double v___x_2832_; double v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2828_ = lean_io_mono_nanos_now();
v___x_2829_ = lean_float_of_nat(v___y_2826_);
v___x_2830_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2831_ = lean_float_div(v___x_2829_, v___x_2830_);
v___x_2832_ = lean_float_of_nat(v___x_2828_);
v___x_2833_ = lean_float_div(v___x_2832_, v___x_2830_);
v___x_2834_ = lean_box_float(v___x_2831_);
v___x_2835_ = lean_box_float(v___x_2833_);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v_a_2827_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_2820_, v_exfalso_2788_, v___x_2821_, v_options_2793_, v___x_2823_, v___y_2825_, v___f_2780_, v___x_2837_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
return v___x_2838_;
}
v___jp_2839_:
{
lean_object* v___x_2844_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 0);
lean_ctor_set(v___x_2790_, 0, v_a_2842_);
v___x_2844_ = v___x_2790_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
v___y_2825_ = v___y_2840_;
v___y_2826_ = v___y_2841_;
v_a_2827_ = v___x_2844_;
goto v___jp_2824_;
}
}
v___jp_2846_:
{
lean_object* v___x_2850_; double v___x_2851_; double v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2850_ = lean_io_get_num_heartbeats();
v___x_2851_ = lean_float_of_nat(v___y_2848_);
v___x_2852_ = lean_float_of_nat(v___x_2850_);
v___x_2853_ = lean_box_float(v___x_2851_);
v___x_2854_ = lean_box_float(v___x_2852_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_a_2849_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_2820_, v_exfalso_2788_, v___x_2821_, v_options_2793_, v___x_2823_, v___y_2847_, v___f_2780_, v___x_2856_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
return v___x_2857_;
}
v___jp_2858_:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v_a_2861_);
v___y_2847_ = v___y_2859_;
v___y_2848_ = v___y_2860_;
v_a_2849_ = v___x_2862_;
goto v___jp_2846_;
}
v___jp_2863_:
{
lean_object* v___x_2864_; lean_object* v_a_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2864_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2778_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2867_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2793_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_io_mono_nanos_now();
v___x_2869_ = l_Lean_MVarId_exfalso(v_head_2815_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_a_2870_);
v___x_2872_ = v___x_2817_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2870_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_tail_2786_);
v___x_2872_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; 
v___x_2873_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2772_, v_ctx_2773_, v_cfg_2781_, v___x_2872_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_del_object(v___x_2790_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set_tag(v___x_2876_, 1);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
v___y_2825_ = v_a_2865_;
v___y_2826_ = v___x_2868_;
v_a_2827_ = v___x_2879_;
goto v___jp_2824_;
}
}
}
else
{
lean_object* v_a_2882_; 
v_a_2882_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2873_, 1);
v___y_2840_ = v_a_2865_;
v___y_2841_ = v___x_2868_;
v_a_2842_ = v_a_2882_;
goto v___jp_2839_;
}
}
}
else
{
lean_object* v_a_2884_; 
lean_del_object(v___x_2817_);
lean_dec_ref(v_cfg_2781_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
v_a_2884_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2869_, 1);
v___y_2840_ = v_a_2865_;
v___y_2841_ = v___x_2868_;
v_a_2842_ = v_a_2884_;
goto v___jp_2839_;
}
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_del_object(v___x_2790_);
v___x_2885_ = lean_io_get_num_heartbeats();
v___x_2886_ = l_Lean_MVarId_exfalso(v_head_2815_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2889_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_a_2887_);
v___x_2889_ = v___x_2817_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2887_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_tail_2786_);
v___x_2889_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2772_, v_ctx_2773_, v_cfg_2781_, v___x_2889_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 1);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
v___y_2847_ = v_a_2865_;
v___y_2848_ = v___x_2885_;
v_a_2849_ = v___x_2896_;
goto v___jp_2846_;
}
}
}
else
{
lean_object* v_a_2899_; 
v_a_2899_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2890_, 1);
v___y_2859_ = v_a_2865_;
v___y_2860_ = v___x_2885_;
v_a_2861_ = v_a_2899_;
goto v___jp_2858_;
}
}
}
else
{
lean_object* v_a_2901_; 
lean_del_object(v___x_2817_);
lean_dec_ref(v_cfg_2781_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
v_a_2901_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2886_, 1);
v___y_2859_ = v_a_2865_;
v___y_2860_ = v___x_2885_;
v_a_2861_ = v_a_2901_;
goto v___jp_2858_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2774_, 2);
lean_dec_ref(v_cfg_2781_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
return v___x_2782_;
}
}
else
{
lean_dec_ref_known(v_goals_2774_, 2);
lean_dec(v_tail_2786_);
lean_dec_ref(v_cfg_2781_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
return v___x_2782_;
}
}
else
{
lean_dec_ref(v_cfg_2781_);
lean_dec(v_goals_2774_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
return v___x_2782_;
}
}
else
{
lean_dec_ref(v_cfg_2781_);
lean_dec(v_goals_2774_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
return v___x_2782_;
}
}
else
{
lean_dec_ref(v_cfg_2781_);
lean_dec(v_goals_2774_);
lean_dec_ref(v_ctx_2773_);
lean_dec(v_lemmas_2772_);
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2920_, lean_object* v_lemmas_2921_, lean_object* v_ctx_2922_, lean_object* v_goals_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2920_, v_lemmas_2921_, v_ctx_2922_, v_goals_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = l_List_reverse___redArg(v_x_2931_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
else
{
lean_object* v_head_2939_; lean_object* v_tail_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2964_; 
v_head_2939_ = lean_ctor_get(v_x_2930_, 0);
v_tail_2940_ = lean_ctor_get(v_x_2930_, 1);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_x_2930_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2942_ = v_x_2930_;
v_isShared_2943_ = v_isSharedCheck_2964_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_tail_2940_);
lean_inc(v_head_2939_);
lean_dec(v_x_2930_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2964_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Expr_applySymm(v_head_2939_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_x_2931_);
lean_ctor_set(v___x_2942_, 0, v_a_2945_);
v___x_2947_ = v___x_2942_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2945_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_x_2931_);
v___x_2947_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
v_x_2930_ = v_tail_2940_;
v_x_2931_ = v___x_2947_;
goto _start;
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2963_; 
lean_del_object(v___x_2942_);
v_a_2950_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2952_ = v___x_2944_;
v_isShared_2953_ = v_isSharedCheck_2963_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2944_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2963_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
uint8_t v___x_2954_; 
v___x_2954_ = l_Lean_Exception_isInterrupt(v_a_2950_);
if (v___x_2954_ == 0)
{
uint8_t v___x_2955_; 
lean_inc(v_a_2950_);
v___x_2955_ = l_Lean_Exception_isRuntime(v_a_2950_);
if (v___x_2955_ == 0)
{
lean_del_object(v___x_2952_);
lean_dec(v_a_2950_);
v_x_2930_ = v_tail_2940_;
goto _start;
}
else
{
lean_object* v___x_2958_; 
lean_dec(v_tail_2940_);
lean_dec(v_x_2931_);
if (v_isShared_2953_ == 0)
{
v___x_2958_ = v___x_2952_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2950_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
else
{
lean_object* v___x_2961_; 
lean_dec(v_tail_2940_);
lean_dec(v_x_2931_);
if (v_isShared_2953_ == 0)
{
v___x_2961_ = v___x_2952_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2950_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2965_, v_x_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2973_, lean_object* v_hyps_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
if (v_symm_2973_ == 0)
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_hyps_2974_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_box(0);
lean_inc(v_hyps_2974_);
v___x_2982_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2974_, v___x_2981_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2991_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2991_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2991_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = l_List_appendTR___redArg(v_hyps_2974_, v_a_2983_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2987_);
v___x_2989_ = v___x_2985_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_dec(v_hyps_2974_);
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_2992_, lean_object* v_hyps_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
uint8_t v_symm_boxed_2999_; lean_object* v_res_3000_; 
v_symm_boxed_2999_ = lean_unbox(v_symm_2992_);
v_res_3000_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_2999_, v_hyps_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3001_, size_t v_sz_3002_, size_t v_i_3003_, lean_object* v_b_3004_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_lt(v_i_3003_, v_sz_3002_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_b_3004_);
return v___x_3007_;
}
else
{
lean_object* v_snd_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3026_; 
v_snd_3008_ = lean_ctor_get(v_b_3004_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_b_3004_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v_b_3004_, 0);
lean_dec(v_unused_3027_);
v___x_3010_ = v_b_3004_;
v_isShared_3011_ = v_isSharedCheck_3026_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_snd_3008_);
lean_dec(v_b_3004_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3026_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v_a_3014_; lean_object* v_a_3021_; 
v___x_3012_ = lean_box(0);
v_a_3021_ = lean_array_uget_borrowed(v_as_3001_, v_i_3003_);
if (lean_obj_tag(v_a_3021_) == 0)
{
v_a_3014_ = v_snd_3008_;
goto v___jp_3013_;
}
else
{
lean_object* v_val_3022_; uint8_t v___x_3023_; 
v_val_3022_ = lean_ctor_get(v_a_3021_, 0);
v___x_3023_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_inc(v_val_3022_);
v___x_3024_ = l_Lean_LocalDecl_toExpr(v_val_3022_);
v___x_3025_ = lean_array_push(v_snd_3008_, v___x_3024_);
v_a_3014_ = v___x_3025_;
goto v___jp_3013_;
}
else
{
v_a_3014_ = v_snd_3008_;
goto v___jp_3013_;
}
}
v___jp_3013_:
{
lean_object* v___x_3016_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 1, v_a_3014_);
lean_ctor_set(v___x_3010_, 0, v___x_3012_);
v___x_3016_ = v___x_3010_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_a_3014_);
v___x_3016_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
size_t v___x_3017_; size_t v___x_3018_; 
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_add(v_i_3003_, v___x_3017_);
v_i_3003_ = v___x_3018_;
v_b_3004_ = v___x_3016_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3028_, lean_object* v_sz_3029_, lean_object* v_i_3030_, lean_object* v_b_3031_, lean_object* v___y_3032_){
_start:
{
size_t v_sz_boxed_3033_; size_t v_i_boxed_3034_; lean_object* v_res_3035_; 
v_sz_boxed_3033_ = lean_unbox_usize(v_sz_3029_);
lean_dec(v_sz_3029_);
v_i_boxed_3034_ = lean_unbox_usize(v_i_3030_);
lean_dec(v_i_3030_);
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3028_, v_sz_boxed_3033_, v_i_boxed_3034_, v_b_3031_);
lean_dec_ref(v_as_3028_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3036_, size_t v_sz_3037_, size_t v_i_3038_, lean_object* v_b_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_usize_dec_lt(v_i_3038_, v_sz_3037_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_b_3039_);
return v___x_3048_;
}
else
{
lean_object* v_snd_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3067_; 
v_snd_3049_ = lean_ctor_get(v_b_3039_, 1);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_b_3039_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v_b_3039_, 0);
lean_dec(v_unused_3068_);
v___x_3051_ = v_b_3039_;
v_isShared_3052_ = v_isSharedCheck_3067_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snd_3049_);
lean_dec(v_b_3039_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3067_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v_a_3055_; lean_object* v_a_3062_; 
v___x_3053_ = lean_box(0);
v_a_3062_ = lean_array_uget_borrowed(v_as_3036_, v_i_3038_);
if (lean_obj_tag(v_a_3062_) == 0)
{
v_a_3055_ = v_snd_3049_;
goto v___jp_3054_;
}
else
{
lean_object* v_val_3063_; uint8_t v___x_3064_; 
v_val_3063_ = lean_ctor_get(v_a_3062_, 0);
v___x_3064_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_inc(v_val_3063_);
v___x_3065_ = l_Lean_LocalDecl_toExpr(v_val_3063_);
v___x_3066_ = lean_array_push(v_snd_3049_, v___x_3065_);
v_a_3055_ = v___x_3066_;
goto v___jp_3054_;
}
else
{
v_a_3055_ = v_snd_3049_;
goto v___jp_3054_;
}
}
v___jp_3054_:
{
lean_object* v___x_3057_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v_a_3055_);
lean_ctor_set(v___x_3051_, 0, v___x_3053_);
v___x_3057_ = v___x_3051_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3055_);
v___x_3057_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_add(v_i_3038_, v___x_3058_);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3036_, v_sz_3037_, v___x_3059_, v___x_3057_);
return v___x_3060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3069_, lean_object* v_sz_3070_, lean_object* v_i_3071_, lean_object* v_b_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
size_t v_sz_boxed_3080_; size_t v_i_boxed_3081_; lean_object* v_res_3082_; 
v_sz_boxed_3080_ = lean_unbox_usize(v_sz_3070_);
lean_dec(v_sz_3070_);
v_i_boxed_3081_ = lean_unbox_usize(v_i_3071_);
lean_dec(v_i_3071_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3069_, v_sz_boxed_3080_, v_i_boxed_3081_, v_b_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v_as_3069_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3083_, size_t v_sz_3084_, size_t v_i_3085_, lean_object* v_b_3086_){
_start:
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_usize_dec_lt(v_i_3085_, v_sz_3084_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_b_3086_);
return v___x_3089_;
}
else
{
lean_object* v_snd_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3108_; 
v_snd_3090_ = lean_ctor_get(v_b_3086_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_b_3086_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v_b_3086_, 0);
lean_dec(v_unused_3109_);
v___x_3092_ = v_b_3086_;
v_isShared_3093_ = v_isSharedCheck_3108_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_snd_3090_);
lean_dec(v_b_3086_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3108_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v_a_3096_; lean_object* v_a_3103_; 
v___x_3094_ = lean_box(0);
v_a_3103_ = lean_array_uget_borrowed(v_as_3083_, v_i_3085_);
if (lean_obj_tag(v_a_3103_) == 0)
{
v_a_3096_ = v_snd_3090_;
goto v___jp_3095_;
}
else
{
lean_object* v_val_3104_; uint8_t v___x_3105_; 
v_val_3104_ = lean_ctor_get(v_a_3103_, 0);
v___x_3105_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_inc(v_val_3104_);
v___x_3106_ = l_Lean_LocalDecl_toExpr(v_val_3104_);
v___x_3107_ = lean_array_push(v_snd_3090_, v___x_3106_);
v_a_3096_ = v___x_3107_;
goto v___jp_3095_;
}
else
{
v_a_3096_ = v_snd_3090_;
goto v___jp_3095_;
}
}
v___jp_3095_:
{
lean_object* v___x_3098_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v_a_3096_);
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3098_ = v___x_3092_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_a_3096_);
v___x_3098_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
size_t v___x_3099_; size_t v___x_3100_; 
v___x_3099_ = ((size_t)1ULL);
v___x_3100_ = lean_usize_add(v_i_3085_, v___x_3099_);
v_i_3085_ = v___x_3100_;
v_b_3086_ = v___x_3098_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3110_, lean_object* v_sz_3111_, lean_object* v_i_3112_, lean_object* v_b_3113_, lean_object* v___y_3114_){
_start:
{
size_t v_sz_boxed_3115_; size_t v_i_boxed_3116_; lean_object* v_res_3117_; 
v_sz_boxed_3115_ = lean_unbox_usize(v_sz_3111_);
lean_dec(v_sz_3111_);
v_i_boxed_3116_ = lean_unbox_usize(v_i_3112_);
lean_dec(v_i_3112_);
v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3110_, v_sz_boxed_3115_, v_i_boxed_3116_, v_b_3113_);
lean_dec_ref(v_as_3110_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3118_, size_t v_sz_3119_, size_t v_i_3120_, lean_object* v_b_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_usize_dec_lt(v_i_3120_, v_sz_3119_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_b_3121_);
return v___x_3130_;
}
else
{
lean_object* v_snd_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3149_; 
v_snd_3131_ = lean_ctor_get(v_b_3121_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_b_3121_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_b_3121_, 0);
lean_dec(v_unused_3150_);
v___x_3133_ = v_b_3121_;
v_isShared_3134_ = v_isSharedCheck_3149_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_snd_3131_);
lean_dec(v_b_3121_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3149_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v_a_3137_; lean_object* v_a_3144_; 
v___x_3135_ = lean_box(0);
v_a_3144_ = lean_array_uget_borrowed(v_as_3118_, v_i_3120_);
if (lean_obj_tag(v_a_3144_) == 0)
{
v_a_3137_ = v_snd_3131_;
goto v___jp_3136_;
}
else
{
lean_object* v_val_3145_; uint8_t v___x_3146_; 
v_val_3145_ = lean_ctor_get(v_a_3144_, 0);
v___x_3146_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_inc(v_val_3145_);
v___x_3147_ = l_Lean_LocalDecl_toExpr(v_val_3145_);
v___x_3148_ = lean_array_push(v_snd_3131_, v___x_3147_);
v_a_3137_ = v___x_3148_;
goto v___jp_3136_;
}
else
{
v_a_3137_ = v_snd_3131_;
goto v___jp_3136_;
}
}
v___jp_3136_:
{
lean_object* v___x_3139_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 1, v_a_3137_);
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3139_ = v___x_3133_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_a_3137_);
v___x_3139_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = ((size_t)1ULL);
v___x_3141_ = lean_usize_add(v_i_3120_, v___x_3140_);
v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3118_, v_sz_3119_, v___x_3141_, v___x_3139_);
return v___x_3142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3151_, lean_object* v_sz_3152_, lean_object* v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
size_t v_sz_boxed_3162_; size_t v_i_boxed_3163_; lean_object* v_res_3164_; 
v_sz_boxed_3162_ = lean_unbox_usize(v_sz_3152_);
lean_dec(v_sz_3152_);
v_i_boxed_3163_ = lean_unbox_usize(v_i_3153_);
lean_dec(v_i_3153_);
v_res_3164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3151_, v_sz_boxed_3162_, v_i_boxed_3163_, v_b_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v_as_3151_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3165_, lean_object* v_n_3166_, lean_object* v_b_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
if (lean_obj_tag(v_n_3166_) == 0)
{
lean_object* v_cs_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; size_t v_sz_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v_cs_3175_ = lean_ctor_get(v_n_3166_, 0);
v___x_3176_ = lean_box(0);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v_b_3167_);
v_sz_3178_ = lean_array_size(v_cs_3175_);
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3165_, v_cs_3175_, v_sz_3178_, v___x_3179_, v___x_3177_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3195_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3195_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3195_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_fst_3185_; 
v_fst_3185_ = lean_ctor_get(v_a_3181_, 0);
if (lean_obj_tag(v_fst_3185_) == 0)
{
lean_object* v_snd_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v_snd_3186_ = lean_ctor_get(v_a_3181_, 1);
lean_inc(v_snd_3186_);
lean_dec(v_a_3181_);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_snd_3186_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3187_);
v___x_3189_ = v___x_3183_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
else
{
lean_object* v_val_3191_; lean_object* v___x_3193_; 
lean_inc_ref(v_fst_3185_);
lean_dec(v_a_3181_);
v_val_3191_ = lean_ctor_get(v_fst_3185_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v_fst_3185_, 1);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v_val_3191_);
v___x_3193_ = v___x_3183_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_val_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3180_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3180_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v_vs_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; size_t v_sz_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v_vs_3204_ = lean_ctor_get(v_n_3166_, 0);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v_b_3167_);
v_sz_3207_ = lean_array_size(v_vs_3204_);
v___x_3208_ = ((size_t)0ULL);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3204_, v_sz_3207_, v___x_3208_, v___x_3206_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3224_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3224_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3224_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v_fst_3214_; 
v_fst_3214_ = lean_ctor_get(v_a_3210_, 0);
if (lean_obj_tag(v_fst_3214_) == 0)
{
lean_object* v_snd_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
v_snd_3215_ = lean_ctor_get(v_a_3210_, 1);
lean_inc(v_snd_3215_);
lean_dec(v_a_3210_);
v___x_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_snd_3215_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3216_);
v___x_3218_ = v___x_3212_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
else
{
lean_object* v_val_3220_; lean_object* v___x_3222_; 
lean_inc_ref(v_fst_3214_);
lean_dec(v_a_3210_);
v_val_3220_ = lean_ctor_get(v_fst_3214_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v_fst_3214_, 1);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v_val_3220_);
v___x_3222_ = v___x_3212_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_val_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
v_a_3225_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3209_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3209_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3233_, lean_object* v_as_3234_, size_t v_sz_3235_, size_t v_i_3236_, lean_object* v_b_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_lt(v_i_3236_, v_sz_3235_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_b_3237_);
return v___x_3246_;
}
else
{
lean_object* v_snd_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3281_; 
v_snd_3247_ = lean_ctor_get(v_b_3237_, 1);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_b_3237_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_b_3237_, 0);
lean_dec(v_unused_3282_);
v___x_3249_ = v_b_3237_;
v_isShared_3250_ = v_isSharedCheck_3281_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_snd_3247_);
lean_dec(v_b_3237_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3281_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v_a_3252_; lean_object* v___x_3253_; 
v___x_3251_ = lean_box(0);
v_a_3252_ = lean_array_uget_borrowed(v_as_3234_, v_i_3236_);
lean_inc(v_snd_3247_);
v___x_3253_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3233_, v_a_3252_, v_snd_3247_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3272_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3272_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3272_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
if (lean_obj_tag(v_a_3254_) == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_a_3254_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3258_);
v___x_3260_ = v___x_3249_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_snd_3247_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3260_);
v___x_3262_ = v___x_3256_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; 
lean_del_object(v___x_3256_);
lean_dec(v_snd_3247_);
v_a_3265_ = lean_ctor_get(v_a_3254_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v_a_3254_, 1);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v_a_3265_);
lean_ctor_set(v___x_3249_, 0, v___x_3251_);
v___x_3267_ = v___x_3249_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_a_3265_);
v___x_3267_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
size_t v___x_3268_; size_t v___x_3269_; 
v___x_3268_ = ((size_t)1ULL);
v___x_3269_ = lean_usize_add(v_i_3236_, v___x_3268_);
v_i_3236_ = v___x_3269_;
v_b_3237_ = v___x_3267_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_del_object(v___x_3249_);
lean_dec(v_snd_3247_);
v_a_3273_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3253_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3253_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3283_, lean_object* v_as_3284_, lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
size_t v_sz_boxed_3295_; size_t v_i_boxed_3296_; lean_object* v_res_3297_; 
v_sz_boxed_3295_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3296_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3283_, v_as_3284_, v_sz_boxed_3295_, v_i_boxed_3296_, v_b_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec_ref(v_as_3284_);
lean_dec_ref(v_init_3283_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3298_, lean_object* v_n_3299_, lean_object* v_b_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3298_, v_n_3299_, v_b_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec_ref(v_n_3299_);
lean_dec_ref(v_init_3298_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3309_, lean_object* v_init_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_root_3318_; lean_object* v_tail_3319_; lean_object* v___x_3320_; 
v_root_3318_ = lean_ctor_get(v_t_3309_, 0);
v_tail_3319_ = lean_ctor_get(v_t_3309_, 1);
lean_inc_ref(v_init_3310_);
v___x_3320_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3310_, v_root_3318_, v_init_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec_ref(v_init_3310_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3357_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3323_ = v___x_3320_;
v_isShared_3324_ = v_isSharedCheck_3357_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3357_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
if (lean_obj_tag(v_a_3321_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; 
v_a_3325_ = lean_ctor_get(v_a_3321_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v_a_3321_, 1);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v_a_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; size_t v_sz_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
lean_del_object(v___x_3323_);
v_a_3329_ = lean_ctor_get(v_a_3321_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v_a_3321_, 1);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v_a_3329_);
v_sz_3332_ = lean_array_size(v_tail_3319_);
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3319_, v_sz_3332_, v___x_3333_, v___x_3331_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3348_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3348_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3348_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_fst_3339_; 
v_fst_3339_ = lean_ctor_get(v_a_3335_, 0);
if (lean_obj_tag(v_fst_3339_) == 0)
{
lean_object* v_snd_3340_; lean_object* v___x_3342_; 
v_snd_3340_ = lean_ctor_get(v_a_3335_, 1);
lean_inc(v_snd_3340_);
lean_dec(v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v_snd_3340_);
v___x_3342_ = v___x_3337_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_snd_3340_);
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
lean_object* v_val_3344_; lean_object* v___x_3346_; 
lean_inc_ref(v_fst_3339_);
lean_dec(v_a_3335_);
v_val_3344_ = lean_ctor_get(v_fst_3339_, 0);
lean_inc(v_val_3344_);
lean_dec_ref_known(v_fst_3339_, 1);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v_val_3344_);
v___x_3346_ = v___x_3337_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_val_3344_);
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
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3334_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3334_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_a_3358_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3320_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3320_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3366_, lean_object* v_init_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3366_, v_init_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec_ref(v_t_3366_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_lctx_3385_; lean_object* v_decls_3386_; lean_object* v_hs_3387_; lean_object* v___x_3388_; 
v_lctx_3385_ = lean_ctor_get(v___y_3380_, 2);
v_decls_3386_ = lean_ctor_get(v_lctx_3385_, 1);
v_hs_3387_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3388_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3386_, v_hs_3387_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3397_, lean_object* v_cfg_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
if (v_only_3397_ == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_toApplyRulesConfig_3407_; lean_object* v_a_3408_; uint8_t v_symm_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_toApplyRulesConfig_3407_ = lean_ctor_get(v_cfg_3398_, 0);
v_a_3408_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3406_, 1);
v_symm_3409_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3407_, sizeof(void*)*2 + 1);
v___x_3410_ = lean_array_to_list(v_a_3408_);
v___x_3411_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3409_, v___x_3410_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
return v___x_3411_;
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
v_a_3412_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3406_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3406_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3422_, lean_object* v_cfg_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v_only_boxed_3431_; lean_object* v_res_3432_; 
v_only_boxed_3431_ = lean_unbox(v_only_3422_);
v_res_3432_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3431_, v_cfg_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v_cfg_3423_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3433_, lean_object* v_lemmas_3434_, uint8_t v_only_3435_, lean_object* v_g_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_toApplyRulesConfig_3442_; uint8_t v_intro_3443_; uint8_t v_constructor_3444_; uint8_t v_suggestions_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3458_; 
v_toApplyRulesConfig_3442_ = lean_ctor_get(v_cfg_3433_, 0);
v_intro_3443_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*1 + 1);
v_constructor_3444_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*1 + 2);
v_suggestions_3445_ = lean_ctor_get_uint8(v_cfg_3433_, sizeof(void*)*1 + 3);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_cfg_3433_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3447_ = v_cfg_3433_;
v_isShared_3448_ = v_isSharedCheck_3458_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_toApplyRulesConfig_3442_);
lean_dec(v_cfg_3433_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3458_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_ctx_3450_; uint8_t v___x_3451_; lean_object* v___x_3453_; 
v___x_3449_ = lean_box(v_only_3435_);
v_ctx_3450_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3450_, 0, v___x_3449_);
v___x_3451_ = 0;
if (v_isShared_3448_ == 0)
{
v___x_3453_ = v___x_3447_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_toApplyRulesConfig_3442_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*1 + 1, v_intro_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*1 + 2, v_constructor_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*1 + 3, v_suggestions_3445_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_ctor_set_uint8(v___x_3453_, sizeof(void*)*1, v___x_3451_);
v___x_3454_ = lean_box(0);
v___x_3455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3455_, 0, v_g_3436_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3453_, v_lemmas_3434_, v_ctx_3450_, v___x_3455_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
return v___x_3456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3459_, lean_object* v_lemmas_3460_, lean_object* v_only_3461_, lean_object* v_g_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
uint8_t v_only_boxed_3468_; lean_object* v_res_3469_; 
v_only_boxed_3468_ = lean_unbox(v_only_3461_);
v_res_3469_ = l_Lean_MVarId_applyRules(v_cfg_3459_, v_lemmas_3460_, v_only_boxed_3468_, v_g_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3470_, size_t v_sz_3471_, size_t v_i_3472_, lean_object* v_b_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; 
v___x_3481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3470_, v_sz_3471_, v_i_3472_, v_b_3473_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3482_, lean_object* v_sz_3483_, lean_object* v_i_3484_, lean_object* v_b_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
size_t v_sz_boxed_3493_; size_t v_i_boxed_3494_; lean_object* v_res_3495_; 
v_sz_boxed_3493_ = lean_unbox_usize(v_sz_3483_);
lean_dec(v_sz_3483_);
v_i_boxed_3494_ = lean_unbox_usize(v_i_3484_);
lean_dec(v_i_3484_);
v_res_3495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3482_, v_sz_boxed_3493_, v_i_boxed_3494_, v_b_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v_as_3482_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3496_, size_t v_sz_3497_, size_t v_i_3498_, lean_object* v_b_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3496_, v_sz_3497_, v_i_3498_, v_b_3499_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3508_, lean_object* v_sz_3509_, lean_object* v_i_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
size_t v_sz_boxed_3519_; size_t v_i_boxed_3520_; lean_object* v_res_3521_; 
v_sz_boxed_3519_ = lean_unbox_usize(v_sz_3509_);
lean_dec(v_sz_3509_);
v_i_boxed_3520_ = lean_unbox_usize(v_i_3510_);
lean_dec(v_i_3510_);
v_res_3521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3508_, v_sz_boxed_3519_, v_i_boxed_3520_, v_b_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v_as_3508_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_box(0);
v___x_3531_ = 1;
v___x_3532_ = l_Lean_Elab_Term_elabTerm(v_t_3522_, v___x_3530_, v___x_3531_, v___x_3531_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_ref_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_ref_3547_ = lean_ctor_get(v___y_3544_, 2);
v___x_3548_ = 0;
v___x_3549_ = l_Lean_SourceInfo_fromRef(v_ref_3547_, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
return v_res_3556_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(lean_object* v_a_3557_, lean_object* v_x_3558_){
_start:
{
if (lean_obj_tag(v_x_3558_) == 0)
{
uint8_t v___x_3559_; 
v___x_3559_ = 0;
return v___x_3559_;
}
else
{
lean_object* v_head_3560_; lean_object* v_tail_3561_; uint8_t v___x_3562_; 
v_head_3560_ = lean_ctor_get(v_x_3558_, 0);
v_tail_3561_ = lean_ctor_get(v_x_3558_, 1);
v___x_3562_ = lean_expr_eqv(v_a_3557_, v_head_3560_);
if (v___x_3562_ == 0)
{
v_x_3558_ = v_tail_3561_;
goto _start;
}
else
{
return v___x_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1___boxed(lean_object* v_a_3564_, lean_object* v_x_3565_){
_start:
{
uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_res_3566_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_a_3564_, v_x_3565_);
lean_dec(v_x_3565_);
lean_dec_ref(v_a_3564_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__2(lean_object* v_ys_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
if (lean_obj_tag(v_a_3569_) == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = l_List_reverse___redArg(v_a_3570_);
return v___x_3571_;
}
else
{
lean_object* v_head_3572_; lean_object* v_tail_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3583_; 
v_head_3572_ = lean_ctor_get(v_a_3569_, 0);
v_tail_3573_ = lean_ctor_get(v_a_3569_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_a_3569_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3575_ = v_a_3569_;
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_tail_3573_);
lean_inc(v_head_3572_);
lean_dec(v_a_3569_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
uint8_t v___x_3577_; 
v___x_3577_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__1(v_head_3572_, v_ys_3568_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3579_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 1, v_a_3570_);
v___x_3579_ = v___x_3575_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_head_3572_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_a_3570_);
v___x_3579_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
v_a_3569_ = v_tail_3573_;
v_a_3570_ = v___x_3579_;
goto _start;
}
}
else
{
lean_del_object(v___x_3575_);
lean_dec(v_head_3572_);
v_a_3569_ = v_tail_3573_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__2___boxed(lean_object* v_ys_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_List_filterTR_loop___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__2(v_ys_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_ys_3584_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_xs_3588_, lean_object* v_ys_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = lean_box(0);
v___x_3591_ = l_List_filterTR_loop___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1_spec__2(v_ys_3589_, v_xs_3588_, v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_xs_3592_, lean_object* v_ys_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_xs_3592_, v_ys_3593_);
lean_dec(v_ys_3593_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(lean_object* v_x_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
if (lean_obj_tag(v_x_3595_) == 0)
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = l_List_reverse___redArg(v_x_3596_);
v___x_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
return v___x_3605_;
}
else
{
lean_object* v_head_3606_; lean_object* v_tail_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3625_; 
v_head_3606_ = lean_ctor_get(v_x_3595_, 0);
v_tail_3607_ = lean_ctor_get(v_x_3595_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_x_3595_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3609_ = v_x_3595_;
v_isShared_3610_ = v_isSharedCheck_3625_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_tail_3607_);
lean_inc(v_head_3606_);
lean_dec(v_x_3595_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3625_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; 
v___x_3611_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3606_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v_x_3596_);
lean_ctor_set(v___x_3609_, 0, v_a_3612_);
v___x_3614_ = v___x_3609_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3612_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_x_3596_);
v___x_3614_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
v_x_3595_ = v_tail_3607_;
v_x_3596_ = v___x_3614_;
goto _start;
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_del_object(v___x_3609_);
lean_dec(v_tail_3607_);
lean_dec(v_x_3596_);
v_a_3617_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3611_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3611_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_x_3626_, lean_object* v_x_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_x_3626_, v_x_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3636_, uint8_t v_noDefaults_3637_, uint8_t v_star_3638_, lean_object* v_cfg_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
if (v_noDefaults_3637_ == 0)
{
goto v___jp_3647_;
}
else
{
if (v_star_3638_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_dec(v_remove_3636_);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
else
{
goto v___jp_3647_;
}
}
v___jp_3647_:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
v___x_3650_ = lean_box(0);
v___x_3651_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_remove_3636_, v___x_3650_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_toApplyRulesConfig_3652_; lean_object* v_a_3653_; uint8_t v_symm_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_toApplyRulesConfig_3652_ = lean_ctor_get(v_cfg_3639_, 0);
v_a_3653_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3651_, 1);
v_symm_3654_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3652_, sizeof(void*)*2 + 1);
v___x_3655_ = lean_array_to_list(v_a_3649_);
v___x_3656_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v___x_3655_, v_a_3653_);
lean_dec(v_a_3653_);
v___x_3657_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3654_, v___x_3656_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3657_;
}
else
{
lean_dec(v_a_3649_);
return v___x_3651_;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_remove_3636_);
v_a_3658_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3648_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3648_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3668_, lean_object* v_noDefaults_3669_, lean_object* v_star_3670_, lean_object* v_cfg_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
uint8_t v_noDefaults_boxed_3679_; uint8_t v_star_boxed_3680_; lean_object* v_res_3681_; 
v_noDefaults_boxed_3679_ = lean_unbox(v_noDefaults_3669_);
v_star_boxed_3680_ = lean_unbox(v_star_3670_);
v_res_3681_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3668_, v_noDefaults_boxed_3679_, v_star_boxed_3680_, v_cfg_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec_ref(v_cfg_3671_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(size_t v_sz_3682_, size_t v_i_3683_, lean_object* v_bs_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
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
lean_object* v_v_3690_; lean_object* v___x_3691_; lean_object* v_bs_x27_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_v_3690_ = lean_array_uget(v_bs_3684_, v_i_3683_);
v___x_3691_ = lean_unsigned_to_nat(0u);
v_bs_x27_3692_ = lean_array_uset(v_bs_3684_, v_i_3683_, v___x_3691_);
v___x_3693_ = l_Lean_Syntax_getId(v_v_3690_);
lean_dec(v_v_3690_);
v___x_3694_ = l_Lean_labelled(v___x_3693_, v___y_3685_, v___y_3686_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v___x_3696_ = ((size_t)1ULL);
v___x_3697_ = lean_usize_add(v_i_3683_, v___x_3696_);
v___x_3698_ = lean_array_uset(v_bs_x27_3692_, v_i_3683_, v_a_3695_);
v_i_3683_ = v___x_3697_;
v_bs_3684_ = v___x_3698_;
goto _start;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v_bs_x27_3692_);
v_a_3700_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3694_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3694_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg___boxed(lean_object* v_sz_3708_, lean_object* v_i_3709_, lean_object* v_bs_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3708_);
lean_dec(v_sz_3708_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3709_);
lean_dec(v_i_3709_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_boxed_3714_, v_i_boxed_3715_, v_bs_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3717_, size_t v_i_3718_, size_t v_stop_3719_, lean_object* v_b_3720_){
_start:
{
uint8_t v___x_3721_; 
v___x_3721_ = lean_usize_dec_eq(v_i_3718_, v_stop_3719_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; 
v___x_3722_ = lean_array_uget_borrowed(v_as_3717_, v_i_3718_);
v___x_3723_ = l_Array_append___redArg(v_b_3720_, v___x_3722_);
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_add(v_i_3718_, v___x_3724_);
v_i_3718_ = v___x_3725_;
v_b_3720_ = v___x_3723_;
goto _start;
}
else
{
return v_b_3720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3727_, lean_object* v_i_3728_, lean_object* v_stop_3729_, lean_object* v_b_3730_){
_start:
{
size_t v_i_boxed_3731_; size_t v_stop_boxed_3732_; lean_object* v_res_3733_; 
v_i_boxed_3731_ = lean_unbox_usize(v_i_3728_);
lean_dec(v_i_3728_);
v_stop_boxed_3732_ = lean_unbox_usize(v_stop_3729_);
lean_dec(v_stop_3729_);
v_res_3733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3727_, v_i_boxed_3731_, v_stop_boxed_3732_, v_b_3730_);
lean_dec_ref(v_as_3727_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3734_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
if (lean_obj_tag(v_a_3752_) == 0)
{
lean_object* v___x_3754_; 
v___x_3754_ = l_List_reverse___redArg(v_a_3753_);
return v___x_3754_;
}
else
{
lean_object* v_head_3755_; lean_object* v_tail_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3765_; 
v_head_3755_ = lean_ctor_get(v_a_3752_, 0);
v_tail_3756_ = lean_ctor_get(v_a_3752_, 1);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_a_3752_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3758_ = v_a_3752_;
v_isShared_3759_ = v_isSharedCheck_3765_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_tail_3756_);
lean_inc(v_head_3755_);
lean_dec(v_a_3752_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3765_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___f_3760_; lean_object* v___x_3762_; 
v___f_3760_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3760_, 0, v_head_3755_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 1, v_a_3753_);
lean_ctor_set(v___x_3758_, 0, v___f_3760_);
v___x_3762_ = v___x_3758_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___f_3760_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_a_3753_);
v___x_3762_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
v_a_3752_ = v_tail_3756_;
v_a_3753_ = v___x_3762_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
if (lean_obj_tag(v_a_3766_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = l_List_reverse___redArg(v_a_3767_);
return v___x_3768_;
}
else
{
lean_object* v_head_3769_; lean_object* v_tail_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3779_; 
v_head_3769_ = lean_ctor_get(v_a_3766_, 0);
v_tail_3770_ = lean_ctor_get(v_a_3766_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3772_ = v_a_3766_;
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_tail_3770_);
lean_inc(v_head_3769_);
lean_dec(v_a_3766_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3774_, 0, v_head_3769_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_a_3767_);
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3776_ = v___x_3772_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_a_3767_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
v_a_3766_ = v_tail_3770_;
v_a_3767_ = v___x_3776_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3782_ = l_Lean_stringToMessageData(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3785_ = l_String_toRawSubstring_x27(v___x_3784_);
return v___x_3785_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3796_ = l_String_toRawSubstring_x27(v___x_3795_);
return v___x_3796_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12));
v___x_3807_ = l_String_toRawSubstring_x27(v___x_3806_);
return v___x_3807_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3818_ = l_String_toRawSubstring_x27(v___x_3817_);
return v___x_3818_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3832_, uint8_t v_star_3833_, lean_object* v_add_3834_, lean_object* v_remove_3835_, lean_object* v_use_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___f_3867_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; 
v___x_3865_ = lean_box(v_noDefaults_3832_);
v___x_3866_ = lean_box(v_star_3833_);
lean_inc(v_remove_3835_);
v___f_3867_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3867_, 0, v_remove_3835_);
lean_closure_set(v___f_3867_, 1, v___x_3865_);
lean_closure_set(v___f_3867_, 2, v___x_3866_);
if (v_star_3833_ == 0)
{
v___y_3884_ = v_a_3837_;
v___y_3885_ = v_a_3838_;
v___y_3886_ = v_a_3839_;
v___y_3887_ = v_a_3840_;
goto v___jp_3883_;
}
else
{
if (v_noDefaults_3832_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v___f_3867_);
lean_dec_ref(v_use_3836_);
lean_dec(v_remove_3835_);
lean_dec(v_add_3834_);
v___x_3944_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3945_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3944_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
v___y_3884_ = v_a_3837_;
v___y_3885_ = v_a_3838_;
v___y_3886_ = v_a_3839_;
v___y_3887_ = v_a_3840_;
goto v___jp_3883_;
}
}
v___jp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___y_3843_);
lean_ctor_set(v___x_3845_, 1, v___y_3844_);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
return v___x_3846_;
}
v___jp_3847_:
{
uint8_t v___x_3854_; 
v___x_3854_ = l_List_isEmpty___redArg(v_remove_3835_);
lean_dec(v_remove_3835_);
if (v___x_3854_ == 0)
{
if (v_noDefaults_3832_ == 0)
{
v___y_3843_ = v___y_3853_;
v___y_3844_ = v___y_3848_;
goto v___jp_3842_;
}
else
{
if (v_star_3833_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3848_);
v___x_3855_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3856_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3855_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
else
{
v___y_3843_ = v___y_3853_;
v___y_3844_ = v___y_3848_;
goto v___jp_3842_;
}
}
}
else
{
v___y_3843_ = v___y_3853_;
v___y_3844_ = v___y_3848_;
goto v___jp_3842_;
}
}
v___jp_3868_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_array_to_list(v___y_3875_);
lean_inc(v___y_3872_);
v___x_3877_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3876_, v___y_3872_);
if (v_noDefaults_3832_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3834_, v___y_3872_);
v___x_3879_ = l_List_appendTR___redArg(v___x_3878_, v___x_3877_);
v___x_3880_ = l_List_appendTR___redArg(v___x_3879_, v___y_3873_);
v___y_3848_ = v___f_3867_;
v___y_3849_ = v___y_3869_;
v___y_3850_ = v___y_3870_;
v___y_3851_ = v___y_3871_;
v___y_3852_ = v___y_3874_;
v___y_3853_ = v___x_3880_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
lean_dec(v___y_3873_);
v___x_3881_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v_add_3834_, v___y_3872_);
v___x_3882_ = l_List_appendTR___redArg(v___x_3881_, v___x_3877_);
v___y_3848_ = v___f_3867_;
v___y_3849_ = v___y_3869_;
v___y_3850_ = v___y_3870_;
v___y_3851_ = v___y_3871_;
v___y_3852_ = v___y_3874_;
v___y_3853_ = v___x_3882_;
goto v___jp_3847_;
}
}
v___jp_3883_:
{
lean_object* v_toCold_3888_; lean_object* v_ref_3889_; lean_object* v_quotContext_3890_; lean_object* v_currMacroScope_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v_a_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; size_t v_sz_3926_; size_t v___x_3927_; lean_object* v___x_3928_; 
v_toCold_3888_ = lean_ctor_get(v___y_3886_, 0);
v_ref_3889_ = lean_ctor_get(v___y_3886_, 2);
v_quotContext_3890_ = lean_ctor_get(v_toCold_3888_, 8);
v_currMacroScope_3891_ = lean_ctor_get(v_toCold_3888_, 9);
v___x_3892_ = 0;
v___x_3893_ = l_Lean_SourceInfo_fromRef(v_ref_3889_, v___x_3892_);
v___x_3894_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3895_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3891_, 4);
lean_inc_n(v_quotContext_3890_, 4);
v___x_3896_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3895_, v_currMacroScope_3891_);
v___x_3897_ = lean_box(0);
v___x_3898_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6));
v___x_3899_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3893_);
lean_ctor_set(v___x_3899_, 1, v___x_3894_);
lean_ctor_set(v___x_3899_, 2, v___x_3896_);
lean_ctor_set(v___x_3899_, 3, v___x_3898_);
v___x_3900_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref(v___x_3900_);
v___x_3902_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8);
v___x_3903_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9));
v___x_3904_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3903_, v_currMacroScope_3891_);
v___x_3905_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3906_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3906_, 0, v_a_3901_);
lean_ctor_set(v___x_3906_, 1, v___x_3902_);
lean_ctor_set(v___x_3906_, 2, v___x_3904_);
lean_ctor_set(v___x_3906_, 3, v___x_3905_);
v___x_3907_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13);
v___x_3910_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14));
v___x_3911_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3910_, v_currMacroScope_3891_);
v___x_3912_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16));
v___x_3913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3913_, 0, v_a_3908_);
lean_ctor_set(v___x_3913_, 1, v___x_3909_);
lean_ctor_set(v___x_3913_, 2, v___x_3911_);
lean_ctor_set(v___x_3913_, 3, v___x_3912_);
v___x_3914_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref(v___x_3914_);
v___x_3916_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18);
v___x_3917_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3918_ = l_Lean_addMacroScope(v_quotContext_3890_, v___x_3917_, v_currMacroScope_3891_);
v___x_3919_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3920_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3920_, 0, v_a_3915_);
lean_ctor_set(v___x_3920_, 1, v___x_3916_);
lean_ctor_set(v___x_3920_, 2, v___x_3918_);
lean_ctor_set(v___x_3920_, 3, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3897_);
v___x_3922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3913_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3906_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3899_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3924_, v___x_3897_);
v_sz_3926_ = lean_array_size(v_use_3836_);
v___x_3927_ = ((size_t)0ULL);
v___x_3928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3926_, v___x_3927_, v_use_3836_, v___y_3886_, v___y_3887_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = lean_unsigned_to_nat(0u);
v___x_3931_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3932_ = lean_array_get_size(v_a_3929_);
v___x_3933_ = lean_nat_dec_lt(v___x_3930_, v___x_3932_);
if (v___x_3933_ == 0)
{
lean_dec(v_a_3929_);
v___y_3869_ = v___y_3884_;
v___y_3870_ = v___y_3885_;
v___y_3871_ = v___y_3886_;
v___y_3872_ = v___x_3897_;
v___y_3873_ = v___x_3925_;
v___y_3874_ = v___y_3887_;
v___y_3875_ = v___x_3931_;
goto v___jp_3868_;
}
else
{
size_t v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_usize_of_nat(v___x_3932_);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3929_, v___x_3927_, v___x_3934_, v___x_3931_);
lean_dec(v_a_3929_);
v___y_3869_ = v___y_3884_;
v___y_3870_ = v___y_3885_;
v___y_3871_ = v___y_3886_;
v___y_3872_ = v___x_3897_;
v___y_3873_ = v___x_3925_;
v___y_3874_ = v___y_3887_;
v___y_3875_ = v___x_3935_;
goto v___jp_3868_;
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v___x_3925_);
lean_dec_ref(v___f_3867_);
lean_dec(v_remove_3835_);
lean_dec(v_add_3834_);
v_a_3936_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3928_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3928_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3954_, lean_object* v_star_3955_, lean_object* v_add_3956_, lean_object* v_remove_3957_, lean_object* v_use_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_){
_start:
{
uint8_t v_noDefaults_boxed_3964_; uint8_t v_star_boxed_3965_; lean_object* v_res_3966_; 
v_noDefaults_boxed_3964_ = lean_unbox(v_noDefaults_3954_);
v_star_boxed_3965_ = lean_unbox(v_star_3955_);
v_res_3966_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3964_, v_star_boxed_3965_, v_add_3956_, v_remove_3957_, v_use_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(size_t v_sz_3967_, size_t v_i_3968_, lean_object* v_bs_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___redArg(v_sz_3967_, v_i_3968_, v_bs_3969_, v___y_3972_, v___y_3973_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3___boxed(lean_object* v_sz_3976_, lean_object* v_i_3977_, lean_object* v_bs_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
size_t v_sz_boxed_3984_; size_t v_i_boxed_3985_; lean_object* v_res_3986_; 
v_sz_boxed_3984_ = lean_unbox_usize(v_sz_3976_);
lean_dec(v_sz_3976_);
v_i_boxed_3985_ = lean_unbox_usize(v_i_3977_);
lean_dec(v_i_3977_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_sz_boxed_3984_, v_i_boxed_3985_, v_bs_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3986_;
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

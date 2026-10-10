// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.LoopProtection
// Imports: public import Lean.Meta.Tactic.Simp.Types public import Lean.Linter.Init
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
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "loopingSimpArgs"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 197, 78, 135, 53, 39, 179, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 451, .m_capacity = 451, .m_length = 450, .m_data = "When enabled, `simp` will check if the theorems passed as simp arguments (`simp [thm1]`) are possibly looping in the current simp set.\n\nMore precisely, it tries to simplify the right-hand side of the theorem and complains if that fails, which it typically does because of running out of recursion depth.\n\nThis is a relatively expensive check, so it i disabled by default, and only run after a `simp` call actually failed with a recursion depth error."};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(203, 225, 37, 249, 29, 246, 11, 175)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 143, 228, 91, 214, 79, 187, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_linter_loopingSimpArgs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "↓ "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1;
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = "↓ ← "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3;
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`."};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2;
static const lean_string_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
static const lean_string_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Possibly looping simp theorem: `"};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6;
static const lean_array_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Possibly caused by: "};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "loopProtection"};
static const lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(240, 184, 129, 165, 74, 170, 27, 160)}};
static const lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "loop protection for "};
static const lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ": got exception"};
static const lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_checkLoops___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__5;
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_60_;
v_res_60_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
return v_res_62_;
}
}
lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(lean_object* v_a_63_, lean_object* v_usedTheorems_64_, lean_object* v_a_x3f_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_cache_68_; lean_object* v_congrCache_69_; lean_object* v_dsimpCache_70_; lean_object* v_numSteps_71_; lean_object* v_diag_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_82_; 
v___x_67_ = lean_st_ref_take(v_a_63_);
v_cache_68_ = lean_ctor_get(v___x_67_, 0);
v_congrCache_69_ = lean_ctor_get(v___x_67_, 1);
v_dsimpCache_70_ = lean_ctor_get(v___x_67_, 2);
v_numSteps_71_ = lean_ctor_get(v___x_67_, 4);
v_diag_72_ = lean_ctor_get(v___x_67_, 5);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v___x_67_, 3);
lean_dec(v_unused_83_);
v___x_74_ = v___x_67_;
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_diag_72_);
lean_inc(v_numSteps_71_);
lean_inc(v_dsimpCache_70_);
lean_inc(v_congrCache_69_);
lean_inc(v_cache_68_);
lean_dec(v___x_67_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 3, v_usedTheorems_64_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_cache_68_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_congrCache_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_dsimpCache_70_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_usedTheorems_64_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v_numSteps_71_);
lean_ctor_set(v_reuseFailAlloc_81_, 5, v_diag_72_);
v___x_78_ = v_reuseFailAlloc_81_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_st_ref_put(v_a_63_, v___x_78_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_76_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_63_ = stack[0].m_obj;
lean_object* v_usedTheorems_64_ = stack[1].m_obj;
lean_object* v_a_x3f_65_ = stack[2].m_obj;
lean_object* v_res_84_;
v_res_84_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_63_, v_usedTheorems_64_, v_a_x3f_65_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0___boxed(lean_object* v_a_85_, lean_object* v_usedTheorems_86_, lean_object* v_a_x3f_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_85_, v_usedTheorems_86_, v_a_x3f_87_);
lean_dec(v_a_x3f_87_);
lean_dec(v_a_85_);
return v_res_89_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
return v___x_95_;
}
}
lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_usedTheorems_106_; lean_object* v___x_107_; lean_object* v_cache_108_; lean_object* v_congrCache_109_; lean_object* v_dsimpCache_110_; lean_object* v_numSteps_111_; lean_object* v_diag_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_150_; 
v___x_105_ = lean_st_ref_get(v_a_99_);
v_usedTheorems_106_ = lean_ctor_get(v___x_105_, 3);
lean_inc_ref(v_usedTheorems_106_);
lean_dec(v___x_105_);
v___x_107_ = lean_st_ref_take(v_a_99_);
v_cache_108_ = lean_ctor_get(v___x_107_, 0);
v_congrCache_109_ = lean_ctor_get(v___x_107_, 1);
v_dsimpCache_110_ = lean_ctor_get(v___x_107_, 2);
v_numSteps_111_ = lean_ctor_get(v___x_107_, 4);
v_diag_112_ = lean_ctor_get(v___x_107_, 5);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v___x_107_, 3);
lean_dec(v_unused_151_);
v___x_114_ = v___x_107_;
v_isShared_115_ = v_isSharedCheck_150_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_diag_112_);
lean_inc(v_numSteps_111_);
lean_inc(v_dsimpCache_110_);
lean_inc(v_congrCache_109_);
lean_inc(v_cache_108_);
lean_dec(v___x_107_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_150_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 3, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_cache_108_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_congrCache_109_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_dsimpCache_110_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v_numSteps_111_);
lean_ctor_set(v_reuseFailAlloc_149_, 5, v_diag_112_);
v___x_118_ = v_reuseFailAlloc_149_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v_r_120_; 
v___x_119_ = lean_st_ref_put(v_a_99_, v___x_118_);
lean_inc(v_a_103_);
lean_inc_ref(v_a_102_);
lean_inc(v_a_101_);
lean_inc_ref(v_a_100_);
lean_inc(v_a_99_);
lean_inc_ref(v_a_98_);
lean_inc(v_a_97_);
v_r_120_ = lean_apply_8(v_x_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, lean_box(0));
if (lean_obj_tag(v_r_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_137_; 
v_a_121_ = lean_ctor_get(v_r_120_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v_r_120_);
if (v_isSharedCheck_137_ == 0)
{
v___x_123_ = v_r_120_;
v_isShared_124_ = v_isSharedCheck_137_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v_r_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_137_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
lean_inc(v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_136_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v___x_127_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_99_, v_usedTheorems_106_, v___x_126_);
lean_dec_ref(v___x_126_);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v___x_127_, 0);
lean_dec(v_unused_135_);
v___x_129_ = v___x_127_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_dec(v___x_127_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_a_121_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_121_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_138_ = lean_ctor_get(v_r_120_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v_r_120_, 1);
v___x_139_ = lean_box(0);
v___x_140_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_99_, v_usedTheorems_106_, v___x_139_);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_140_, 0);
lean_dec(v_unused_148_);
v___x_142_ = v___x_140_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_dec(v___x_140_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 1);
lean_ctor_set(v___x_142_, 0, v_a_138_);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_138_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_withFreshUsedTheorems___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_96_ = stack[0].m_obj;
lean_object* v_a_97_ = stack[1].m_obj;
lean_object* v_a_98_ = stack[2].m_obj;
lean_object* v_a_99_ = stack[3].m_obj;
lean_object* v_a_100_ = stack[4].m_obj;
lean_object* v_a_101_ = stack[5].m_obj;
lean_object* v_a_102_ = stack[6].m_obj;
lean_object* v_a_103_ = stack[7].m_obj;
lean_object* v_res_152_;
v_res_152_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(v_x_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___boxed(lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(v_x_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
return v_res_162_;
}
}
lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems(lean_object* v_00_u03b1_163_, lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_usedTheorems_174_; lean_object* v___x_175_; lean_object* v_cache_176_; lean_object* v_congrCache_177_; lean_object* v_dsimpCache_178_; lean_object* v_numSteps_179_; lean_object* v_diag_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_218_; 
v___x_173_ = lean_st_ref_get(v_a_167_);
v_usedTheorems_174_ = lean_ctor_get(v___x_173_, 3);
lean_inc_ref(v_usedTheorems_174_);
lean_dec(v___x_173_);
v___x_175_ = lean_st_ref_take(v_a_167_);
v_cache_176_ = lean_ctor_get(v___x_175_, 0);
v_congrCache_177_ = lean_ctor_get(v___x_175_, 1);
v_dsimpCache_178_ = lean_ctor_get(v___x_175_, 2);
v_numSteps_179_ = lean_ctor_get(v___x_175_, 4);
v_diag_180_ = lean_ctor_get(v___x_175_, 5);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_175_, 3);
lean_dec(v_unused_219_);
v___x_182_ = v___x_175_;
v_isShared_183_ = v_isSharedCheck_218_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_diag_180_);
lean_inc(v_numSteps_179_);
lean_inc(v_dsimpCache_178_);
lean_inc(v_congrCache_177_);
lean_inc(v_cache_176_);
lean_dec(v___x_175_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_218_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 3, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_cache_176_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_congrCache_177_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_dsimpCache_178_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_numSteps_179_);
lean_ctor_set(v_reuseFailAlloc_217_, 5, v_diag_180_);
v___x_186_ = v_reuseFailAlloc_217_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v_r_188_; 
v___x_187_ = lean_st_ref_put(v_a_167_, v___x_186_);
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
v_r_188_ = lean_apply_8(v_x_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, lean_box(0));
if (lean_obj_tag(v_r_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_205_; 
v_a_189_ = lean_ctor_get(v_r_188_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_r_188_);
if (v_isSharedCheck_205_ == 0)
{
v___x_191_ = v_r_188_;
v_isShared_192_ = v_isSharedCheck_205_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v_r_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_205_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
lean_inc(v_a_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 1);
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_204_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v___x_195_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_167_, v_usedTheorems_174_, v___x_194_);
lean_dec_ref(v___x_194_);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v___x_195_, 0);
lean_dec(v_unused_203_);
v___x_197_ = v___x_195_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_dec(v___x_195_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v_a_189_);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_189_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_206_ = lean_ctor_get(v_r_188_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v_r_188_, 1);
v___x_207_ = lean_box(0);
v___x_208_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_167_, v_usedTheorems_174_, v___x_207_);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v___x_208_, 0);
lean_dec(v_unused_216_);
v___x_210_ = v___x_208_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_dec(v___x_208_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 1);
lean_ctor_set(v___x_210_, 0, v_a_206_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_206_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_withFreshUsedTheorems_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_164_ = stack[1].m_obj;
lean_object* v_a_165_ = stack[2].m_obj;
lean_object* v_a_166_ = stack[3].m_obj;
lean_object* v_a_167_ = stack[4].m_obj;
lean_object* v_a_168_ = stack[5].m_obj;
lean_object* v_a_169_ = stack[6].m_obj;
lean_object* v_a_170_ = stack[7].m_obj;
lean_object* v_a_171_ = stack[8].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Meta_Simp_withFreshUsedTheorems(lean_box(0), v_x_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___boxed(lean_object* v_00_u03b1_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_Simp_withFreshUsedTheorems(v_00_u03b1_221_, v_x_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(lean_object* v_x_241_){
_start:
{
switch(lean_obj_tag(v_x_241_))
{
case 0:
{
lean_object* v_declName_243_; uint8_t v_post_244_; uint8_t v_inv_245_; uint8_t v___x_246_; lean_object* v_r_247_; 
v_declName_243_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_declName_243_);
v_post_244_ = lean_ctor_get_uint8(v_x_241_, sizeof(void*)*1);
v_inv_245_ = lean_ctor_get_uint8(v_x_241_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_241_, 1);
v___x_246_ = 0;
v_r_247_ = l_Lean_MessageData_ofConstName(v_declName_243_, v___x_246_);
if (v_post_244_ == 0)
{
if (v_inv_245_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_r_247_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_r_247_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
else
{
if (v_inv_245_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_r_247_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_r_247_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
case 1:
{
lean_object* v_fvarId_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_267_; 
v_fvarId_258_ = lean_ctor_get(v_x_241_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_267_ == 0)
{
v___x_260_ = v_x_241_;
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_fvarId_258_);
lean_dec(v_x_241_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_262_ = l_Lean_mkFVar(v_fvarId_258_);
v___x_263_ = l_Lean_MessageData_ofExpr(v___x_262_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 0);
lean_ctor_set(v___x_260_, 0, v___x_263_);
v___x_265_ = v___x_260_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
case 2:
{
lean_object* v_ref_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_ref_268_ = lean_ctor_get(v_x_241_, 1);
lean_inc(v_ref_268_);
lean_dec_ref_known(v_x_241_, 2);
v___x_269_ = l_Lean_MessageData_ofSyntax(v_ref_268_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
default: 
{
lean_object* v_name_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_name_271_ = lean_ctor_get(v_x_241_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_279_ == 0)
{
v___x_273_ = v_x_241_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_name_271_);
lean_dec(v_x_241_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_MessageData_ofName(v_name_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 0);
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_241_ = stack[0].m_obj;
lean_object* v_res_280_;
v_res_280_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_241_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___boxed(lean_object* v_x_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_281_);
return v_res_283_;
}
}
lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_284_);
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_284_ = stack[0].m_obj;
lean_object* v___y_285_ = stack[1].m_obj;
lean_object* v___y_286_ = stack[2].m_obj;
lean_object* v___y_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___boxed(lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(size_t v_sz_302_, size_t v_i_303_, lean_object* v_bs_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = lean_usize_dec_lt(v_i_303_, v_sz_302_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_bs_304_);
return v___x_311_;
}
else
{
lean_object* v_v_312_; lean_object* v___x_313_; lean_object* v_bs_x27_314_; lean_object* v_a_316_; lean_object* v___x_321_; 
v_v_312_ = lean_array_uget(v_bs_304_, v_i_303_);
v___x_313_ = lean_unsigned_to_nat(0u);
v_bs_x27_314_ = lean_array_uset(v_bs_304_, v_i_303_, v___x_313_);
v___x_321_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_v_312_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_a_322_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
v_a_316_ = v___x_325_;
goto v___jp_315_;
}
else
{
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_326_; 
v_a_326_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_321_, 1);
v_a_316_ = v_a_326_;
goto v___jp_315_;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_bs_x27_314_);
v_a_327_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_321_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_321_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
v___jp_315_:
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_add(v_i_303_, v___x_317_);
v___x_319_ = lean_array_uset(v_bs_x27_314_, v_i_303_, v_a_316_);
v_i_303_ = v___x_318_;
v_bs_304_ = v___x_319_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_302_ = stack[0].m_num;
size_t v_i_303_ = stack[1].m_num;
lean_object* v_bs_304_ = stack[2].m_obj;
lean_object* v___y_305_ = stack[3].m_obj;
lean_object* v___y_306_ = stack[4].m_obj;
lean_object* v___y_307_ = stack[5].m_obj;
lean_object* v___y_308_ = stack[6].m_obj;
lean_object* v_res_335_;
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_302_, v_i_303_, v_bs_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___boxed(lean_object* v_sz_336_, lean_object* v_i_337_, lean_object* v_bs_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
size_t v_sz_boxed_344_; size_t v_i_boxed_345_; lean_object* v_res_346_; 
v_sz_boxed_344_ = lean_unbox_usize(v_sz_336_);
lean_dec(v_sz_336_);
v_i_boxed_345_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_boxed_344_, v_i_boxed_345_, v_bs_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_346_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(lean_object* v_origins_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
size_t v_sz_353_; size_t v___x_354_; lean_object* v___x_355_; 
v_sz_353_ = lean_array_size(v_origins_347_);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_353_, v___x_354_, v_origins_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_365_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = lean_array_to_list(v_a_356_);
v___x_361_ = l_Lean_MessageData_andList(v___x_360_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_355_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_355_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_0interp(lean_interpreter_value* stack)
{
lean_object* v_origins_347_ = stack[0].m_obj;
lean_object* v_a_348_ = stack[1].m_obj;
lean_object* v_a_349_ = stack[2].m_obj;
lean_object* v_a_350_ = stack[3].m_obj;
lean_object* v_a_351_ = stack[4].m_obj;
lean_object* v_res_374_;
v_res_374_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_origins_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins___boxed(lean_object* v_origins_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_origins_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_381_;
}
}
lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(lean_object* v_x_382_){
_start:
{
switch(lean_obj_tag(v_x_382_))
{
case 0:
{
lean_object* v_declName_384_; uint8_t v_post_385_; uint8_t v_inv_386_; uint8_t v___x_387_; lean_object* v_r_388_; 
v_declName_384_ = lean_ctor_get(v_x_382_, 0);
lean_inc(v_declName_384_);
v_post_385_ = lean_ctor_get_uint8(v_x_382_, sizeof(void*)*1);
v_inv_386_ = lean_ctor_get_uint8(v_x_382_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_382_, 1);
v___x_387_ = 0;
v_r_388_ = l_Lean_MessageData_ofConstName(v_declName_384_, v___x_387_);
if (v_post_385_ == 0)
{
if (v_inv_386_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_r_388_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
v___x_393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_r_388_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
else
{
if (v_inv_386_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v_r_388_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_r_388_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
case 1:
{
lean_object* v_fvarId_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v_fvarId_399_ = lean_ctor_get(v_x_382_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_408_ == 0)
{
v___x_401_ = v_x_382_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_fvarId_399_);
lean_dec(v_x_382_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = l_Lean_mkFVar(v_fvarId_399_);
v___x_404_ = l_Lean_MessageData_ofExpr(v___x_403_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
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
case 2:
{
lean_object* v_ref_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_ref_409_ = lean_ctor_get(v_x_382_, 1);
lean_inc(v_ref_409_);
lean_dec_ref_known(v_x_382_, 2);
v___x_410_ = l_Lean_MessageData_ofSyntax(v_ref_409_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
default: 
{
lean_object* v_name_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_name_412_ = lean_ctor_get(v_x_382_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v_x_382_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_name_412_);
lean_dec(v_x_382_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = l_Lean_MessageData_ofName(v_name_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_382_ = stack[0].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_382_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg___boxed(lean_object* v_x_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_422_);
return v_res_424_;
}
}
lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_425_);
return v___x_434_;
}
}
LEAN_EXPORT void l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_425_ = stack[0].m_obj;
lean_object* v___y_426_ = stack[1].m_obj;
lean_object* v___y_427_ = stack[2].m_obj;
lean_object* v___y_428_ = stack[3].m_obj;
lean_object* v___y_429_ = stack[4].m_obj;
lean_object* v___y_430_ = stack[5].m_obj;
lean_object* v___y_431_ = stack[6].m_obj;
lean_object* v___y_432_ = stack[7].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___boxed(lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(v_x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
return v_res_445_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(lean_object* v___x_446_, lean_object* v_as_447_, size_t v_sz_448_, size_t v_i_449_, lean_object* v_b_450_){
_start:
{
lean_object* v_a_453_; uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_lt(v_i_449_, v_sz_448_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_b_450_);
return v___x_458_;
}
else
{
lean_object* v_a_459_; uint8_t v___y_463_; 
v_a_459_ = lean_array_uget_borrowed(v_as_447_, v_i_449_);
if (lean_obj_tag(v_a_459_) == 0)
{
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_declName_464_; uint8_t v_inv_465_; lean_object* v_declName_466_; uint8_t v_inv_467_; uint8_t v___x_468_; 
v_declName_464_ = lean_ctor_get(v_a_459_, 0);
v_inv_465_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*1 + 1);
v_declName_466_ = lean_ctor_get(v___x_446_, 0);
v_inv_467_ = lean_ctor_get_uint8(v___x_446_, sizeof(void*)*1 + 1);
v___x_468_ = lean_name_eq(v_declName_464_, v_declName_466_);
if (v___x_468_ == 0)
{
v___y_463_ = v___x_468_;
goto v___jp_462_;
}
else
{
if (v_inv_467_ == 0)
{
if (v_inv_465_ == 0)
{
v___y_463_ = v___x_468_;
goto v___jp_462_;
}
else
{
goto v___jp_460_;
}
}
else
{
v___y_463_ = v_inv_465_;
goto v___jp_462_;
}
}
}
else
{
goto v___jp_460_;
}
}
else
{
if (lean_obj_tag(v___x_446_) == 0)
{
goto v___jp_460_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Meta_Origin_key(v_a_459_);
v___x_470_ = l_Lean_Meta_Origin_key(v___x_446_);
v___x_471_ = lean_name_eq(v___x_469_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
v___y_463_ = v___x_471_;
goto v___jp_462_;
}
}
v___jp_460_:
{
lean_object* v___x_461_; 
lean_inc(v_a_459_);
v___x_461_ = lean_array_push(v_b_450_, v_a_459_);
v_a_453_ = v___x_461_;
goto v___jp_452_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
goto v___jp_460_;
}
else
{
v_a_453_ = v_b_450_;
goto v___jp_452_;
}
}
}
v___jp_452_:
{
size_t v___x_454_; size_t v___x_455_; 
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_449_, v___x_454_);
v_i_449_ = v___x_455_;
v_b_450_ = v_a_453_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_446_ = stack[0].m_obj;
lean_object* v_as_447_ = stack[1].m_obj;
size_t v_sz_448_ = stack[2].m_num;
size_t v_i_449_ = stack[3].m_num;
lean_object* v_b_450_ = stack[4].m_obj;
lean_object* v_res_472_;
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_446_, v_as_447_, v_sz_448_, v_i_449_, v_b_450_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(lean_object* v___x_473_, lean_object* v_as_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_b_477_, lean_object* v___y_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_480_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_473_, v_as_474_, v_sz_boxed_479_, v_i_boxed_480_, v_b_477_);
lean_dec_ref(v_as_474_);
lean_dec_ref(v___x_473_);
return v_res_481_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1);
v___x_486_ = l_Lean_MessageData_hint_x27(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4(void){
_start:
{
lean_object* v___x_488_; lean_object* v_msg_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v_msg_489_ = l_Lean_stringToMessageData(v___x_488_);
return v_msg_489_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg(lean_object* v_thm_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_msg_508_; lean_object* v_origin_512_; lean_object* v_msg_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_usedTheorems_524_; lean_object* v___x_525_; size_t v_sz_526_; size_t v___x_527_; lean_object* v___x_528_; 
v_origin_512_ = lean_ctor_get(v_thm_498_, 4);
lean_inc_ref_n(v_origin_512_, 2);
lean_dec_ref(v_thm_498_);
v_msg_513_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4);
v___x_514_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_512_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v_a_515_);
v___x_518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v_msg_513_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7));
v___x_523_ = lean_st_ref_get(v_a_501_);
v_usedTheorems_524_ = lean_ctor_get(v___x_523_, 3);
lean_inc_ref(v_usedTheorems_524_);
lean_dec(v___x_523_);
v___x_525_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_524_);
lean_dec_ref(v_usedTheorems_524_);
v_sz_526_ = lean_array_size(v___x_525_);
v___x_527_ = ((size_t)0ULL);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_512_, v___x_525_, v_sz_526_, v___x_527_, v___x_522_);
lean_dec_ref(v___x_525_);
lean_dec_ref(v_origin_512_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = lean_array_get_size(v_a_529_);
v___x_531_ = lean_nat_dec_eq(v___x_530_, v___x_521_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_529_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_a_533_);
v___x_536_ = l_Lean_MessageData_note(v___x_535_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_520_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v_msg_508_ = v___x_537_;
goto v___jp_507_;
}
else
{
lean_dec_ref_known(v___x_520_, 2);
return v___x_532_;
}
}
else
{
lean_dec(v_a_529_);
v_msg_508_ = v___x_520_;
goto v___jp_507_;
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref_known(v___x_520_, 2);
v_a_538_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_528_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_528_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v_msg_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_mkLoopWarningMsg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_498_ = stack[0].m_obj;
lean_object* v_a_499_ = stack[1].m_obj;
lean_object* v_a_500_ = stack[2].m_obj;
lean_object* v_a_501_ = stack[3].m_obj;
lean_object* v_a_502_ = stack[4].m_obj;
lean_object* v_a_503_ = stack[5].m_obj;
lean_object* v_a_504_ = stack[6].m_obj;
lean_object* v_a_505_ = stack[7].m_obj;
lean_object* v_res_546_;
v_res_546_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(lean_object* v_thm_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
return v_res_556_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(lean_object* v___x_557_, lean_object* v_as_558_, size_t v_sz_559_, size_t v_i_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_557_, v_as_558_, v_sz_559_, v_i_560_, v_b_561_);
return v___x_570_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_557_ = stack[0].m_obj;
lean_object* v_as_558_ = stack[1].m_obj;
size_t v_sz_559_ = stack[2].m_num;
size_t v_i_560_ = stack[3].m_num;
lean_object* v_b_561_ = stack[4].m_obj;
lean_object* v___y_562_ = stack[5].m_obj;
lean_object* v___y_563_ = stack[6].m_obj;
lean_object* v___y_564_ = stack[7].m_obj;
lean_object* v___y_565_ = stack[8].m_obj;
lean_object* v___y_566_ = stack[9].m_obj;
lean_object* v___y_567_ = stack[10].m_obj;
lean_object* v___y_568_ = stack[11].m_obj;
lean_object* v_res_571_;
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_557_, v_as_558_, v_sz_559_, v_i_560_, v_b_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(lean_object* v___x_572_, lean_object* v_as_573_, lean_object* v_sz_574_, lean_object* v_i_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_574_);
lean_dec(v_sz_574_);
v_i_boxed_586_ = lean_unbox_usize(v_i_575_);
lean_dec(v_i_575_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_572_, v_as_573_, v_sz_boxed_585_, v_i_boxed_586_, v_b_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v_as_573_);
lean_dec_ref(v___x_572_);
return v_res_587_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(lean_object* v_o_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_env_593_; lean_object* v___x_594_; lean_object* v_toEnvExtension_595_; lean_object* v_asyncMode_596_; lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v_merged_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v___x_591_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_592_ = lean_st_ref_get(v___y_589_);
v_env_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_ref(v_env_593_);
lean_dec(v___x_592_);
v___x_594_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_595_ = lean_ctor_get(v___x_594_, 0);
v_asyncMode_596_ = lean_ctor_get(v_toEnvExtension_595_, 2);
v___x_597_ = lean_box(0);
v___x_598_ = 0;
v___x_599_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_591_, v___x_594_, v_env_593_, v_asyncMode_596_, v___x_597_, v___x_598_);
v_merged_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_599_, 1);
lean_dec(v_unused_609_);
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_merged_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_merged_600_);
lean_ctor_set(v___x_602_, 0, v_o_588_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_o_588_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_merged_600_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_588_ = stack[0].m_obj;
lean_object* v___y_589_ = stack[1].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_588_, v___y_589_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(lean_object* v_o_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_611_, v___y_612_);
lean_dec(v___y_612_);
return v_res_614_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_615_);
v___x_619_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v___x_618_, v___y_616_);
return v___x_619_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_615_ = stack[0].m_obj;
lean_object* v___y_616_ = stack[1].m_obj;
lean_object* v_res_620_;
v_res_620_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v___y_615_, v___y_616_);
stack->m_obj
 = v_res_620_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_624_;
}
}
lean_object* l_Lean_Meta_Simp_shouldCheckLoops(uint8_t v_force_625_, lean_object* v_ctxt_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_config_630_; uint8_t v_singlePass_631_; 
v_config_630_ = lean_ctor_get(v_ctxt_626_, 0);
v_singlePass_631_ = lean_ctor_get_uint8(v_config_630_, sizeof(void*)*3 + 2);
if (v_singlePass_631_ == 0)
{
if (v_force_625_ == 0)
{
lean_object* v___x_632_; lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
v___x_632_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_627_, v_a_628_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_643_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_637_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_638_ = l_Lean_Linter_getLinterValue(v___x_637_, v_a_633_);
lean_dec(v_a_633_);
v___x_639_ = lean_box(v___x_638_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_639_);
v___x_641_ = v___x_635_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(v_force_625_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
else
{
uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = 0;
v___x_647_ = lean_box(v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_shouldCheckLoops_0interp(lean_interpreter_value* stack)
{
uint8_t v_force_625_ = stack[0].m_num;
lean_object* v_ctxt_626_ = stack[1].m_obj;
lean_object* v_a_627_ = stack[2].m_obj;
lean_object* v_a_628_ = stack[3].m_obj;
lean_object* v_res_649_;
v_res_649_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_625_, v_ctxt_626_, v_a_627_, v_a_628_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops___boxed(lean_object* v_force_650_, lean_object* v_ctxt_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
uint8_t v_force_boxed_655_; lean_object* v_res_656_; 
v_force_boxed_655_ = lean_unbox(v_force_650_);
v_res_656_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_655_, v_ctxt_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec_ref(v_ctxt_651_);
return v_res_656_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(lean_object* v_o_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_657_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_657_ = stack[0].m_obj;
lean_object* v___y_658_ = stack[1].m_obj;
lean_object* v___y_659_ = stack[2].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_657_, v___y_658_, v___y_659_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(lean_object* v_o_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v_res_667_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(lean_object* v_k_668_, lean_object* v_b_669_, lean_object* v_c_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_676_ = lean_apply_7(v_k_668_, v_b_669_, v_c_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, lean_box(0));
return v___x_676_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_668_ = stack[0].m_obj;
lean_object* v_b_669_ = stack[1].m_obj;
lean_object* v_c_670_ = stack[2].m_obj;
lean_object* v___y_671_ = stack[3].m_obj;
lean_object* v___y_672_ = stack[4].m_obj;
lean_object* v___y_673_ = stack[5].m_obj;
lean_object* v___y_674_ = stack[6].m_obj;
lean_object* v_res_677_;
v_res_677_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_668_, v_b_669_, v_c_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(lean_object* v_k_678_, lean_object* v_b_679_, lean_object* v_c_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_678_, v_b_679_, v_c_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(lean_object* v_type_687_, lean_object* v_k_688_, uint8_t v_cleanupAnnotations_689_, uint8_t v_whnfType_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_696_, 0, v_k_688_);
v___x_697_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_687_, v___f_696_, v_cleanupAnnotations_689_, v_whnfType_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
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
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_697_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_697_);
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
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_687_ = stack[0].m_obj;
lean_object* v_k_688_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_689_ = stack[2].m_num;
uint8_t v_whnfType_690_ = stack[3].m_num;
lean_object* v___y_691_ = stack[4].m_obj;
lean_object* v___y_692_ = stack[5].m_obj;
lean_object* v___y_693_ = stack[6].m_obj;
lean_object* v___y_694_ = stack[7].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_687_, v_k_688_, v_cleanupAnnotations_689_, v_whnfType_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(lean_object* v_type_715_, lean_object* v_k_716_, lean_object* v_cleanupAnnotations_717_, lean_object* v_whnfType_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_724_; uint8_t v_whnfType_boxed_725_; lean_object* v_res_726_; 
v_cleanupAnnotations_boxed_724_ = lean_unbox(v_cleanupAnnotations_717_);
v_whnfType_boxed_725_ = lean_unbox(v_whnfType_718_);
v_res_726_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_715_, v_k_716_, v_cleanupAnnotations_boxed_724_, v_whnfType_boxed_725_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_726_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_object* v_00_u03b1_727_, lean_object* v_type_728_, lean_object* v_k_729_, uint8_t v_cleanupAnnotations_730_, uint8_t v_whnfType_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_728_, v_k_729_, v_cleanupAnnotations_730_, v_whnfType_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_728_ = stack[1].m_obj;
lean_object* v_k_729_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_730_ = stack[3].m_num;
uint8_t v_whnfType_731_ = stack[4].m_num;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v___y_733_ = stack[6].m_obj;
lean_object* v___y_734_ = stack[7].m_obj;
lean_object* v___y_735_ = stack[8].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_box(0), v_type_728_, v_k_729_, v_cleanupAnnotations_730_, v_whnfType_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(lean_object* v_00_u03b1_739_, lean_object* v_type_740_, lean_object* v_k_741_, lean_object* v_cleanupAnnotations_742_, lean_object* v_whnfType_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_749_; uint8_t v_whnfType_boxed_750_; lean_object* v_res_751_; 
v_cleanupAnnotations_boxed_749_ = lean_unbox(v_cleanupAnnotations_742_);
v_whnfType_boxed_750_ = lean_unbox(v_whnfType_743_);
v_res_751_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(v_00_u03b1_739_, v_type_740_, v_k_741_, v_cleanupAnnotations_boxed_749_, v_whnfType_boxed_750_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_751_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(lean_object* v_msgData_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; lean_object* v_env_759_; uint8_t v___x_760_; lean_object* v_env_761_; lean_object* v___x_762_; lean_object* v_toCold_763_; lean_object* v_mctx_764_; lean_object* v_lctx_765_; lean_object* v_options_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_758_ = lean_st_ref_get(v___y_756_);
v_env_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_env_759_);
lean_dec(v___x_758_);
v___x_760_ = 0;
v_env_761_ = l_Lean_Environment_setRecordingDeps(v_env_759_, v___x_760_);
v___x_762_ = lean_st_ref_get(v___y_754_);
v_toCold_763_ = lean_ctor_get(v___y_755_, 0);
v_mctx_764_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_mctx_764_);
lean_dec(v___x_762_);
v_lctx_765_ = lean_ctor_get(v___y_753_, 2);
v_options_766_ = lean_ctor_get(v_toCold_763_, 2);
lean_inc_ref(v_options_766_);
lean_inc_ref(v_lctx_765_);
v___x_767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_767_, 0, v_env_761_);
lean_ctor_set(v___x_767_, 1, v_mctx_764_);
lean_ctor_set(v___x_767_, 2, v_lctx_765_);
lean_ctor_set(v___x_767_, 3, v_options_766_);
v___x_768_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v_msgData_752_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_752_ = stack[0].m_obj;
lean_object* v___y_753_ = stack[1].m_obj;
lean_object* v___y_754_ = stack[2].m_obj;
lean_object* v___y_755_ = stack[3].m_obj;
lean_object* v___y_756_ = stack[4].m_obj;
lean_object* v_res_770_;
v_res_770_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(lean_object* v_msgData_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_777_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_778_; double v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_float_of_nat(v___x_778_);
return v___x_779_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(lean_object* v_cls_782_, lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_ref_789_; lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_836_; 
v_ref_789_ = lean_ctor_get(v___y_786_, 2);
v___x_790_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_836_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_836_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_836_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v_traceState_796_; lean_object* v_env_797_; lean_object* v_nextMacroScope_798_; lean_object* v_ngen_799_; lean_object* v_auxDeclNGen_800_; lean_object* v_cache_801_; lean_object* v_recordedDeps_802_; lean_object* v_messages_803_; lean_object* v_infoState_804_; lean_object* v_snapshotTasks_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_835_; 
v___x_795_ = lean_st_ref_take(v___y_787_);
v_traceState_796_ = lean_ctor_get(v___x_795_, 4);
v_env_797_ = lean_ctor_get(v___x_795_, 0);
v_nextMacroScope_798_ = lean_ctor_get(v___x_795_, 1);
v_ngen_799_ = lean_ctor_get(v___x_795_, 2);
v_auxDeclNGen_800_ = lean_ctor_get(v___x_795_, 3);
v_cache_801_ = lean_ctor_get(v___x_795_, 5);
v_recordedDeps_802_ = lean_ctor_get(v___x_795_, 6);
v_messages_803_ = lean_ctor_get(v___x_795_, 7);
v_infoState_804_ = lean_ctor_get(v___x_795_, 8);
v_snapshotTasks_805_ = lean_ctor_get(v___x_795_, 9);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_835_ == 0)
{
v___x_807_ = v___x_795_;
v_isShared_808_ = v_isSharedCheck_835_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snapshotTasks_805_);
lean_inc(v_infoState_804_);
lean_inc(v_messages_803_);
lean_inc(v_recordedDeps_802_);
lean_inc(v_cache_801_);
lean_inc(v_traceState_796_);
lean_inc(v_auxDeclNGen_800_);
lean_inc(v_ngen_799_);
lean_inc(v_nextMacroScope_798_);
lean_inc(v_env_797_);
lean_dec(v___x_795_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_835_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint64_t v_tid_809_; lean_object* v_traces_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_834_; 
v_tid_809_ = lean_ctor_get_uint64(v_traceState_796_, sizeof(void*)*1);
v_traces_810_ = lean_ctor_get(v_traceState_796_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_traceState_796_);
if (v_isSharedCheck_834_ == 0)
{
v___x_812_ = v_traceState_796_;
v_isShared_813_ = v_isSharedCheck_834_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_traces_810_);
lean_dec(v_traceState_796_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_834_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; double v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_box(0);
v___x_816_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
v___x_817_ = 0;
v___x_818_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v___x_819_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_819_, 0, v_cls_782_);
lean_ctor_set(v___x_819_, 1, v___x_815_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
lean_ctor_set_float(v___x_819_, sizeof(void*)*3, v___x_816_);
lean_ctor_set_float(v___x_819_, sizeof(void*)*3 + 8, v___x_816_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 16, v___x_817_);
v___x_820_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1));
v___x_821_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v_a_791_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
lean_inc(v_ref_789_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_ref_789_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_PersistentArray_push___redArg(v_traces_810_, v___x_822_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_823_);
v___x_825_ = v___x_812_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_823_);
lean_ctor_set_uint64(v_reuseFailAlloc_833_, sizeof(void*)*1, v_tid_809_);
v___x_825_ = v_reuseFailAlloc_833_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v___x_825_);
v___x_827_ = v___x_807_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_env_797_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_nextMacroScope_798_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_ngen_799_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_auxDeclNGen_800_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v_cache_801_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_recordedDeps_802_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_messages_803_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_infoState_804_);
lean_ctor_set(v_reuseFailAlloc_832_, 9, v_snapshotTasks_805_);
v___x_827_ = v_reuseFailAlloc_832_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_st_ref_put(v___y_787_, v___x_827_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_814_);
v___x_830_ = v___x_793_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_814_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_782_ = stack[0].m_obj;
lean_object* v_msg_783_ = stack[1].m_obj;
lean_object* v___y_784_ = stack[2].m_obj;
lean_object* v___y_785_ = stack[3].m_obj;
lean_object* v___y_786_ = stack[4].m_obj;
lean_object* v___y_787_ = stack[5].m_obj;
lean_object* v_res_837_;
v_res_837_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_782_, v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(lean_object* v_cls_838_, lean_object* v_msg_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_838_, v_msg_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_845_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(lean_object* v_opts_846_, lean_object* v_opt_847_){
_start:
{
lean_object* v_name_848_; lean_object* v_defValue_849_; lean_object* v_map_850_; lean_object* v___x_851_; 
v_name_848_ = lean_ctor_get(v_opt_847_, 0);
v_defValue_849_ = lean_ctor_get(v_opt_847_, 1);
v_map_850_ = lean_ctor_get(v_opts_846_, 0);
v___x_851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_850_, v_name_848_);
if (lean_obj_tag(v___x_851_) == 0)
{
uint8_t v___x_852_; 
v___x_852_ = lean_unbox(v_defValue_849_);
return v___x_852_;
}
else
{
lean_object* v_val_853_; 
v_val_853_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v___x_851_, 1);
if (lean_obj_tag(v_val_853_) == 1)
{
uint8_t v_v_854_; 
v_v_854_ = lean_ctor_get_uint8(v_val_853_, 0);
lean_dec_ref_known(v_val_853_, 0);
return v_v_854_;
}
else
{
uint8_t v___x_855_; 
lean_dec(v_val_853_);
v___x_855_ = lean_unbox(v_defValue_849_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_846_ = stack[0].m_obj;
lean_object* v_opt_847_ = stack[1].m_obj;
uint8_t v_res_856_;
v_res_856_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_846_, v_opt_847_);
stack->m_num = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_opts_857_, lean_object* v_opt_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_857_, v_opt_858_);
lean_dec_ref(v_opt_858_);
lean_dec_ref(v_opts_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_869_, uint8_t v___y_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 1)
{
lean_object* v_pre_872_; 
v_pre_872_ = lean_ctor_get(v_x_871_, 0);
switch(lean_obj_tag(v_pre_872_))
{
case 1:
{
lean_object* v_pre_873_; 
v_pre_873_ = lean_ctor_get(v_pre_872_, 0);
switch(lean_obj_tag(v_pre_873_))
{
case 0:
{
lean_object* v_str_874_; lean_object* v_str_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_str_874_ = lean_ctor_get(v_x_871_, 1);
v_str_875_ = lean_ctor_get(v_pre_872_, 1);
v___x_876_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_877_ = lean_string_dec_eq(v_str_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_879_ = lean_string_dec_eq(v_str_875_, v___x_878_);
if (v___x_879_ == 0)
{
return v___x_879_;
}
else
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_881_ = lean_string_dec_eq(v_str_874_, v___x_880_);
if (v___x_881_ == 0)
{
return v___x_881_;
}
else
{
return v_suppressElabErrors_869_;
}
}
}
else
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_883_ = lean_string_dec_eq(v_str_874_, v___x_882_);
if (v___x_883_ == 0)
{
return v___x_883_;
}
else
{
return v_suppressElabErrors_869_;
}
}
}
case 1:
{
lean_object* v_pre_884_; 
v_pre_884_ = lean_ctor_get(v_pre_873_, 0);
if (lean_obj_tag(v_pre_884_) == 0)
{
lean_object* v_str_885_; lean_object* v_str_886_; lean_object* v_str_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_str_885_ = lean_ctor_get(v_x_871_, 1);
v_str_886_ = lean_ctor_get(v_pre_872_, 1);
v_str_887_ = lean_ctor_get(v_pre_873_, 1);
v___x_888_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_889_ = lean_string_dec_eq(v_str_887_, v___x_888_);
if (v___x_889_ == 0)
{
return v___x_889_;
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_891_ = lean_string_dec_eq(v_str_886_, v___x_890_);
if (v___x_891_ == 0)
{
return v___x_891_;
}
else
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_893_ = lean_string_dec_eq(v_str_885_, v___x_892_);
if (v___x_893_ == 0)
{
return v___x_893_;
}
else
{
return v_suppressElabErrors_869_;
}
}
}
}
else
{
return v___y_870_;
}
}
default: 
{
return v___y_870_;
}
}
}
case 0:
{
lean_object* v_str_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_str_894_ = lean_ctor_get(v_x_871_, 1);
v___x_895_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_896_ = lean_string_dec_eq(v_str_894_, v___x_895_);
if (v___x_896_ == 0)
{
return v___x_896_;
}
else
{
return v_suppressElabErrors_869_;
}
}
default: 
{
return v___y_870_;
}
}
}
else
{
return v___y_870_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_869_ = stack[0].m_num;
uint8_t v___y_870_ = stack[1].m_num;
lean_object* v_x_871_ = stack[2].m_obj;
uint8_t v_res_897_;
v_res_897_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_869_, v___y_870_, v_x_871_);
stack->m_num = v_res_897_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_898_, lean_object* v___y_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_suppressElabErrors_boxed_901_; uint8_t v___y_21816__boxed_902_; uint8_t v_res_903_; lean_object* v_r_904_; 
v_suppressElabErrors_boxed_901_ = lean_unbox(v_suppressElabErrors_898_);
v___y_21816__boxed_902_ = lean_unbox(v___y_899_);
v_res_903_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_901_, v___y_21816__boxed_902_, v_x_900_);
lean_dec(v_x_900_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_905_, lean_object* v_msgData_906_, uint8_t v_severity_907_, uint8_t v_isSilent_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; uint8_t v___y_920_; uint8_t v___y_921_; lean_object* v_toCold_922_; lean_object* v___y_923_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_956_; uint8_t v___y_957_; uint8_t v___y_958_; lean_object* v___y_959_; lean_object* v___y_979_; lean_object* v___y_980_; uint8_t v___y_981_; uint8_t v___y_982_; lean_object* v___y_983_; uint8_t v___y_984_; lean_object* v___y_985_; uint8_t v___y_989_; uint8_t v___y_990_; uint8_t v___y_991_; uint8_t v___x_1002_; uint8_t v___y_1004_; uint8_t v___y_1005_; uint8_t v___y_1006_; uint8_t v___y_1008_; uint8_t v___x_1016_; 
v___x_1002_ = 2;
v___x_1016_ = l_Lean_instBEqMessageSeverity_beq(v_severity_907_, v___x_1002_);
if (v___x_1016_ == 0)
{
v___y_1008_ = v___x_1016_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1017_; 
lean_inc_ref(v_msgData_906_);
v___x_1017_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_906_);
v___y_1008_ = v___x_1017_;
goto v___jp_1007_;
}
v___jp_914_:
{
lean_object* v_currNamespace_924_; lean_object* v_openDecls_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_env_930_; lean_object* v_nextMacroScope_931_; lean_object* v_ngen_932_; lean_object* v_auxDeclNGen_933_; lean_object* v_traceState_934_; lean_object* v_cache_935_; lean_object* v_recordedDeps_936_; lean_object* v_messages_937_; lean_object* v_infoState_938_; lean_object* v_snapshotTasks_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_950_; 
v_currNamespace_924_ = lean_ctor_get(v_toCold_922_, 4);
v_openDecls_925_ = lean_ctor_get(v_toCold_922_, 5);
lean_inc(v_openDecls_925_);
lean_inc(v_currNamespace_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_currNamespace_924_);
lean_ctor_set(v___x_926_, 1, v_openDecls_925_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___y_919_);
lean_inc_ref(v___y_917_);
lean_inc_ref(v___y_915_);
v___x_928_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_928_, 0, v___y_915_);
lean_ctor_set(v___x_928_, 1, v___y_916_);
lean_ctor_set(v___x_928_, 2, v___y_918_);
lean_ctor_set(v___x_928_, 3, v___y_917_);
lean_ctor_set(v___x_928_, 4, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*5, v___y_920_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*5 + 1, v___y_921_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*5 + 2, v_isSilent_908_);
v___x_929_ = lean_st_ref_take(v___y_923_);
v_env_930_ = lean_ctor_get(v___x_929_, 0);
v_nextMacroScope_931_ = lean_ctor_get(v___x_929_, 1);
v_ngen_932_ = lean_ctor_get(v___x_929_, 2);
v_auxDeclNGen_933_ = lean_ctor_get(v___x_929_, 3);
v_traceState_934_ = lean_ctor_get(v___x_929_, 4);
v_cache_935_ = lean_ctor_get(v___x_929_, 5);
v_recordedDeps_936_ = lean_ctor_get(v___x_929_, 6);
v_messages_937_ = lean_ctor_get(v___x_929_, 7);
v_infoState_938_ = lean_ctor_get(v___x_929_, 8);
v_snapshotTasks_939_ = lean_ctor_get(v___x_929_, 9);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_950_ == 0)
{
v___x_941_ = v___x_929_;
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snapshotTasks_939_);
lean_inc(v_infoState_938_);
lean_inc(v_messages_937_);
lean_inc(v_recordedDeps_936_);
lean_inc(v_cache_935_);
lean_inc(v_traceState_934_);
lean_inc(v_auxDeclNGen_933_);
lean_inc(v_ngen_932_);
lean_inc(v_nextMacroScope_931_);
lean_inc(v_env_930_);
lean_dec(v___x_929_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = lean_box(0);
v___x_944_ = l_Lean_MessageLog_add(v___x_928_, v_messages_937_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 7, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_env_930_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_nextMacroScope_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_ngen_932_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_auxDeclNGen_933_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_traceState_934_);
lean_ctor_set(v_reuseFailAlloc_949_, 5, v_cache_935_);
lean_ctor_set(v_reuseFailAlloc_949_, 6, v_recordedDeps_936_);
lean_ctor_set(v_reuseFailAlloc_949_, 7, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 8, v_infoState_938_);
lean_ctor_set(v_reuseFailAlloc_949_, 9, v_snapshotTasks_939_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_st_ref_put(v___y_923_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_943_);
return v___x_948_;
}
}
}
v___jp_951_:
{
lean_object* v_fileName_960_; lean_object* v_fileMap_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_977_; 
v_fileName_960_ = lean_ctor_get(v___y_954_, 0);
v_fileMap_961_ = lean_ctor_get(v___y_954_, 1);
v___x_962_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_906_);
v___x_963_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_962_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_977_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_977_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_977_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc_ref_n(v_fileMap_961_, 2);
v___x_968_ = l_Lean_FileMap_toPosition(v_fileMap_961_, v___y_955_);
lean_dec(v___y_955_);
v___x_969_ = l_Lean_FileMap_toPosition(v_fileMap_961_, v___y_959_);
lean_dec(v___y_959_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
if (v___y_957_ == 0)
{
lean_del_object(v___x_966_);
lean_dec_ref(v___y_953_);
v___y_915_ = v_fileName_960_;
v___y_916_ = v___x_968_;
v___y_917_ = v___x_971_;
v___y_918_ = v___x_970_;
v___y_919_ = v_a_964_;
v___y_920_ = v___y_956_;
v___y_921_ = v___y_958_;
v_toCold_922_ = v___y_952_;
v___y_923_ = v___y_912_;
goto v___jp_914_;
}
else
{
uint8_t v___x_972_; 
lean_inc(v_a_964_);
v___x_972_ = l_Lean_MessageData_hasTag(v___y_953_, v_a_964_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec_ref_known(v___x_970_, 1);
lean_dec_ref(v___x_968_);
lean_dec(v_a_964_);
v___x_973_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_973_);
v___x_975_ = v___x_966_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_del_object(v___x_966_);
v___y_915_ = v_fileName_960_;
v___y_916_ = v___x_968_;
v___y_917_ = v___x_971_;
v___y_918_ = v___x_970_;
v___y_919_ = v_a_964_;
v___y_920_ = v___y_956_;
v___y_921_ = v___y_958_;
v_toCold_922_ = v___y_952_;
v___y_923_ = v___y_912_;
goto v___jp_914_;
}
}
}
}
v___jp_978_:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Syntax_getTailPos_x3f(v___y_983_, v___y_982_);
lean_dec(v___y_983_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_inc(v___y_985_);
v___y_952_ = v___y_979_;
v___y_953_ = v___y_980_;
v___y_954_ = v___y_979_;
v___y_955_ = v___y_985_;
v___y_956_ = v___y_982_;
v___y_957_ = v___y_981_;
v___y_958_ = v___y_984_;
v___y_959_ = v___y_985_;
goto v___jp_951_;
}
else
{
lean_object* v_val_987_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_986_, 1);
v___y_952_ = v___y_979_;
v___y_953_ = v___y_980_;
v___y_954_ = v___y_979_;
v___y_955_ = v___y_985_;
v___y_956_ = v___y_982_;
v___y_957_ = v___y_981_;
v___y_958_ = v___y_984_;
v___y_959_ = v_val_987_;
goto v___jp_951_;
}
}
v___jp_988_:
{
lean_object* v_toCold_992_; lean_object* v_ref_993_; uint8_t v_suppressElabErrors_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v_ref_998_; lean_object* v___x_999_; 
v_toCold_992_ = lean_ctor_get(v___y_911_, 0);
v_ref_993_ = lean_ctor_get(v___y_911_, 2);
v_suppressElabErrors_994_ = lean_ctor_get_uint8(v___y_911_, sizeof(void*)*3 + 2);
v___x_995_ = lean_box(v_suppressElabErrors_994_);
v___x_996_ = lean_box(v___y_989_);
v___f_997_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_997_, 0, v___x_995_);
lean_closure_set(v___f_997_, 1, v___x_996_);
v_ref_998_ = l_Lean_replaceRef(v_ref_905_, v_ref_993_);
v___x_999_ = l_Lean_Syntax_getPos_x3f(v_ref_998_, v___y_990_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___y_979_ = v_toCold_992_;
v___y_980_ = v___f_997_;
v___y_981_ = v_suppressElabErrors_994_;
v___y_982_ = v___y_990_;
v___y_983_ = v_ref_998_;
v___y_984_ = v___y_991_;
v___y_985_ = v___x_1000_;
goto v___jp_978_;
}
else
{
lean_object* v_val_1001_; 
v_val_1001_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_999_, 1);
v___y_979_ = v_toCold_992_;
v___y_980_ = v___f_997_;
v___y_981_ = v_suppressElabErrors_994_;
v___y_982_ = v___y_990_;
v___y_983_ = v_ref_998_;
v___y_984_ = v___y_991_;
v___y_985_ = v_val_1001_;
goto v___jp_978_;
}
}
v___jp_1003_:
{
if (v___y_1006_ == 0)
{
v___y_989_ = v___y_1004_;
v___y_990_ = v___y_1005_;
v___y_991_ = v_severity_907_;
goto v___jp_988_;
}
else
{
v___y_989_ = v___y_1004_;
v___y_990_ = v___y_1005_;
v___y_991_ = v___x_1002_;
goto v___jp_988_;
}
}
v___jp_1007_:
{
if (v___y_1008_ == 0)
{
uint8_t v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = 1;
v___x_1010_ = l_Lean_instBEqMessageSeverity_beq(v_severity_907_, v___x_1009_);
if (v___x_1010_ == 0)
{
v___y_1004_ = v___y_1008_;
v___y_1005_ = v___y_1008_;
v___y_1006_ = v___x_1010_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_911_);
v___x_1012_ = l_Lean_warningAsError;
v___x_1013_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v___x_1011_, v___x_1012_);
lean_dec_ref(v___x_1011_);
v___y_1004_ = v___y_1008_;
v___y_1005_ = v___y_1008_;
v___y_1006_ = v___x_1013_;
goto v___jp_1003_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v_msgData_906_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_905_ = stack[0].m_obj;
lean_object* v_msgData_906_ = stack[1].m_obj;
uint8_t v_severity_907_ = stack[2].m_num;
uint8_t v_isSilent_908_ = stack[3].m_num;
lean_object* v___y_909_ = stack[4].m_obj;
lean_object* v___y_910_ = stack[5].m_obj;
lean_object* v___y_911_ = stack[6].m_obj;
lean_object* v___y_912_ = stack[7].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_905_, v_msgData_906_, v_severity_907_, v_isSilent_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1019_, lean_object* v_msgData_1020_, lean_object* v_severity_1021_, lean_object* v_isSilent_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
uint8_t v_severity_boxed_1028_; uint8_t v_isSilent_boxed_1029_; lean_object* v_res_1030_; 
v_severity_boxed_1028_ = lean_unbox(v_severity_1021_);
v_isSilent_boxed_1029_ = lean_unbox(v_isSilent_1022_);
v_res_1030_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1019_, v_msgData_1020_, v_severity_boxed_1028_, v_isSilent_boxed_1029_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v_ref_1019_);
return v_res_1030_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(lean_object* v_ref_1031_, lean_object* v_msgData_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = 1;
v___x_1042_ = 0;
v___x_1043_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1031_, v_msgData_1032_, v___x_1041_, v___x_1042_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1043_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1031_ = stack[0].m_obj;
lean_object* v_msgData_1032_ = stack[1].m_obj;
lean_object* v___y_1033_ = stack[2].m_obj;
lean_object* v___y_1034_ = stack[3].m_obj;
lean_object* v___y_1035_ = stack[4].m_obj;
lean_object* v___y_1036_ = stack[5].m_obj;
lean_object* v___y_1037_ = stack[6].m_obj;
lean_object* v___y_1038_ = stack[7].m_obj;
lean_object* v___y_1039_ = stack[8].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_1031_, v_msgData_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(lean_object* v_ref_1045_, lean_object* v_msgData_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_1045_, v_msgData_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec(v_ref_1045_);
return v_res_1055_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(lean_object* v_linterOption_1062_, lean_object* v_stx_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_name_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1091_; 
v_name_1073_ = lean_ctor_get(v_linterOption_1062_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_linterOption_1062_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_linterOption_1062_, 1);
lean_dec(v_unused_1092_);
v___x_1075_ = v_linterOption_1062_;
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_name_1073_);
lean_dec(v_linterOption_1062_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
lean_inc(v_name_1073_);
v___x_1078_ = l_Lean_MessageData_ofName(v_name_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 7);
lean_ctor_set(v___x_1075_, 1, v___x_1078_);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_disable_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1081_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v_disable_1083_ = l_Lean_MessageData_note(v___x_1082_);
v___x_1084_ = l_Lean_Linter_linterMessageTag;
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_msg_1064_);
lean_ctor_set(v___x_1085_, 1, v_disable_1083_);
v___x_1086_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_name_1073_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
lean_inc(v_stx_1063_);
v___x_1088_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_stx_1063_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_1063_, v___x_1088_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v_stx_1063_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_1062_ = stack[0].m_obj;
lean_object* v_stx_1063_ = stack[1].m_obj;
lean_object* v_msg_1064_ = stack[2].m_obj;
lean_object* v___y_1065_ = stack[3].m_obj;
lean_object* v___y_1066_ = stack[4].m_obj;
lean_object* v___y_1067_ = stack[5].m_obj;
lean_object* v___y_1068_ = stack[6].m_obj;
lean_object* v___y_1069_ = stack[7].m_obj;
lean_object* v___y_1070_ = stack[8].m_obj;
lean_object* v___y_1071_ = stack[9].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v_linterOption_1062_, v_stx_1063_, v_msg_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(lean_object* v_linterOption_1094_, lean_object* v_stx_1095_, lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v_linterOption_1094_, v_stx_1095_, v_msg_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
return v_res_1105_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(lean_object* v_msgData_1106_, uint8_t v_severity_1107_, uint8_t v_isSilent_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; 
v_ref_1117_ = lean_ctor_get(v___y_1114_, 2);
v___x_1118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1117_, v_msgData_1106_, v_severity_1107_, v_isSilent_1108_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1106_ = stack[0].m_obj;
uint8_t v_severity_1107_ = stack[1].m_num;
uint8_t v_isSilent_1108_ = stack[2].m_num;
lean_object* v___y_1109_ = stack[3].m_obj;
lean_object* v___y_1110_ = stack[4].m_obj;
lean_object* v___y_1111_ = stack[5].m_obj;
lean_object* v___y_1112_ = stack[6].m_obj;
lean_object* v___y_1113_ = stack[7].m_obj;
lean_object* v___y_1114_ = stack[8].m_obj;
lean_object* v___y_1115_ = stack[9].m_obj;
lean_object* v_res_1119_;
v_res_1119_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1106_, v_severity_1107_, v_isSilent_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
stack->m_obj
 = v_res_1119_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(lean_object* v_msgData_1120_, lean_object* v_severity_1121_, lean_object* v_isSilent_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_severity_boxed_1131_; uint8_t v_isSilent_boxed_1132_; lean_object* v_res_1133_; 
v_severity_boxed_1131_ = lean_unbox(v_severity_1121_);
v_isSilent_boxed_1132_ = lean_unbox(v_isSilent_1122_);
v_res_1133_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1120_, v_severity_boxed_1131_, v_isSilent_boxed_1132_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
return v_res_1133_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(lean_object* v_msgData_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
uint8_t v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = 1;
v___x_1144_ = 0;
v___x_1145_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1134_, v___x_1143_, v___x_1144_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1145_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1134_ = stack[0].m_obj;
lean_object* v___y_1135_ = stack[1].m_obj;
lean_object* v___y_1136_ = stack[2].m_obj;
lean_object* v___y_1137_ = stack[3].m_obj;
lean_object* v___y_1138_ = stack[4].m_obj;
lean_object* v___y_1139_ = stack[5].m_obj;
lean_object* v___y_1140_ = stack[6].m_obj;
lean_object* v___y_1141_ = stack[7].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_msgData_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(lean_object* v_msgData_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_msgData_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
return v_res_1156_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1167_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3));
v___x_1168_ = l_Lean_Name_append(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(uint8_t v_force_1175_, lean_object* v_thm_1176_, lean_object* v___x_1177_, lean_object* v_origin_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1212_; 
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
v___x_1212_ = lean_simp(v___x_1177_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v___y_1179_);
lean_dec_ref(v_origin_1178_);
lean_dec_ref(v_thm_1176_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1221_);
v___x_1214_ = v___x_1212_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_dec(v___x_1212_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1247_; 
v_a_1222_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1224_ = v___x_1212_;
v_isShared_1225_ = v_isSharedCheck_1247_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1212_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1247_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Lean_Exception_isInterrupt(v_a_1222_);
if (v___x_1226_ == 0)
{
lean_object* v_toCold_1227_; lean_object* v_options_1228_; uint8_t v_hasTrace_1229_; 
lean_del_object(v___x_1224_);
v_toCold_1227_ = lean_ctor_get(v___y_1184_, 0);
v_options_1228_ = lean_ctor_get(v_toCold_1227_, 2);
v_hasTrace_1229_ = lean_ctor_get_uint8(v_options_1228_, sizeof(void*)*1);
if (v_hasTrace_1229_ == 0)
{
lean_dec(v_a_1222_);
lean_dec_ref(v_origin_1178_);
goto v___jp_1187_;
}
else
{
lean_object* v_inheritedTraceOptions_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_inheritedTraceOptions_1230_ = lean_ctor_get(v_toCold_1227_, 11);
v___x_1231_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1232_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4);
v___x_1233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1230_, v_options_1228_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_a_1222_);
lean_dec_ref(v_origin_1178_);
goto v___jp_1187_;
}
else
{
lean_object* v___x_1234_; lean_object* v_a_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1234_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_1178_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_a_1235_);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__8, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = l_Lean_Exception_toMessageData(v_a_1222_);
v___x_1241_ = l_Lean_indentD(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1239_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v___x_1231_, v___x_1242_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_dec_ref_known(v___x_1243_, 1);
goto v___jp_1187_;
}
else
{
lean_dec(v___y_1179_);
lean_dec_ref(v_thm_1176_);
return v___x_1243_;
}
}
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v___y_1179_);
lean_dec_ref(v_origin_1178_);
lean_dec_ref(v_thm_1176_);
if (v_isShared_1225_ == 0)
{
v___x_1245_ = v___x_1224_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1222_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
v___jp_1187_:
{
if (v_force_1175_ == 0)
{
lean_object* v_ref_1188_; lean_object* v___x_1189_; 
v_ref_1188_ = lean_ctor_get(v___y_1184_, 2);
v___x_1189_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1176_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
lean_inc(v_ref_1188_);
v___x_1192_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v___x_1191_, v_ref_1188_, v_a_1190_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1179_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v___y_1179_);
v_a_1193_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1189_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1189_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1176_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1203_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1201_, 1);
v___x_1203_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_a_1202_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1179_);
return v___x_1203_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v___y_1179_);
v_a_1204_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1201_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1201_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_checkLoops___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_force_1175_ = stack[0].m_num;
lean_object* v_thm_1176_ = stack[1].m_obj;
lean_object* v___x_1177_ = stack[2].m_obj;
lean_object* v_origin_1178_ = stack[3].m_obj;
lean_object* v___y_1179_ = stack[4].m_obj;
lean_object* v___y_1180_ = stack[5].m_obj;
lean_object* v___y_1181_ = stack[6].m_obj;
lean_object* v___y_1182_ = stack[7].m_obj;
lean_object* v___y_1183_ = stack[8].m_obj;
lean_object* v___y_1184_ = stack[9].m_obj;
lean_object* v___y_1185_ = stack[10].m_obj;
lean_object* v_res_1248_;
v_res_1248_ = l_Lean_Meta_Simp_checkLoops___lam__0(v_force_1175_, v_thm_1176_, v___x_1177_, v_origin_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
stack->m_obj
 = v_res_1248_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___boxed(lean_object* v_force_1249_, lean_object* v_thm_1250_, lean_object* v___x_1251_, lean_object* v_origin_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v_force_boxed_1261_; lean_object* v_res_1262_; 
v_force_boxed_1261_ = lean_unbox(v_force_1249_);
v_res_1262_ = l_Lean_Meta_Simp_checkLoops___lam__0(v_force_boxed_1261_, v_thm_1250_, v___x_1251_, v_origin_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1262_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_unsigned_to_nat(16u);
v___x_1265_ = lean_mk_array(v___x_1264_, v___x_1263_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__0, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___x_1266_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1271_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_unsigned_to_nat(32u);
v___x_1275_ = lean_mk_empty_array_with_capacity(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5(void){
_start:
{
size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((size_t)5ULL);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_unsigned_to_nat(32u);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1279_);
v___x_1281_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4);
v___x_1282_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1280_);
lean_ctor_set(v___x_1282_, 2, v___x_1278_);
lean_ctor_set(v___x_1282_, 3, v___x_1278_);
lean_ctor_set_usize(v___x_1282_, 4, v___x_1277_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__5, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5);
v___x_1284_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
lean_ctor_set(v___x_1285_, 2, v___x_1284_);
lean_ctor_set(v___x_1285_, 3, v___x_1283_);
return v___x_1285_;
}
}
lean_object* l_Lean_Meta_Simp_checkLoops___lam__1(uint8_t v_force_1286_, lean_object* v_thm_1287_, lean_object* v_origin_1288_, uint8_t v_a_1289_, lean_object* v_ctxt_1290_, lean_object* v_methods_1291_, lean_object* v___xs_1292_, lean_object* v_type_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___x_1299_ = lean_whnf(v_type_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = l_Lean_Expr_appArg_x21(v_a_1300_);
lean_dec(v_a_1300_);
v___x_1302_ = lean_box(v_force_1286_);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1303_, 0, v___x_1302_);
lean_closure_set(v___f_1303_, 1, v_thm_1287_);
lean_closure_set(v___f_1303_, 2, v___x_1301_);
lean_closure_set(v___f_1303_, 3, v_origin_1288_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__1, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1);
v___x_1306_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1307_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*2, v_a_1289_);
v___x_1308_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1309_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6);
v___x_1310_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1307_);
lean_ctor_set(v___x_1310_, 1, v___x_1305_);
lean_ctor_set(v___x_1310_, 2, v___x_1305_);
lean_ctor_set(v___x_1310_, 3, v___x_1308_);
lean_ctor_set(v___x_1310_, 4, v___x_1304_);
lean_ctor_set(v___x_1310_, 5, v___x_1309_);
v___x_1311_ = l_Lean_Meta_Simp_SimpM_run___redArg(v_ctxt_1290_, v___x_1310_, v_methods_1291_, v___f_1303_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1320_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = lean_box(0);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_methods_1291_);
lean_dec_ref(v_ctxt_1290_);
lean_dec_ref(v_origin_1288_);
lean_dec_ref(v_thm_1287_);
v_a_1329_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1299_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1299_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_checkLoops___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_force_1286_ = stack[0].m_num;
lean_object* v_thm_1287_ = stack[1].m_obj;
lean_object* v_origin_1288_ = stack[2].m_obj;
uint8_t v_a_1289_ = stack[3].m_num;
lean_object* v_ctxt_1290_ = stack[4].m_obj;
lean_object* v_methods_1291_ = stack[5].m_obj;
lean_object* v___xs_1292_ = stack[6].m_obj;
lean_object* v_type_1293_ = stack[7].m_obj;
lean_object* v___y_1294_ = stack[8].m_obj;
lean_object* v___y_1295_ = stack[9].m_obj;
lean_object* v___y_1296_ = stack[10].m_obj;
lean_object* v___y_1297_ = stack[11].m_obj;
lean_object* v_res_1337_;
v_res_1337_ = l_Lean_Meta_Simp_checkLoops___lam__1(v_force_1286_, v_thm_1287_, v_origin_1288_, v_a_1289_, v_ctxt_1290_, v_methods_1291_, v___xs_1292_, v_type_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
stack->m_obj
 = v_res_1337_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___boxed(lean_object* v_force_1338_, lean_object* v_thm_1339_, lean_object* v_origin_1340_, lean_object* v_a_1341_, lean_object* v_ctxt_1342_, lean_object* v_methods_1343_, lean_object* v___xs_1344_, lean_object* v_type_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_force_boxed_1351_; uint8_t v_a_22810__boxed_1352_; lean_object* v_res_1353_; 
v_force_boxed_1351_ = lean_unbox(v_force_1338_);
v_a_22810__boxed_1352_ = lean_unbox(v_a_1341_);
v_res_1353_ = l_Lean_Meta_Simp_checkLoops___lam__1(v_force_boxed_1351_, v_thm_1339_, v_origin_1340_, v_a_22810__boxed_1352_, v_ctxt_1342_, v_methods_1343_, v___xs_1344_, v_type_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___xs_1344_);
return v_res_1353_;
}
}
lean_object* l_Lean_Meta_Simp_checkLoops(uint8_t v_force_1354_, lean_object* v_ctxt_1355_, lean_object* v_methods_1356_, lean_object* v_thm_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_1354_, v_ctxt_1355_, v_a_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1403_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1403_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1403_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_unbox(v_a_1364_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec(v_a_1364_);
lean_dec_ref(v_thm_1357_);
lean_dec_ref(v_methods_1356_);
lean_dec_ref(v_ctxt_1355_);
v___x_1369_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1369_);
v___x_1371_ = v___x_1366_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v_proof_1373_; lean_object* v_origin_1374_; uint8_t v___x_1375_; 
v_proof_1373_ = lean_ctor_get(v_thm_1357_, 2);
v_origin_1374_ = lean_ctor_get(v_thm_1357_, 4);
v___x_1375_ = l_Lean_Expr_hasFVar(v_proof_1373_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; 
lean_del_object(v___x_1366_);
v___x_1376_ = lean_box(v_force_1354_);
lean_inc_ref(v_origin_1374_);
lean_inc_ref(v_thm_1357_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1377_, 0, v___x_1376_);
lean_closure_set(v___f_1377_, 1, v_thm_1357_);
lean_closure_set(v___f_1377_, 2, v_origin_1374_);
lean_closure_set(v___f_1377_, 3, v_a_1364_);
lean_closure_set(v___f_1377_, 4, v_ctxt_1355_);
lean_closure_set(v___f_1377_, 5, v_methods_1356_);
v___x_1378_ = l_Lean_Meta_SimpTheorem_getValue(v_thm_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
lean_inc(v_a_1359_);
lean_inc_ref(v_a_1358_);
v___x_1380_ = lean_infer_type(v_a_1379_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_1381_, v___f_1377_, v___x_1375_, v___x_1375_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
return v___x_1382_;
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___f_1377_);
v_a_1383_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1380_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1380_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v___f_1377_);
v_a_1391_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1378_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1378_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec(v_a_1364_);
lean_dec_ref(v_thm_1357_);
lean_dec_ref(v_methods_1356_);
lean_dec_ref(v_ctxt_1355_);
v___x_1399_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1399_);
v___x_1401_ = v___x_1366_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_thm_1357_);
lean_dec_ref(v_methods_1356_);
lean_dec_ref(v_ctxt_1355_);
v_a_1404_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1363_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1363_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_checkLoops_0interp(lean_interpreter_value* stack)
{
uint8_t v_force_1354_ = stack[0].m_num;
lean_object* v_ctxt_1355_ = stack[1].m_obj;
lean_object* v_methods_1356_ = stack[2].m_obj;
lean_object* v_thm_1357_ = stack[3].m_obj;
lean_object* v_a_1358_ = stack[4].m_obj;
lean_object* v_a_1359_ = stack[5].m_obj;
lean_object* v_a_1360_ = stack[6].m_obj;
lean_object* v_a_1361_ = stack[7].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l_Lean_Meta_Simp_checkLoops(v_force_1354_, v_ctxt_1355_, v_methods_1356_, v_thm_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___boxed(lean_object* v_force_1413_, lean_object* v_ctxt_1414_, lean_object* v_methods_1415_, lean_object* v_thm_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
uint8_t v_force_boxed_1422_; lean_object* v_res_1423_; 
v_force_boxed_1422_ = lean_unbox(v_force_1413_);
v_res_1423_ = l_Lean_Meta_Simp_checkLoops(v_force_boxed_1422_, v_ctxt_1414_, v_methods_1415_, v_thm_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1423_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(lean_object* v_cls_1424_, lean_object* v_msg_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_1424_, v_msg_1425_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1424_ = stack[0].m_obj;
lean_object* v_msg_1425_ = stack[1].m_obj;
lean_object* v___y_1426_ = stack[2].m_obj;
lean_object* v___y_1427_ = stack[3].m_obj;
lean_object* v___y_1428_ = stack[4].m_obj;
lean_object* v___y_1429_ = stack[5].m_obj;
lean_object* v___y_1430_ = stack[6].m_obj;
lean_object* v___y_1431_ = stack[7].m_obj;
lean_object* v___y_1432_ = stack[8].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(v_cls_1424_, v_msg_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(lean_object* v_cls_1436_, lean_object* v_msg_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(v_cls_1436_, v_msg_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1446_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(lean_object* v_ref_1447_, lean_object* v_msgData_1448_, uint8_t v_severity_1449_, uint8_t v_isSilent_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1447_, v_msgData_1448_, v_severity_1449_, v_isSilent_1450_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1447_ = stack[0].m_obj;
lean_object* v_msgData_1448_ = stack[1].m_obj;
uint8_t v_severity_1449_ = stack[2].m_num;
uint8_t v_isSilent_1450_ = stack[3].m_num;
lean_object* v___y_1451_ = stack[4].m_obj;
lean_object* v___y_1452_ = stack[5].m_obj;
lean_object* v___y_1453_ = stack[6].m_obj;
lean_object* v___y_1454_ = stack[7].m_obj;
lean_object* v___y_1455_ = stack[8].m_obj;
lean_object* v___y_1456_ = stack[9].m_obj;
lean_object* v___y_1457_ = stack[10].m_obj;
lean_object* v_res_1460_;
v_res_1460_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_1447_, v_msgData_1448_, v_severity_1449_, v_isSilent_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
stack->m_obj
 = v_res_1460_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_1461_, lean_object* v_msgData_1462_, lean_object* v_severity_1463_, lean_object* v_isSilent_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v_severity_boxed_1473_; uint8_t v_isSilent_boxed_1474_; lean_object* v_res_1475_; 
v_severity_boxed_1473_ = lean_unbox(v_severity_1463_);
v_isSilent_boxed_1474_ = lean_unbox(v_isSilent_1464_);
v_res_1475_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_1461_, v_msgData_1462_, v_severity_boxed_1473_, v_isSilent_boxed_1474_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v_ref_1461_);
return v_res_1475_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_linter_loopingSimpArgs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_linter_loopingSimpArgs);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_LoopProtection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_LoopProtection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
}
#ifdef __cplusplus
}
#endif

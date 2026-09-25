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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(lean_object* v_a_61_, lean_object* v_usedTheorems_62_, lean_object* v_a_x3f_63_){
_start:
{
lean_object* v___x_65_; lean_object* v_cache_66_; lean_object* v_congrCache_67_; lean_object* v_dsimpCache_68_; lean_object* v_numSteps_69_; lean_object* v_diag_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_80_; 
v___x_65_ = lean_st_ref_take(v_a_61_);
v_cache_66_ = lean_ctor_get(v___x_65_, 0);
v_congrCache_67_ = lean_ctor_get(v___x_65_, 1);
v_dsimpCache_68_ = lean_ctor_get(v___x_65_, 2);
v_numSteps_69_ = lean_ctor_get(v___x_65_, 4);
v_diag_70_ = lean_ctor_get(v___x_65_, 5);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_65_, 3);
lean_dec(v_unused_81_);
v___x_72_ = v___x_65_;
v_isShared_73_ = v_isSharedCheck_80_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_diag_70_);
lean_inc(v_numSteps_69_);
lean_inc(v_dsimpCache_68_);
lean_inc(v_congrCache_67_);
lean_inc(v_cache_66_);
lean_dec(v___x_65_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_80_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_box(0);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 3, v_usedTheorems_62_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_cache_66_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_congrCache_67_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_dsimpCache_68_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_usedTheorems_62_);
lean_ctor_set(v_reuseFailAlloc_79_, 4, v_numSteps_69_);
lean_ctor_set(v_reuseFailAlloc_79_, 5, v_diag_70_);
v___x_76_ = v_reuseFailAlloc_79_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_st_ref_put(v_a_61_, v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_74_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0___boxed(lean_object* v_a_82_, lean_object* v_usedTheorems_83_, lean_object* v_a_x3f_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_82_, v_usedTheorems_83_, v_a_x3f_84_);
lean_dec(v_a_x3f_84_);
lean_dec(v_a_82_);
return v_res_86_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; lean_object* v_usedTheorems_103_; lean_object* v___x_104_; lean_object* v_cache_105_; lean_object* v_congrCache_106_; lean_object* v_dsimpCache_107_; lean_object* v_numSteps_108_; lean_object* v_diag_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_147_; 
v___x_102_ = lean_st_ref_get(v_a_96_);
v_usedTheorems_103_ = lean_ctor_get(v___x_102_, 3);
lean_inc_ref(v_usedTheorems_103_);
lean_dec(v___x_102_);
v___x_104_ = lean_st_ref_take(v_a_96_);
v_cache_105_ = lean_ctor_get(v___x_104_, 0);
v_congrCache_106_ = lean_ctor_get(v___x_104_, 1);
v_dsimpCache_107_ = lean_ctor_get(v___x_104_, 2);
v_numSteps_108_ = lean_ctor_get(v___x_104_, 4);
v_diag_109_ = lean_ctor_get(v___x_104_, 5);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_104_, 3);
lean_dec(v_unused_148_);
v___x_111_ = v___x_104_;
v_isShared_112_ = v_isSharedCheck_147_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_diag_109_);
lean_inc(v_numSteps_108_);
lean_inc(v_dsimpCache_107_);
lean_inc(v_congrCache_106_);
lean_inc(v_cache_105_);
lean_dec(v___x_104_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_147_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 3, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_cache_105_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_congrCache_106_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_dsimpCache_107_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_numSteps_108_);
lean_ctor_set(v_reuseFailAlloc_146_, 5, v_diag_109_);
v___x_115_ = v_reuseFailAlloc_146_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v_r_117_; 
v___x_116_ = lean_st_ref_put(v_a_96_, v___x_115_);
lean_inc(v_a_100_);
lean_inc_ref(v_a_99_);
lean_inc(v_a_98_);
lean_inc_ref(v_a_97_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
lean_inc(v_a_94_);
v_r_117_ = lean_apply_8(v_x_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, lean_box(0));
if (lean_obj_tag(v_r_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_134_; 
v_a_118_ = lean_ctor_get(v_r_117_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_r_117_);
if (v_isSharedCheck_134_ == 0)
{
v___x_120_ = v_r_117_;
v_isShared_121_ = v_isSharedCheck_134_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v_r_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_134_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
lean_inc(v_a_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set_tag(v___x_120_, 1);
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_133_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v___x_124_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_96_, v_usedTheorems_103_, v___x_123_);
lean_dec_ref(v___x_123_);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_132_);
v___x_126_ = v___x_124_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_dec(v___x_124_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v_a_118_);
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_118_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v_a_135_ = lean_ctor_get(v_r_117_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v_r_117_, 1);
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_96_, v_usedTheorems_103_, v___x_136_);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_137_, 0);
lean_dec(v_unused_145_);
v___x_139_ = v___x_137_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_dec(v___x_137_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 1);
lean_ctor_set(v___x_139_, 0, v_a_135_);
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_135_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___boxed(lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(v_x_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems(lean_object* v_00_u03b1_159_, lean_object* v_x_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_usedTheorems_170_; lean_object* v___x_171_; lean_object* v_cache_172_; lean_object* v_congrCache_173_; lean_object* v_dsimpCache_174_; lean_object* v_numSteps_175_; lean_object* v_diag_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_214_; 
v___x_169_ = lean_st_ref_get(v_a_163_);
v_usedTheorems_170_ = lean_ctor_get(v___x_169_, 3);
lean_inc_ref(v_usedTheorems_170_);
lean_dec(v___x_169_);
v___x_171_ = lean_st_ref_take(v_a_163_);
v_cache_172_ = lean_ctor_get(v___x_171_, 0);
v_congrCache_173_ = lean_ctor_get(v___x_171_, 1);
v_dsimpCache_174_ = lean_ctor_get(v___x_171_, 2);
v_numSteps_175_ = lean_ctor_get(v___x_171_, 4);
v_diag_176_ = lean_ctor_get(v___x_171_, 5);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v___x_171_, 3);
lean_dec(v_unused_215_);
v___x_178_ = v___x_171_;
v_isShared_179_ = v_isSharedCheck_214_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_diag_176_);
lean_inc(v_numSteps_175_);
lean_inc(v_dsimpCache_174_);
lean_inc(v_congrCache_173_);
lean_inc(v_cache_172_);
lean_dec(v___x_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_214_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 3, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_cache_172_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_congrCache_173_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_dsimpCache_174_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_numSteps_175_);
lean_ctor_set(v_reuseFailAlloc_213_, 5, v_diag_176_);
v___x_182_ = v_reuseFailAlloc_213_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v_r_184_; 
v___x_183_ = lean_st_ref_put(v_a_163_, v___x_182_);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
lean_inc_ref(v_a_164_);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
v_r_184_ = lean_apply_8(v_x_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, lean_box(0));
if (lean_obj_tag(v_r_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_201_; 
v_a_185_ = lean_ctor_get(v_r_184_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_r_184_);
if (v_isSharedCheck_201_ == 0)
{
v___x_187_ = v_r_184_;
v_isShared_188_ = v_isSharedCheck_201_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v_r_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_201_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
lean_inc(v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_200_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v___x_191_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_163_, v_usedTheorems_170_, v___x_190_);
lean_dec_ref(v___x_190_);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_191_, 0);
lean_dec(v_unused_199_);
v___x_193_ = v___x_191_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_dec(v___x_191_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v_a_185_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_185_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_202_ = lean_ctor_get(v_r_184_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v_r_184_, 1);
v___x_203_ = lean_box(0);
v___x_204_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_163_, v_usedTheorems_170_, v___x_203_);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v___x_204_, 0);
lean_dec(v_unused_212_);
v___x_206_ = v___x_204_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_dec(v___x_204_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 1);
lean_ctor_set(v___x_206_, 0, v_a_202_);
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_202_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___boxed(lean_object* v_00_u03b1_216_, lean_object* v_x_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_Simp_withFreshUsedTheorems(v_00_u03b1_216_, v_x_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(lean_object* v_x_236_){
_start:
{
switch(lean_obj_tag(v_x_236_))
{
case 0:
{
lean_object* v_declName_238_; uint8_t v_post_239_; uint8_t v_inv_240_; uint8_t v___x_241_; lean_object* v_r_242_; 
v_declName_238_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_declName_238_);
v_post_239_ = lean_ctor_get_uint8(v_x_236_, sizeof(void*)*1);
v_inv_240_ = lean_ctor_get_uint8(v_x_236_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_236_, 1);
v___x_241_ = 0;
v_r_242_ = l_Lean_MessageData_ofConstName(v_declName_238_, v___x_241_);
if (v_post_239_ == 0)
{
if (v_inv_240_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_r_242_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_r_242_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
else
{
if (v_inv_240_ == 0)
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_r_242_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_r_242_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
case 1:
{
lean_object* v_fvarId_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_262_; 
v_fvarId_253_ = lean_ctor_get(v_x_236_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_262_ == 0)
{
v___x_255_ = v_x_236_;
v_isShared_256_ = v_isSharedCheck_262_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_fvarId_253_);
lean_dec(v_x_236_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_262_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = l_Lean_mkFVar(v_fvarId_253_);
v___x_258_ = l_Lean_MessageData_ofExpr(v___x_257_);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 0);
lean_ctor_set(v___x_255_, 0, v___x_258_);
v___x_260_ = v___x_255_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
case 2:
{
lean_object* v_ref_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_ref_263_ = lean_ctor_get(v_x_236_, 1);
lean_inc(v_ref_263_);
lean_dec_ref_known(v_x_236_, 2);
v___x_264_ = l_Lean_MessageData_ofSyntax(v_ref_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
default: 
{
lean_object* v_name_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_name_266_ = lean_ctor_get(v_x_236_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v_x_236_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_name_266_);
lean_dec(v_x_236_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = l_Lean_MessageData_ofName(v_name_266_);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___boxed(lean_object* v_x_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_278_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___boxed(lean_object* v_x_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(v_x_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(size_t v_sz_295_, size_t v_i_296_, lean_object* v_bs_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = lean_usize_dec_lt(v_i_296_, v_sz_295_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_bs_297_);
return v___x_304_;
}
else
{
lean_object* v_v_305_; lean_object* v___x_306_; lean_object* v_bs_x27_307_; lean_object* v_a_309_; lean_object* v___x_314_; 
v_v_305_ = lean_array_uget(v_bs_297_, v_i_296_);
v___x_306_ = lean_unsigned_to_nat(0u);
v_bs_x27_307_ = lean_array_uset(v_bs_297_, v_i_296_, v___x_306_);
v___x_314_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_v_305_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v___x_316_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_315_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
v_a_309_ = v___x_318_;
goto v___jp_308_;
}
else
{
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_314_, 1);
v_a_309_ = v_a_319_;
goto v___jp_308_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_bs_x27_307_);
v_a_320_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_314_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_314_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
v___jp_308_:
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_296_, v___x_310_);
v___x_312_ = lean_array_uset(v_bs_x27_307_, v_i_296_, v_a_309_);
v_i_296_ = v___x_311_;
v_bs_297_ = v___x_312_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___boxed(lean_object* v_sz_328_, lean_object* v_i_329_, lean_object* v_bs_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
size_t v_sz_boxed_336_; size_t v_i_boxed_337_; lean_object* v_res_338_; 
v_sz_boxed_336_ = lean_unbox_usize(v_sz_328_);
lean_dec(v_sz_328_);
v_i_boxed_337_ = lean_unbox_usize(v_i_329_);
lean_dec(v_i_329_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_boxed_336_, v_i_boxed_337_, v_bs_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(lean_object* v_origins_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; 
v_sz_345_ = lean_array_size(v_origins_339_);
v___x_346_ = ((size_t)0ULL);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_345_, v___x_346_, v_origins_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_357_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_357_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_352_ = lean_array_to_list(v_a_348_);
v___x_353_ = l_Lean_MessageData_andList(v___x_352_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_347_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_347_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins___boxed(lean_object* v_origins_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_origins_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(lean_object* v_x_373_){
_start:
{
switch(lean_obj_tag(v_x_373_))
{
case 0:
{
lean_object* v_declName_375_; uint8_t v_post_376_; uint8_t v_inv_377_; uint8_t v___x_378_; lean_object* v_r_379_; 
v_declName_375_ = lean_ctor_get(v_x_373_, 0);
lean_inc(v_declName_375_);
v_post_376_ = lean_ctor_get_uint8(v_x_373_, sizeof(void*)*1);
v_inv_377_ = lean_ctor_get_uint8(v_x_373_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_373_, 1);
v___x_378_ = 0;
v_r_379_ = l_Lean_MessageData_ofConstName(v_declName_375_, v___x_378_);
if (v_post_376_ == 0)
{
if (v_inv_377_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_r_379_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_r_379_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
else
{
if (v_inv_377_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_r_379_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_r_379_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
case 1:
{
lean_object* v_fvarId_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_399_; 
v_fvarId_390_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_399_ == 0)
{
v___x_392_ = v_x_373_;
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_fvarId_390_);
lean_dec(v_x_373_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = l_Lean_mkFVar(v_fvarId_390_);
v___x_395_ = l_Lean_MessageData_ofExpr(v___x_394_);
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 0);
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
case 2:
{
lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_ref_400_ = lean_ctor_get(v_x_373_, 1);
lean_inc(v_ref_400_);
lean_dec_ref_known(v_x_373_, 2);
v___x_401_ = l_Lean_MessageData_ofSyntax(v_ref_400_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
default: 
{
lean_object* v_name_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_name_403_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v_x_373_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_name_403_);
lean_dec(v_x_373_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_Lean_MessageData_ofName(v_name_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 0);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg___boxed(lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(lean_object* v_x_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_415_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___boxed(lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(lean_object* v___x_435_, lean_object* v_as_436_, size_t v_sz_437_, size_t v_i_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_a_442_; uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_b_439_);
return v___x_447_;
}
else
{
lean_object* v_a_448_; uint8_t v___y_452_; 
v_a_448_ = lean_array_uget_borrowed(v_as_436_, v_i_438_);
if (lean_obj_tag(v_a_448_) == 0)
{
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_declName_453_; uint8_t v_inv_454_; lean_object* v_declName_455_; uint8_t v_inv_456_; uint8_t v___x_457_; 
v_declName_453_ = lean_ctor_get(v_a_448_, 0);
v_inv_454_ = lean_ctor_get_uint8(v_a_448_, sizeof(void*)*1 + 1);
v_declName_455_ = lean_ctor_get(v___x_435_, 0);
v_inv_456_ = lean_ctor_get_uint8(v___x_435_, sizeof(void*)*1 + 1);
v___x_457_ = lean_name_eq(v_declName_453_, v_declName_455_);
if (v___x_457_ == 0)
{
v___y_452_ = v___x_457_;
goto v___jp_451_;
}
else
{
if (v_inv_456_ == 0)
{
if (v_inv_454_ == 0)
{
v___y_452_ = v___x_457_;
goto v___jp_451_;
}
else
{
goto v___jp_449_;
}
}
else
{
v___y_452_ = v_inv_454_;
goto v___jp_451_;
}
}
}
else
{
goto v___jp_449_;
}
}
else
{
if (lean_obj_tag(v___x_435_) == 0)
{
goto v___jp_449_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = l_Lean_Meta_Origin_key(v_a_448_);
v___x_459_ = l_Lean_Meta_Origin_key(v___x_435_);
v___x_460_ = lean_name_eq(v___x_458_, v___x_459_);
lean_dec(v___x_459_);
lean_dec(v___x_458_);
v___y_452_ = v___x_460_;
goto v___jp_451_;
}
}
v___jp_449_:
{
lean_object* v___x_450_; 
lean_inc(v_a_448_);
v___x_450_ = lean_array_push(v_b_439_, v_a_448_);
v_a_442_ = v___x_450_;
goto v___jp_441_;
}
v___jp_451_:
{
if (v___y_452_ == 0)
{
goto v___jp_449_;
}
else
{
v_a_442_ = v_b_439_;
goto v___jp_441_;
}
}
}
v___jp_441_:
{
size_t v___x_443_; size_t v___x_444_; 
v___x_443_ = ((size_t)1ULL);
v___x_444_ = lean_usize_add(v_i_438_, v___x_443_);
v_i_438_ = v___x_444_;
v_b_439_ = v_a_442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(lean_object* v___x_461_, lean_object* v_as_462_, lean_object* v_sz_463_, lean_object* v_i_464_, lean_object* v_b_465_, lean_object* v___y_466_){
_start:
{
size_t v_sz_boxed_467_; size_t v_i_boxed_468_; lean_object* v_res_469_; 
v_sz_boxed_467_ = lean_unbox_usize(v_sz_463_);
lean_dec(v_sz_463_);
v_i_boxed_468_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_461_, v_as_462_, v_sz_boxed_467_, v_i_boxed_468_, v_b_465_);
lean_dec_ref(v_as_462_);
lean_dec_ref(v___x_461_);
return v_res_469_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0));
v___x_472_ = l_Lean_stringToMessageData(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1);
v___x_474_ = l_Lean_MessageData_hint_x27(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4(void){
_start:
{
lean_object* v___x_476_; lean_object* v_msg_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v_msg_477_ = l_Lean_stringToMessageData(v___x_476_);
return v_msg_477_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg(lean_object* v_thm_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_msg_496_; lean_object* v_origin_500_; lean_object* v_msg_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_usedTheorems_512_; lean_object* v___x_513_; size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; 
v_origin_500_ = lean_ctor_get(v_thm_486_, 4);
lean_inc_ref_n(v_origin_500_, 2);
lean_dec_ref(v_thm_486_);
v_msg_501_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4);
v___x_502_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_500_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v___x_504_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_a_503_);
v___x_506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v_msg_501_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7));
v___x_511_ = lean_st_ref_get(v_a_489_);
v_usedTheorems_512_ = lean_ctor_get(v___x_511_, 3);
lean_inc_ref(v_usedTheorems_512_);
lean_dec(v___x_511_);
v___x_513_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_512_);
lean_dec_ref(v_usedTheorems_512_);
v_sz_514_ = lean_array_size(v___x_513_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_500_, v___x_513_, v_sz_514_, v___x_515_, v___x_510_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_origin_500_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = lean_array_get_size(v_a_517_);
v___x_519_ = lean_nat_dec_eq(v___x_518_, v___x_509_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_517_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_a_521_);
v___x_524_ = l_Lean_MessageData_note(v___x_523_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_508_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v_msg_496_ = v___x_525_;
goto v___jp_495_;
}
else
{
lean_dec_ref_known(v___x_508_, 2);
return v___x_520_;
}
}
else
{
lean_dec(v_a_517_);
v_msg_496_ = v___x_508_;
goto v___jp_495_;
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref_known(v___x_508_, 2);
v_a_526_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_516_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v_msg_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(lean_object* v_thm_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(lean_object* v___x_544_, lean_object* v_as_545_, size_t v_sz_546_, size_t v_i_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_544_, v_as_545_, v_sz_546_, v_i_547_, v_b_548_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(lean_object* v___x_558_, lean_object* v_as_559_, lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
size_t v_sz_boxed_571_; size_t v_i_boxed_572_; lean_object* v_res_573_; 
v_sz_boxed_571_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_572_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_558_, v_as_559_, v_sz_boxed_571_, v_i_boxed_572_, v_b_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v_as_559_);
lean_dec_ref(v___x_558_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(lean_object* v_o_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_env_579_; lean_object* v___x_580_; lean_object* v_toEnvExtension_581_; lean_object* v_asyncMode_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_merged_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v___x_577_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_578_ = lean_st_ref_get(v___y_575_);
v_env_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_env_579_);
lean_dec(v___x_578_);
v___x_580_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_581_ = lean_ctor_get(v___x_580_, 0);
v_asyncMode_582_ = lean_ctor_get(v_toEnvExtension_581_, 2);
v___x_583_ = lean_box(0);
v___x_584_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_577_, v___x_580_, v_env_579_, v_asyncMode_582_, v___x_583_);
v_merged_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_584_, 1);
lean_dec(v_unused_594_);
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_merged_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_merged_585_);
lean_ctor_set(v___x_587_, 0, v_o_574_);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_o_574_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_merged_585_);
v___x_590_ = v_reuseFailAlloc_592_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(lean_object* v_o_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_595_, v___y_596_);
lean_dec(v___y_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_599_);
v___x_603_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v___x_602_, v___y_600_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops(uint8_t v_force_608_, lean_object* v_ctxt_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_config_613_; uint8_t v_singlePass_614_; 
v_config_613_ = lean_ctor_get(v_ctxt_609_, 0);
v_singlePass_614_ = lean_ctor_get_uint8(v_config_613_, sizeof(void*)*3 + 2);
if (v_singlePass_614_ == 0)
{
if (v_force_608_ == 0)
{
lean_object* v___x_615_; lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v___x_615_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_610_, v_a_611_);
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_621_ = l_Lean_Linter_getLinterValue(v___x_620_, v_a_616_);
lean_dec(v_a_616_);
v___x_622_ = lean_box(v___x_621_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_box(v_force_608_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
else
{
uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = 0;
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops___boxed(lean_object* v_force_632_, lean_object* v_ctxt_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
uint8_t v_force_boxed_637_; lean_object* v_res_638_; 
v_force_boxed_637_ = lean_unbox(v_force_632_);
v_res_638_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_637_, v_ctxt_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec_ref(v_ctxt_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(lean_object* v_o_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_639_, v___y_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(lean_object* v_o_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(lean_object* v_k_649_, lean_object* v_b_650_, lean_object* v_c_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
v___x_657_ = lean_apply_7(v_k_649_, v_b_650_, v_c_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, lean_box(0));
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(lean_object* v_k_658_, lean_object* v_b_659_, lean_object* v_c_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_658_, v_b_659_, v_c_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(lean_object* v_type_667_, lean_object* v_k_668_, uint8_t v_cleanupAnnotations_669_, uint8_t v_whnfType_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___f_676_; lean_object* v___x_677_; 
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_676_, 0, v_k_668_);
v___x_677_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_667_, v___f_676_, v_cleanupAnnotations_669_, v_whnfType_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_677_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_677_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(lean_object* v_type_694_, lean_object* v_k_695_, lean_object* v_cleanupAnnotations_696_, lean_object* v_whnfType_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_703_; uint8_t v_whnfType_boxed_704_; lean_object* v_res_705_; 
v_cleanupAnnotations_boxed_703_ = lean_unbox(v_cleanupAnnotations_696_);
v_whnfType_boxed_704_ = lean_unbox(v_whnfType_697_);
v_res_705_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_694_, v_k_695_, v_cleanupAnnotations_boxed_703_, v_whnfType_boxed_704_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_object* v_00_u03b1_706_, lean_object* v_type_707_, lean_object* v_k_708_, uint8_t v_cleanupAnnotations_709_, uint8_t v_whnfType_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_707_, v_k_708_, v_cleanupAnnotations_709_, v_whnfType_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(lean_object* v_00_u03b1_717_, lean_object* v_type_718_, lean_object* v_k_719_, lean_object* v_cleanupAnnotations_720_, lean_object* v_whnfType_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_727_; uint8_t v_whnfType_boxed_728_; lean_object* v_res_729_; 
v_cleanupAnnotations_boxed_727_ = lean_unbox(v_cleanupAnnotations_720_);
v_whnfType_boxed_728_ = lean_unbox(v_whnfType_721_);
v_res_729_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(v_00_u03b1_717_, v_type_718_, v_k_719_, v_cleanupAnnotations_boxed_727_, v_whnfType_boxed_728_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(lean_object* v_msgData_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; lean_object* v_env_737_; lean_object* v___x_738_; lean_object* v_toCold_739_; lean_object* v_mctx_740_; lean_object* v_lctx_741_; lean_object* v_options_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_736_ = lean_st_ref_get(v___y_734_);
v_env_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc_ref(v_env_737_);
lean_dec(v___x_736_);
v___x_738_ = lean_st_ref_get(v___y_732_);
v_toCold_739_ = lean_ctor_get(v___y_733_, 0);
v_mctx_740_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_mctx_740_);
lean_dec(v___x_738_);
v_lctx_741_ = lean_ctor_get(v___y_731_, 2);
v_options_742_ = lean_ctor_get(v_toCold_739_, 2);
lean_inc_ref(v_options_742_);
lean_inc_ref(v_lctx_741_);
v___x_743_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_743_, 0, v_env_737_);
lean_ctor_set(v___x_743_, 1, v_mctx_740_);
lean_ctor_set(v___x_743_, 2, v_lctx_741_);
lean_ctor_set(v___x_743_, 3, v_options_742_);
v___x_744_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v_msgData_730_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(lean_object* v_msgData_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_752_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_753_; double v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_float_of_nat(v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(lean_object* v_cls_757_, lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_ref_764_; lean_object* v___x_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_811_; 
v_ref_764_ = lean_ctor_get(v___y_761_, 2);
v___x_765_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_811_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_811_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_811_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v_traceState_771_; lean_object* v_env_772_; lean_object* v_nextMacroScope_773_; lean_object* v_ngen_774_; lean_object* v_auxDeclNGen_775_; lean_object* v_cache_776_; lean_object* v_recordedDeps_777_; lean_object* v_messages_778_; lean_object* v_infoState_779_; lean_object* v_snapshotTasks_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_810_; 
v___x_770_ = lean_st_ref_take(v___y_762_);
v_traceState_771_ = lean_ctor_get(v___x_770_, 4);
v_env_772_ = lean_ctor_get(v___x_770_, 0);
v_nextMacroScope_773_ = lean_ctor_get(v___x_770_, 1);
v_ngen_774_ = lean_ctor_get(v___x_770_, 2);
v_auxDeclNGen_775_ = lean_ctor_get(v___x_770_, 3);
v_cache_776_ = lean_ctor_get(v___x_770_, 5);
v_recordedDeps_777_ = lean_ctor_get(v___x_770_, 6);
v_messages_778_ = lean_ctor_get(v___x_770_, 7);
v_infoState_779_ = lean_ctor_get(v___x_770_, 8);
v_snapshotTasks_780_ = lean_ctor_get(v___x_770_, 9);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_810_ == 0)
{
v___x_782_ = v___x_770_;
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snapshotTasks_780_);
lean_inc(v_infoState_779_);
lean_inc(v_messages_778_);
lean_inc(v_recordedDeps_777_);
lean_inc(v_cache_776_);
lean_inc(v_traceState_771_);
lean_inc(v_auxDeclNGen_775_);
lean_inc(v_ngen_774_);
lean_inc(v_nextMacroScope_773_);
lean_inc(v_env_772_);
lean_dec(v___x_770_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
uint64_t v_tid_784_; lean_object* v_traces_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_809_; 
v_tid_784_ = lean_ctor_get_uint64(v_traceState_771_, sizeof(void*)*1);
v_traces_785_ = lean_ctor_get(v_traceState_771_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_traceState_771_);
if (v_isSharedCheck_809_ == 0)
{
v___x_787_ = v_traceState_771_;
v_isShared_788_ = v_isSharedCheck_809_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_traces_785_);
lean_dec(v_traceState_771_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_809_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; double v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_box(0);
v___x_791_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
v___x_792_ = 0;
v___x_793_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v___x_794_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_794_, 0, v_cls_757_);
lean_ctor_set(v___x_794_, 1, v___x_790_);
lean_ctor_set(v___x_794_, 2, v___x_793_);
lean_ctor_set_float(v___x_794_, sizeof(void*)*3, v___x_791_);
lean_ctor_set_float(v___x_794_, sizeof(void*)*3 + 8, v___x_791_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*3 + 16, v___x_792_);
v___x_795_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1));
v___x_796_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v_a_766_);
lean_ctor_set(v___x_796_, 2, v___x_795_);
lean_inc(v_ref_764_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_ref_764_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_PersistentArray_push___redArg(v_traces_785_, v___x_797_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_798_);
v___x_800_ = v___x_787_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_798_);
lean_ctor_set_uint64(v_reuseFailAlloc_808_, sizeof(void*)*1, v_tid_784_);
v___x_800_ = v_reuseFailAlloc_808_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___x_800_);
v___x_802_ = v___x_782_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_env_772_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_nextMacroScope_773_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_ngen_774_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_auxDeclNGen_775_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_807_, 5, v_cache_776_);
lean_ctor_set(v_reuseFailAlloc_807_, 6, v_recordedDeps_777_);
lean_ctor_set(v_reuseFailAlloc_807_, 7, v_messages_778_);
lean_ctor_set(v_reuseFailAlloc_807_, 8, v_infoState_779_);
lean_ctor_set(v_reuseFailAlloc_807_, 9, v_snapshotTasks_780_);
v___x_802_ = v_reuseFailAlloc_807_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_st_ref_put(v___y_762_, v___x_802_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_789_);
v___x_805_ = v___x_768_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_789_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(lean_object* v_cls_812_, lean_object* v_msg_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_812_, v_msg_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(lean_object* v_opts_820_, lean_object* v_opt_821_){
_start:
{
lean_object* v_name_822_; lean_object* v_defValue_823_; lean_object* v_map_824_; lean_object* v___x_825_; 
v_name_822_ = lean_ctor_get(v_opt_821_, 0);
v_defValue_823_ = lean_ctor_get(v_opt_821_, 1);
v_map_824_ = lean_ctor_get(v_opts_820_, 0);
v___x_825_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_824_, v_name_822_);
if (lean_obj_tag(v___x_825_) == 0)
{
uint8_t v___x_826_; 
v___x_826_ = lean_unbox(v_defValue_823_);
return v___x_826_;
}
else
{
lean_object* v_val_827_; 
v_val_827_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v___x_825_, 1);
if (lean_obj_tag(v_val_827_) == 1)
{
uint8_t v_v_828_; 
v_v_828_ = lean_ctor_get_uint8(v_val_827_, 0);
lean_dec_ref_known(v_val_827_, 0);
return v_v_828_;
}
else
{
uint8_t v___x_829_; 
lean_dec(v_val_827_);
v___x_829_ = lean_unbox(v_defValue_823_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_opts_830_, lean_object* v_opt_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_830_, v_opt_831_);
lean_dec_ref(v_opt_831_);
lean_dec_ref(v_opts_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_842_, uint8_t v___y_843_, lean_object* v_x_844_){
_start:
{
if (lean_obj_tag(v_x_844_) == 1)
{
lean_object* v_pre_845_; 
v_pre_845_ = lean_ctor_get(v_x_844_, 0);
switch(lean_obj_tag(v_pre_845_))
{
case 1:
{
lean_object* v_pre_846_; 
v_pre_846_ = lean_ctor_get(v_pre_845_, 0);
switch(lean_obj_tag(v_pre_846_))
{
case 0:
{
lean_object* v_str_847_; lean_object* v_str_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_str_847_ = lean_ctor_get(v_x_844_, 1);
v_str_848_ = lean_ctor_get(v_pre_845_, 1);
v___x_849_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_850_ = lean_string_dec_eq(v_str_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_852_ = lean_string_dec_eq(v_str_848_, v___x_851_);
if (v___x_852_ == 0)
{
return v___x_852_;
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_854_ = lean_string_dec_eq(v_str_847_, v___x_853_);
if (v___x_854_ == 0)
{
return v___x_854_;
}
else
{
return v_suppressElabErrors_842_;
}
}
}
else
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_856_ = lean_string_dec_eq(v_str_847_, v___x_855_);
if (v___x_856_ == 0)
{
return v___x_856_;
}
else
{
return v_suppressElabErrors_842_;
}
}
}
case 1:
{
lean_object* v_pre_857_; 
v_pre_857_ = lean_ctor_get(v_pre_846_, 0);
if (lean_obj_tag(v_pre_857_) == 0)
{
lean_object* v_str_858_; lean_object* v_str_859_; lean_object* v_str_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_str_858_ = lean_ctor_get(v_x_844_, 1);
v_str_859_ = lean_ctor_get(v_pre_845_, 1);
v_str_860_ = lean_ctor_get(v_pre_846_, 1);
v___x_861_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_862_ = lean_string_dec_eq(v_str_860_, v___x_861_);
if (v___x_862_ == 0)
{
return v___x_862_;
}
else
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_864_ = lean_string_dec_eq(v_str_859_, v___x_863_);
if (v___x_864_ == 0)
{
return v___x_864_;
}
else
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_866_ = lean_string_dec_eq(v_str_858_, v___x_865_);
if (v___x_866_ == 0)
{
return v___x_866_;
}
else
{
return v_suppressElabErrors_842_;
}
}
}
}
else
{
return v___y_843_;
}
}
default: 
{
return v___y_843_;
}
}
}
case 0:
{
lean_object* v_str_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_str_867_ = lean_ctor_get(v_x_844_, 1);
v___x_868_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_869_ = lean_string_dec_eq(v_str_867_, v___x_868_);
if (v___x_869_ == 0)
{
return v___x_869_;
}
else
{
return v_suppressElabErrors_842_;
}
}
default: 
{
return v___y_843_;
}
}
}
else
{
return v___y_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_870_, lean_object* v___y_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_suppressElabErrors_boxed_873_; uint8_t v___y_21688__boxed_874_; uint8_t v_res_875_; lean_object* v_r_876_; 
v_suppressElabErrors_boxed_873_ = lean_unbox(v_suppressElabErrors_870_);
v___y_21688__boxed_874_ = lean_unbox(v___y_871_);
v_res_875_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_873_, v___y_21688__boxed_874_, v_x_872_);
lean_dec(v_x_872_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_877_, lean_object* v_msgData_878_, uint8_t v_severity_879_, uint8_t v_isSilent_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; uint8_t v___y_893_; lean_object* v_toCold_894_; lean_object* v___y_895_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; uint8_t v___y_927_; lean_object* v___y_928_; uint8_t v___y_929_; uint8_t v___y_930_; lean_object* v___y_931_; lean_object* v___y_951_; lean_object* v___y_952_; uint8_t v___y_953_; lean_object* v___y_954_; uint8_t v___y_955_; uint8_t v___y_956_; lean_object* v___y_957_; uint8_t v___y_961_; uint8_t v___y_962_; uint8_t v___y_963_; uint8_t v___x_974_; uint8_t v___y_976_; uint8_t v___y_977_; uint8_t v___y_978_; uint8_t v___y_980_; uint8_t v___x_988_; 
v___x_974_ = 2;
v___x_988_ = l_Lean_instBEqMessageSeverity_beq(v_severity_879_, v___x_974_);
if (v___x_988_ == 0)
{
v___y_980_ = v___x_988_;
goto v___jp_979_;
}
else
{
uint8_t v___x_989_; 
lean_inc_ref(v_msgData_878_);
v___x_989_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_878_);
v___y_980_ = v___x_989_;
goto v___jp_979_;
}
v___jp_886_:
{
lean_object* v_currNamespace_896_; lean_object* v_openDecls_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_env_902_; lean_object* v_nextMacroScope_903_; lean_object* v_ngen_904_; lean_object* v_auxDeclNGen_905_; lean_object* v_traceState_906_; lean_object* v_cache_907_; lean_object* v_recordedDeps_908_; lean_object* v_messages_909_; lean_object* v_infoState_910_; lean_object* v_snapshotTasks_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_922_; 
v_currNamespace_896_ = lean_ctor_get(v_toCold_894_, 4);
v_openDecls_897_ = lean_ctor_get(v_toCold_894_, 5);
lean_inc(v_openDecls_897_);
lean_inc(v_currNamespace_896_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_currNamespace_896_);
lean_ctor_set(v___x_898_, 1, v_openDecls_897_);
v___x_899_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___y_887_);
lean_inc_ref(v___y_892_);
lean_inc_ref(v___y_888_);
v___x_900_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_900_, 0, v___y_888_);
lean_ctor_set(v___x_900_, 1, v___y_891_);
lean_ctor_set(v___x_900_, 2, v___y_890_);
lean_ctor_set(v___x_900_, 3, v___y_892_);
lean_ctor_set(v___x_900_, 4, v___x_899_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*5, v___y_889_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*5 + 1, v___y_893_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*5 + 2, v_isSilent_880_);
v___x_901_ = lean_st_ref_take(v___y_895_);
v_env_902_ = lean_ctor_get(v___x_901_, 0);
v_nextMacroScope_903_ = lean_ctor_get(v___x_901_, 1);
v_ngen_904_ = lean_ctor_get(v___x_901_, 2);
v_auxDeclNGen_905_ = lean_ctor_get(v___x_901_, 3);
v_traceState_906_ = lean_ctor_get(v___x_901_, 4);
v_cache_907_ = lean_ctor_get(v___x_901_, 5);
v_recordedDeps_908_ = lean_ctor_get(v___x_901_, 6);
v_messages_909_ = lean_ctor_get(v___x_901_, 7);
v_infoState_910_ = lean_ctor_get(v___x_901_, 8);
v_snapshotTasks_911_ = lean_ctor_get(v___x_901_, 9);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_922_ == 0)
{
v___x_913_ = v___x_901_;
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snapshotTasks_911_);
lean_inc(v_infoState_910_);
lean_inc(v_messages_909_);
lean_inc(v_recordedDeps_908_);
lean_inc(v_cache_907_);
lean_inc(v_traceState_906_);
lean_inc(v_auxDeclNGen_905_);
lean_inc(v_ngen_904_);
lean_inc(v_nextMacroScope_903_);
lean_inc(v_env_902_);
lean_dec(v___x_901_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = lean_box(0);
v___x_916_ = l_Lean_MessageLog_add(v___x_900_, v_messages_909_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 7, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_env_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_nextMacroScope_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_ngen_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_auxDeclNGen_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_traceState_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v_cache_907_);
lean_ctor_set(v_reuseFailAlloc_921_, 6, v_recordedDeps_908_);
lean_ctor_set(v_reuseFailAlloc_921_, 7, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_921_, 8, v_infoState_910_);
lean_ctor_set(v_reuseFailAlloc_921_, 9, v_snapshotTasks_911_);
v___x_918_ = v_reuseFailAlloc_921_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_st_ref_put(v___y_895_, v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_915_);
return v___x_920_;
}
}
}
v___jp_923_:
{
lean_object* v_fileName_932_; lean_object* v_fileMap_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_949_; 
v_fileName_932_ = lean_ctor_get(v___y_926_, 0);
v_fileMap_933_ = lean_ctor_get(v___y_926_, 1);
v___x_934_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_878_);
v___x_935_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_934_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_949_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_inc_ref_n(v_fileMap_933_, 2);
v___x_940_ = l_Lean_FileMap_toPosition(v_fileMap_933_, v___y_928_);
lean_dec(v___y_928_);
v___x_941_ = l_Lean_FileMap_toPosition(v_fileMap_933_, v___y_931_);
lean_dec(v___y_931_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
v___x_943_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
if (v___y_930_ == 0)
{
lean_del_object(v___x_938_);
lean_dec_ref(v___y_925_);
v___y_887_ = v_a_936_;
v___y_888_ = v_fileName_932_;
v___y_889_ = v___y_927_;
v___y_890_ = v___x_942_;
v___y_891_ = v___x_940_;
v___y_892_ = v___x_943_;
v___y_893_ = v___y_929_;
v_toCold_894_ = v___y_924_;
v___y_895_ = v___y_884_;
goto v___jp_886_;
}
else
{
uint8_t v___x_944_; 
lean_inc(v_a_936_);
v___x_944_ = l_Lean_MessageData_hasTag(v___y_925_, v_a_936_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec_ref_known(v___x_942_, 1);
lean_dec_ref(v___x_940_);
lean_dec(v_a_936_);
v___x_945_ = lean_box(0);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_947_ = v___x_938_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
lean_del_object(v___x_938_);
v___y_887_ = v_a_936_;
v___y_888_ = v_fileName_932_;
v___y_889_ = v___y_927_;
v___y_890_ = v___x_942_;
v___y_891_ = v___x_940_;
v___y_892_ = v___x_943_;
v___y_893_ = v___y_929_;
v_toCold_894_ = v___y_924_;
v___y_895_ = v___y_884_;
goto v___jp_886_;
}
}
}
}
v___jp_950_:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Syntax_getTailPos_x3f(v___y_954_, v___y_955_);
lean_dec(v___y_954_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_inc(v___y_957_);
v___y_924_ = v___y_951_;
v___y_925_ = v___y_952_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_955_;
v___y_928_ = v___y_957_;
v___y_929_ = v___y_956_;
v___y_930_ = v___y_953_;
v___y_931_ = v___y_957_;
goto v___jp_923_;
}
else
{
lean_object* v_val_959_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v___x_958_, 1);
v___y_924_ = v___y_951_;
v___y_925_ = v___y_952_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_955_;
v___y_928_ = v___y_957_;
v___y_929_ = v___y_956_;
v___y_930_ = v___y_953_;
v___y_931_ = v_val_959_;
goto v___jp_923_;
}
}
v___jp_960_:
{
lean_object* v_toCold_964_; lean_object* v_ref_965_; uint8_t v_suppressElabErrors_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v_ref_970_; lean_object* v___x_971_; 
v_toCold_964_ = lean_ctor_get(v___y_883_, 0);
v_ref_965_ = lean_ctor_get(v___y_883_, 2);
v_suppressElabErrors_966_ = lean_ctor_get_uint8(v___y_883_, sizeof(void*)*3 + 2);
v___x_967_ = lean_box(v_suppressElabErrors_966_);
v___x_968_ = lean_box(v___y_961_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_969_, 0, v___x_967_);
lean_closure_set(v___f_969_, 1, v___x_968_);
v_ref_970_ = l_Lean_replaceRef(v_ref_877_, v_ref_965_);
v___x_971_ = l_Lean_Syntax_getPos_x3f(v_ref_970_, v___y_962_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___y_951_ = v_toCold_964_;
v___y_952_ = v___f_969_;
v___y_953_ = v_suppressElabErrors_966_;
v___y_954_ = v_ref_970_;
v___y_955_ = v___y_962_;
v___y_956_ = v___y_963_;
v___y_957_ = v___x_972_;
goto v___jp_950_;
}
else
{
lean_object* v_val_973_; 
v_val_973_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_val_973_);
lean_dec_ref_known(v___x_971_, 1);
v___y_951_ = v_toCold_964_;
v___y_952_ = v___f_969_;
v___y_953_ = v_suppressElabErrors_966_;
v___y_954_ = v_ref_970_;
v___y_955_ = v___y_962_;
v___y_956_ = v___y_963_;
v___y_957_ = v_val_973_;
goto v___jp_950_;
}
}
v___jp_975_:
{
if (v___y_978_ == 0)
{
v___y_961_ = v___y_976_;
v___y_962_ = v___y_977_;
v___y_963_ = v_severity_879_;
goto v___jp_960_;
}
else
{
v___y_961_ = v___y_976_;
v___y_962_ = v___y_977_;
v___y_963_ = v___x_974_;
goto v___jp_960_;
}
}
v___jp_979_:
{
if (v___y_980_ == 0)
{
uint8_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = 1;
v___x_982_ = l_Lean_instBEqMessageSeverity_beq(v_severity_879_, v___x_981_);
if (v___x_982_ == 0)
{
v___y_976_ = v___y_980_;
v___y_977_ = v___y_980_;
v___y_978_ = v___x_982_;
goto v___jp_975_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_883_);
v___x_984_ = l_Lean_warningAsError;
v___x_985_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v___x_983_, v___x_984_);
lean_dec_ref(v___x_983_);
v___y_976_ = v___y_980_;
v___y_977_ = v___y_980_;
v___y_978_ = v___x_985_;
goto v___jp_975_;
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v_msgData_878_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_990_, lean_object* v_msgData_991_, lean_object* v_severity_992_, lean_object* v_isSilent_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
uint8_t v_severity_boxed_999_; uint8_t v_isSilent_boxed_1000_; lean_object* v_res_1001_; 
v_severity_boxed_999_ = lean_unbox(v_severity_992_);
v_isSilent_boxed_1000_ = lean_unbox(v_isSilent_993_);
v_res_1001_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_990_, v_msgData_991_, v_severity_boxed_999_, v_isSilent_boxed_1000_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v_ref_990_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(lean_object* v_ref_1002_, lean_object* v_msgData_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = 1;
v___x_1013_ = 0;
v___x_1014_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1002_, v_msgData_1003_, v___x_1012_, v___x_1013_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(lean_object* v_ref_1015_, lean_object* v_msgData_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_1015_, v_msgData_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec(v_ref_1015_);
return v_res_1025_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(lean_object* v_linterOption_1032_, lean_object* v_stx_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_name_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1061_; 
v_name_1043_ = lean_ctor_get(v_linterOption_1032_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_linterOption_1032_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_linterOption_1032_, 1);
lean_dec(v_unused_1062_);
v___x_1045_ = v_linterOption_1032_;
v_isShared_1046_ = v_isSharedCheck_1061_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_name_1043_);
lean_dec(v_linterOption_1032_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1061_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
lean_inc(v_name_1043_);
v___x_1048_ = l_Lean_MessageData_ofName(v_name_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 7);
lean_ctor_set(v___x_1045_, 1, v___x_1048_);
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_disable_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1051_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v_disable_1053_ = l_Lean_MessageData_note(v___x_1052_);
v___x_1054_ = l_Lean_Linter_linterMessageTag;
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_msg_1034_);
lean_ctor_set(v___x_1055_, 1, v_disable_1053_);
v___x_1056_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_name_1043_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
lean_inc(v_stx_1033_);
v___x_1058_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_stx_1033_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_1033_, v___x_1058_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v_stx_1033_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(lean_object* v_linterOption_1063_, lean_object* v_stx_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v_linterOption_1063_, v_stx_1064_, v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(lean_object* v_msgData_1075_, uint8_t v_severity_1076_, uint8_t v_isSilent_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_ref_1086_; lean_object* v___x_1087_; 
v_ref_1086_ = lean_ctor_get(v___y_1083_, 2);
v___x_1087_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1086_, v_msgData_1075_, v_severity_1076_, v_isSilent_1077_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(lean_object* v_msgData_1088_, lean_object* v_severity_1089_, lean_object* v_isSilent_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_severity_boxed_1099_; uint8_t v_isSilent_boxed_1100_; lean_object* v_res_1101_; 
v_severity_boxed_1099_ = lean_unbox(v_severity_1089_);
v_isSilent_boxed_1100_ = lean_unbox(v_isSilent_1090_);
v_res_1101_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1088_, v_severity_boxed_1099_, v_isSilent_boxed_1100_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(lean_object* v_msgData_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = 1;
v___x_1112_ = 0;
v___x_1113_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1102_, v___x_1111_, v___x_1112_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(lean_object* v_msgData_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_msgData_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3));
v___x_1135_ = l_Lean_Name_append(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(uint8_t v_force_1142_, lean_object* v_thm_1143_, lean_object* v___x_1144_, lean_object* v_origin_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1179_; 
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
lean_inc(v___y_1150_);
lean_inc_ref(v___y_1149_);
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc(v___y_1146_);
v___x_1179_ = lean_simp(v___x_1144_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v___y_1146_);
lean_dec_ref(v_origin_1145_);
lean_dec_ref(v_thm_1143_);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v___x_1179_, 0);
lean_dec(v_unused_1188_);
v___x_1181_ = v___x_1179_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v___x_1179_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_box(0);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1214_; 
v_a_1189_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1191_ = v___x_1179_;
v_isShared_1192_ = v_isSharedCheck_1214_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1179_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1214_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v___x_1193_; 
v___x_1193_ = l_Lean_Exception_isInterrupt(v_a_1189_);
if (v___x_1193_ == 0)
{
lean_object* v_toCold_1194_; lean_object* v_options_1195_; uint8_t v_hasTrace_1196_; 
lean_del_object(v___x_1191_);
v_toCold_1194_ = lean_ctor_get(v___y_1151_, 0);
v_options_1195_ = lean_ctor_get(v_toCold_1194_, 2);
v_hasTrace_1196_ = lean_ctor_get_uint8(v_options_1195_, sizeof(void*)*1);
if (v_hasTrace_1196_ == 0)
{
lean_dec(v_a_1189_);
lean_dec_ref(v_origin_1145_);
goto v___jp_1154_;
}
else
{
lean_object* v_inheritedTraceOptions_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_inheritedTraceOptions_1197_ = lean_ctor_get(v_toCold_1194_, 11);
v___x_1198_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4);
v___x_1200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1197_, v_options_1195_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_a_1189_);
lean_dec_ref(v_origin_1145_);
goto v___jp_1154_;
}
else
{
lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1201_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_1145_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_a_1202_);
v___x_1205_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__8, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_Exception_toMessageData(v_a_1189_);
v___x_1208_ = l_Lean_indentD(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v___x_1198_, v___x_1209_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_dec_ref_known(v___x_1210_, 1);
goto v___jp_1154_;
}
else
{
lean_dec(v___y_1146_);
lean_dec_ref(v_thm_1143_);
return v___x_1210_;
}
}
}
}
else
{
lean_object* v___x_1212_; 
lean_dec(v___y_1146_);
lean_dec_ref(v_origin_1145_);
lean_dec_ref(v_thm_1143_);
if (v_isShared_1192_ == 0)
{
v___x_1212_ = v___x_1191_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1189_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
v___jp_1154_:
{
if (v_force_1142_ == 0)
{
lean_object* v_ref_1155_; lean_object* v___x_1156_; 
v_ref_1155_ = lean_ctor_get(v___y_1151_, 2);
v___x_1156_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1143_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
lean_inc(v_ref_1155_);
v___x_1159_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v___x_1158_, v_ref_1155_, v_a_1157_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1146_);
return v___x_1159_;
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v___y_1146_);
v_a_1160_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1156_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1156_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
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
else
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1143_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_a_1169_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1146_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec(v___y_1146_);
v_a_1171_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1168_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1168_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___boxed(lean_object* v_force_1215_, lean_object* v_thm_1216_, lean_object* v___x_1217_, lean_object* v_origin_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_force_boxed_1227_; lean_object* v_res_1228_; 
v_force_boxed_1227_ = lean_unbox(v_force_1215_);
v_res_1228_ = l_Lean_Meta_Simp_checkLoops___lam__0(v_force_boxed_1227_, v_thm_1216_, v___x_1217_, v_origin_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1228_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_unsigned_to_nat(16u);
v___x_1231_ = lean_mk_array(v___x_1230_, v___x_1229_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__0, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_unsigned_to_nat(32u);
v___x_1241_ = lean_mk_empty_array_with_capacity(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5(void){
_start:
{
size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_unsigned_to_nat(32u);
v___x_1246_ = lean_mk_empty_array_with_capacity(v___x_1245_);
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4);
v___x_1248_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___x_1246_);
lean_ctor_set(v___x_1248_, 2, v___x_1244_);
lean_ctor_set(v___x_1248_, 3, v___x_1244_);
lean_ctor_set_usize(v___x_1248_, 4, v___x_1243_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__5, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5);
v___x_1250_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
lean_ctor_set(v___x_1251_, 2, v___x_1250_);
lean_ctor_set(v___x_1251_, 3, v___x_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1(uint8_t v_force_1252_, lean_object* v_thm_1253_, lean_object* v_origin_1254_, uint8_t v_a_1255_, lean_object* v_ctxt_1256_, lean_object* v_methods_1257_, lean_object* v___xs_1258_, lean_object* v_type_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v___y_1261_);
lean_inc_ref(v___y_1260_);
v___x_1265_ = lean_whnf(v_type_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Expr_appArg_x21(v_a_1266_);
lean_dec(v_a_1266_);
v___x_1268_ = lean_box(v_force_1252_);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1269_, 0, v___x_1268_);
lean_closure_set(v___f_1269_, 1, v_thm_1253_);
lean_closure_set(v___f_1269_, 2, v___x_1267_);
lean_closure_set(v___f_1269_, 3, v_origin_1254_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__1, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1);
v___x_1272_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1273_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*2, v_a_1255_);
v___x_1274_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1275_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6);
v___x_1276_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1273_);
lean_ctor_set(v___x_1276_, 1, v___x_1271_);
lean_ctor_set(v___x_1276_, 2, v___x_1271_);
lean_ctor_set(v___x_1276_, 3, v___x_1274_);
lean_ctor_set(v___x_1276_, 4, v___x_1270_);
lean_ctor_set(v___x_1276_, 5, v___x_1275_);
v___x_1277_ = l_Lean_Meta_Simp_SimpM_run___redArg(v_ctxt_1256_, v___x_1276_, v_methods_1257_, v___f_1269_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1277_, 0);
lean_dec(v_unused_1286_);
v___x_1279_ = v___x_1277_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v___x_1277_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_box(0);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1277_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1277_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
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
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_methods_1257_);
lean_dec_ref(v_ctxt_1256_);
lean_dec_ref(v_origin_1254_);
lean_dec_ref(v_thm_1253_);
v_a_1295_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1265_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1265_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___boxed(lean_object* v_force_1303_, lean_object* v_thm_1304_, lean_object* v_origin_1305_, lean_object* v_a_1306_, lean_object* v_ctxt_1307_, lean_object* v_methods_1308_, lean_object* v___xs_1309_, lean_object* v_type_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_force_boxed_1316_; uint8_t v_a_22363__boxed_1317_; lean_object* v_res_1318_; 
v_force_boxed_1316_ = lean_unbox(v_force_1303_);
v_a_22363__boxed_1317_ = lean_unbox(v_a_1306_);
v_res_1318_ = l_Lean_Meta_Simp_checkLoops___lam__1(v_force_boxed_1316_, v_thm_1304_, v_origin_1305_, v_a_22363__boxed_1317_, v_ctxt_1307_, v_methods_1308_, v___xs_1309_, v_type_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v___xs_1309_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops(uint8_t v_force_1319_, lean_object* v_ctxt_1320_, lean_object* v_methods_1321_, lean_object* v_thm_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_1319_, v_ctxt_1320_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1368_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1368_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1368_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_unbox(v_a_1329_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec(v_a_1329_);
lean_dec_ref(v_thm_1322_);
lean_dec_ref(v_methods_1321_);
lean_dec_ref(v_ctxt_1320_);
v___x_1334_ = lean_box(0);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1334_);
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v_proof_1338_; lean_object* v_origin_1339_; uint8_t v___x_1340_; 
v_proof_1338_ = lean_ctor_get(v_thm_1322_, 2);
v_origin_1339_ = lean_ctor_get(v_thm_1322_, 4);
v___x_1340_ = l_Lean_Expr_hasFVar(v_proof_1338_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1331_);
v___x_1341_ = lean_box(v_force_1319_);
lean_inc_ref(v_origin_1339_);
lean_inc_ref(v_thm_1322_);
v___f_1342_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1342_, 0, v___x_1341_);
lean_closure_set(v___f_1342_, 1, v_thm_1322_);
lean_closure_set(v___f_1342_, 2, v_origin_1339_);
lean_closure_set(v___f_1342_, 3, v_a_1329_);
lean_closure_set(v___f_1342_, 4, v_ctxt_1320_);
lean_closure_set(v___f_1342_, 5, v_methods_1321_);
v___x_1343_ = l_Lean_Meta_SimpTheorem_getValue(v_thm_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
lean_inc(v_a_1326_);
lean_inc_ref(v_a_1325_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
v___x_1345_ = lean_infer_type(v_a_1344_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_1346_, v___f_1342_, v___x_1340_, v___x_1340_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1347_;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v___f_1342_);
v_a_1348_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1345_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v___f_1342_);
v_a_1356_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1343_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1343_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec(v_a_1329_);
lean_dec_ref(v_thm_1322_);
lean_dec_ref(v_methods_1321_);
lean_dec_ref(v_ctxt_1320_);
v___x_1364_ = lean_box(0);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1364_);
v___x_1366_ = v___x_1331_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_thm_1322_);
lean_dec_ref(v_methods_1321_);
lean_dec_ref(v_ctxt_1320_);
v_a_1369_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1328_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1328_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___boxed(lean_object* v_force_1377_, lean_object* v_ctxt_1378_, lean_object* v_methods_1379_, lean_object* v_thm_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
uint8_t v_force_boxed_1386_; lean_object* v_res_1387_; 
v_force_boxed_1386_ = lean_unbox(v_force_1377_);
v_res_1387_ = l_Lean_Meta_Simp_checkLoops(v_force_boxed_1386_, v_ctxt_1378_, v_methods_1379_, v_thm_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(lean_object* v_cls_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_1388_, v_msg_1389_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(lean_object* v_cls_1399_, lean_object* v_msg_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(v_cls_1399_, v_msg_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(lean_object* v_ref_1410_, lean_object* v_msgData_1411_, uint8_t v_severity_1412_, uint8_t v_isSilent_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1410_, v_msgData_1411_, v_severity_1412_, v_isSilent_1413_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_1423_, lean_object* v_msgData_1424_, lean_object* v_severity_1425_, lean_object* v_isSilent_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v_severity_boxed_1435_; uint8_t v_isSilent_boxed_1436_; lean_object* v_res_1437_; 
v_severity_boxed_1435_ = lean_unbox(v_severity_1425_);
v_isSilent_boxed_1436_ = lean_unbox(v_isSilent_1426_);
v_res_1437_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_1423_, v_msgData_1424_, v_severity_boxed_1435_, v_isSilent_boxed_1436_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec(v_ref_1423_);
return v_res_1437_;
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

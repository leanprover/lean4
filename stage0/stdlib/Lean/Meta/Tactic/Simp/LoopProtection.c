// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.LoopProtection
// Imports: public import Lean.Meta.Tactic.Simp.Types public import Lean.Linter.Basic
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5;
static const lean_string_object l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Possibly looping simp theorem: `"};
static const lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___closed__7;
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
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 3, v_usedTheorems_62_);
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
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
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_st_ref_set(v_a_61_, v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
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
v___x_87_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_cache_104_; lean_object* v_congrCache_105_; lean_object* v_dsimpCache_106_; lean_object* v_numSteps_107_; lean_object* v_diag_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_147_; 
v___x_102_ = lean_st_ref_get(v_a_96_);
v___x_103_ = lean_st_ref_take(v_a_96_);
v_cache_104_ = lean_ctor_get(v___x_103_, 0);
v_congrCache_105_ = lean_ctor_get(v___x_103_, 1);
v_dsimpCache_106_ = lean_ctor_get(v___x_103_, 2);
v_numSteps_107_ = lean_ctor_get(v___x_103_, 4);
v_diag_108_ = lean_ctor_get(v___x_103_, 5);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_103_, 3);
lean_dec(v_unused_148_);
v___x_110_ = v___x_103_;
v_isShared_111_ = v_isSharedCheck_147_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_diag_108_);
lean_inc(v_numSteps_107_);
lean_inc(v_dsimpCache_106_);
lean_inc(v_congrCache_105_);
lean_inc(v_cache_104_);
lean_dec(v___x_103_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_147_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 3, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_cache_104_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_congrCache_105_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_dsimpCache_106_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_numSteps_107_);
lean_ctor_set(v_reuseFailAlloc_146_, 5, v_diag_108_);
v___x_114_ = v_reuseFailAlloc_146_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v_usedTheorems_116_; lean_object* v_r_117_; 
v___x_115_ = lean_st_ref_set(v_a_96_, v___x_114_);
v_usedTheorems_116_ = lean_ctor_get(v___x_102_, 3);
lean_inc_ref(v_usedTheorems_116_);
lean_dec(v___x_102_);
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
v___x_124_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_96_, v_usedTheorems_116_, v___x_123_);
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
lean_dec_ref(v_r_117_);
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_96_, v_usedTheorems_116_, v___x_136_);
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
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_cache_171_; lean_object* v_congrCache_172_; lean_object* v_dsimpCache_173_; lean_object* v_numSteps_174_; lean_object* v_diag_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_214_; 
v___x_169_ = lean_st_ref_get(v_a_163_);
v___x_170_ = lean_st_ref_take(v_a_163_);
v_cache_171_ = lean_ctor_get(v___x_170_, 0);
v_congrCache_172_ = lean_ctor_get(v___x_170_, 1);
v_dsimpCache_173_ = lean_ctor_get(v___x_170_, 2);
v_numSteps_174_ = lean_ctor_get(v___x_170_, 4);
v_diag_175_ = lean_ctor_get(v___x_170_, 5);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v___x_170_, 3);
lean_dec(v_unused_215_);
v___x_177_ = v___x_170_;
v_isShared_178_ = v_isSharedCheck_214_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_diag_175_);
lean_inc(v_numSteps_174_);
lean_inc(v_dsimpCache_173_);
lean_inc(v_congrCache_172_);
lean_inc(v_cache_171_);
lean_dec(v___x_170_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_214_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 3, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_cache_171_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_congrCache_172_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_dsimpCache_173_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_numSteps_174_);
lean_ctor_set(v_reuseFailAlloc_213_, 5, v_diag_175_);
v___x_181_ = v_reuseFailAlloc_213_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v_usedTheorems_183_; lean_object* v_r_184_; 
v___x_182_ = lean_st_ref_set(v_a_163_, v___x_181_);
v_usedTheorems_183_ = lean_ctor_get(v___x_169_, 3);
lean_inc_ref(v_usedTheorems_183_);
lean_dec(v___x_169_);
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
v___x_191_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_163_, v_usedTheorems_183_, v___x_190_);
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
lean_dec_ref(v_r_184_);
v___x_203_ = lean_box(0);
v___x_204_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_163_, v_usedTheorems_183_, v___x_203_);
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
lean_dec_ref(v_x_236_);
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
lean_dec_ref(v_x_236_);
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
lean_dec_ref(v___x_314_);
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
lean_dec_ref(v___x_314_);
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
lean_dec_ref(v_x_373_);
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
lean_dec_ref(v_x_373_);
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
if (v_inv_454_ == 0)
{
if (v_inv_456_ == 0)
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
v___y_452_ = v_inv_456_;
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
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v_msg_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
v_msg_479_ = l_Lean_stringToMessageData(v___x_478_);
return v_msg_479_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
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
lean_object* v_msg_496_; lean_object* v_origin_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v_usedTheorems_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; size_t v_sz_508_; size_t v___x_509_; lean_object* v___x_510_; 
v_origin_500_ = lean_ctor_get(v_thm_486_, 4);
lean_inc_ref_n(v_origin_500_, 2);
lean_dec_ref(v_thm_486_);
v___x_501_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_500_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = lean_st_ref_get(v_a_489_);
v_usedTheorems_504_ = lean_ctor_get(v___x_503_, 3);
lean_inc_ref(v_usedTheorems_504_);
lean_dec(v___x_503_);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v___x_507_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_504_);
lean_dec_ref(v_usedTheorems_504_);
v_sz_508_ = lean_array_size(v___x_507_);
v___x_509_ = ((size_t)0ULL);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_500_, v___x_507_, v_sz_508_, v___x_509_, v___x_506_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_origin_500_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v_msg_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v_msg_512_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5);
v___x_513_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_a_502_);
v___x_515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v_msg_512_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_array_get_size(v_a_511_);
v___x_519_ = lean_nat_dec_eq(v___x_518_, v___x_505_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_511_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_a_521_);
v___x_524_ = l_Lean_MessageData_note(v___x_523_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_517_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v_msg_496_ = v___x_525_;
goto v___jp_495_;
}
else
{
lean_dec_ref(v___x_517_);
return v___x_520_;
}
}
else
{
lean_dec(v_a_511_);
v_msg_496_ = v___x_517_;
goto v___jp_495_;
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_502_);
v_a_526_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_510_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_510_);
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
lean_object* v___x_577_; lean_object* v_env_578_; lean_object* v___x_579_; lean_object* v_toEnvExtension_580_; lean_object* v_asyncMode_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_linterSets_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_577_ = lean_st_ref_get(v___y_575_);
v_env_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_577_);
v___x_579_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_580_ = lean_ctor_get(v___x_579_, 0);
v_asyncMode_581_ = lean_ctor_get(v_toEnvExtension_580_, 2);
v___x_582_ = lean_box(1);
v___x_583_ = lean_box(0);
v_linterSets_584_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_582_, v___x_579_, v_env_578_, v_asyncMode_581_, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_o_574_);
lean_ctor_set(v___x_585_, 1, v_linterSets_584_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(lean_object* v_o_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_587_, v___y_588_);
lean_dec(v___y_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_options_594_; lean_object* v___x_595_; 
v_options_594_ = lean_ctor_get(v___y_591_, 2);
lean_inc_ref(v_options_594_);
v___x_595_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_options_594_, v___y_592_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops(uint8_t v_force_600_, lean_object* v_ctxt_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_config_605_; uint8_t v_singlePass_606_; 
v_config_605_ = lean_ctor_get(v_ctxt_601_, 0);
v_singlePass_606_ = lean_ctor_get_uint8(v_config_605_, sizeof(void*)*3 + 2);
if (v_singlePass_606_ == 0)
{
if (v_force_600_ == 0)
{
lean_object* v___x_607_; lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_618_; 
v___x_607_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_602_, v_a_603_);
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_618_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_618_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_612_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_613_ = l_Lean_Linter_getLinterValue(v___x_612_, v_a_608_);
lean_dec(v_a_608_);
v___x_614_ = lean_box(v___x_613_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_614_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(v_force_600_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
else
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = 0;
v___x_622_ = lean_box(v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops___boxed(lean_object* v_force_624_, lean_object* v_ctxt_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
uint8_t v_force_boxed_629_; lean_object* v_res_630_; 
v_force_boxed_629_ = lean_unbox(v_force_624_);
v_res_630_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_629_, v_ctxt_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec_ref(v_ctxt_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(lean_object* v_o_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_631_, v___y_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(lean_object* v_o_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(lean_object* v_k_641_, lean_object* v_b_642_, lean_object* v_c_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
v___x_649_ = lean_apply_7(v_k_641_, v_b_642_, v_c_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, lean_box(0));
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(lean_object* v_k_650_, lean_object* v_b_651_, lean_object* v_c_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_650_, v_b_651_, v_c_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(lean_object* v_type_659_, lean_object* v_k_660_, uint8_t v_cleanupAnnotations_661_, uint8_t v_whnfType_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; 
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_668_, 0, v_k_660_);
v___x_669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_659_, v___f_668_, v_cleanupAnnotations_661_, v_whnfType_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_669_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_669_);
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
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(lean_object* v_type_686_, lean_object* v_k_687_, lean_object* v_cleanupAnnotations_688_, lean_object* v_whnfType_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_695_; uint8_t v_whnfType_boxed_696_; lean_object* v_res_697_; 
v_cleanupAnnotations_boxed_695_ = lean_unbox(v_cleanupAnnotations_688_);
v_whnfType_boxed_696_ = lean_unbox(v_whnfType_689_);
v_res_697_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_686_, v_k_687_, v_cleanupAnnotations_boxed_695_, v_whnfType_boxed_696_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_object* v_00_u03b1_698_, lean_object* v_type_699_, lean_object* v_k_700_, uint8_t v_cleanupAnnotations_701_, uint8_t v_whnfType_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_699_, v_k_700_, v_cleanupAnnotations_701_, v_whnfType_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(lean_object* v_00_u03b1_709_, lean_object* v_type_710_, lean_object* v_k_711_, lean_object* v_cleanupAnnotations_712_, lean_object* v_whnfType_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_719_; uint8_t v_whnfType_boxed_720_; lean_object* v_res_721_; 
v_cleanupAnnotations_boxed_719_ = lean_unbox(v_cleanupAnnotations_712_);
v_whnfType_boxed_720_ = lean_unbox(v_whnfType_713_);
v_res_721_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(v_00_u03b1_709_, v_type_710_, v_k_711_, v_cleanupAnnotations_boxed_719_, v_whnfType_boxed_720_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(lean_object* v_msgData_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v_env_729_; lean_object* v___x_730_; lean_object* v_mctx_731_; lean_object* v_lctx_732_; lean_object* v_options_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_728_ = lean_st_ref_get(v___y_726_);
v_env_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc_ref(v_env_729_);
lean_dec(v___x_728_);
v___x_730_ = lean_st_ref_get(v___y_724_);
v_mctx_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_mctx_731_);
lean_dec(v___x_730_);
v_lctx_732_ = lean_ctor_get(v___y_723_, 2);
v_options_733_ = lean_ctor_get(v___y_725_, 2);
lean_inc_ref(v_options_733_);
lean_inc_ref(v_lctx_732_);
v___x_734_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_734_, 0, v_env_729_);
lean_ctor_set(v___x_734_, 1, v_mctx_731_);
lean_ctor_set(v___x_734_, 2, v_lctx_732_);
lean_ctor_set(v___x_734_, 3, v_options_733_);
v___x_735_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_msgData_722_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(lean_object* v_msgData_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_743_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_744_; double v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_float_of_nat(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(lean_object* v_cls_748_, lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_ref_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_801_; 
v_ref_755_ = lean_ctor_get(v___y_752_, 5);
v___x_756_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_801_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_801_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_801_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v_traceState_762_; lean_object* v_env_763_; lean_object* v_nextMacroScope_764_; lean_object* v_ngen_765_; lean_object* v_auxDeclNGen_766_; lean_object* v_cache_767_; lean_object* v_messages_768_; lean_object* v_infoState_769_; lean_object* v_snapshotTasks_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_800_; 
v___x_761_ = lean_st_ref_take(v___y_753_);
v_traceState_762_ = lean_ctor_get(v___x_761_, 4);
v_env_763_ = lean_ctor_get(v___x_761_, 0);
v_nextMacroScope_764_ = lean_ctor_get(v___x_761_, 1);
v_ngen_765_ = lean_ctor_get(v___x_761_, 2);
v_auxDeclNGen_766_ = lean_ctor_get(v___x_761_, 3);
v_cache_767_ = lean_ctor_get(v___x_761_, 5);
v_messages_768_ = lean_ctor_get(v___x_761_, 6);
v_infoState_769_ = lean_ctor_get(v___x_761_, 7);
v_snapshotTasks_770_ = lean_ctor_get(v___x_761_, 8);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_800_ == 0)
{
v___x_772_ = v___x_761_;
v_isShared_773_ = v_isSharedCheck_800_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_snapshotTasks_770_);
lean_inc(v_infoState_769_);
lean_inc(v_messages_768_);
lean_inc(v_cache_767_);
lean_inc(v_traceState_762_);
lean_inc(v_auxDeclNGen_766_);
lean_inc(v_ngen_765_);
lean_inc(v_nextMacroScope_764_);
lean_inc(v_env_763_);
lean_dec(v___x_761_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_800_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint64_t v_tid_774_; lean_object* v_traces_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_799_; 
v_tid_774_ = lean_ctor_get_uint64(v_traceState_762_, sizeof(void*)*1);
v_traces_775_ = lean_ctor_get(v_traceState_762_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_traceState_762_);
if (v_isSharedCheck_799_ == 0)
{
v___x_777_ = v_traceState_762_;
v_isShared_778_ = v_isSharedCheck_799_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_traces_775_);
lean_dec(v_traceState_762_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_799_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; double v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_779_ = lean_box(0);
v___x_780_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
v___x_781_ = 0;
v___x_782_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
v___x_783_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_783_, 0, v_cls_748_);
lean_ctor_set(v___x_783_, 1, v___x_779_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
lean_ctor_set_float(v___x_783_, sizeof(void*)*3, v___x_780_);
lean_ctor_set_float(v___x_783_, sizeof(void*)*3 + 8, v___x_780_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 16, v___x_781_);
v___x_784_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1));
v___x_785_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v_a_757_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
lean_inc(v_ref_755_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_ref_755_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_PersistentArray_push___redArg(v_traces_775_, v___x_786_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_787_);
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_787_);
lean_ctor_set_uint64(v_reuseFailAlloc_798_, sizeof(void*)*1, v_tid_774_);
v___x_789_ = v_reuseFailAlloc_798_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v___x_789_);
v___x_791_ = v___x_772_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_env_763_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_nextMacroScope_764_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_ngen_765_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_auxDeclNGen_766_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_797_, 5, v_cache_767_);
lean_ctor_set(v_reuseFailAlloc_797_, 6, v_messages_768_);
lean_ctor_set(v_reuseFailAlloc_797_, 7, v_infoState_769_);
lean_ctor_set(v_reuseFailAlloc_797_, 8, v_snapshotTasks_770_);
v___x_791_ = v_reuseFailAlloc_797_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = lean_st_ref_set(v___y_753_, v___x_791_);
v___x_793_ = lean_box(0);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_793_);
v___x_795_ = v___x_759_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(lean_object* v_cls_802_, lean_object* v_msg_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_802_, v_msg_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(lean_object* v_opts_810_, lean_object* v_opt_811_){
_start:
{
lean_object* v_name_812_; lean_object* v_defValue_813_; lean_object* v_map_814_; lean_object* v___x_815_; 
v_name_812_ = lean_ctor_get(v_opt_811_, 0);
v_defValue_813_ = lean_ctor_get(v_opt_811_, 1);
v_map_814_ = lean_ctor_get(v_opts_810_, 0);
v___x_815_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_814_, v_name_812_);
if (lean_obj_tag(v___x_815_) == 0)
{
uint8_t v___x_816_; 
v___x_816_ = lean_unbox(v_defValue_813_);
return v___x_816_;
}
else
{
lean_object* v_val_817_; 
v_val_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_817_);
lean_dec_ref(v___x_815_);
if (lean_obj_tag(v_val_817_) == 1)
{
uint8_t v_v_818_; 
v_v_818_ = lean_ctor_get_uint8(v_val_817_, 0);
lean_dec_ref(v_val_817_);
return v_v_818_;
}
else
{
uint8_t v___x_819_; 
lean_dec(v_val_817_);
v___x_819_ = lean_unbox(v_defValue_813_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_opts_820_, lean_object* v_opt_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_820_, v_opt_821_);
lean_dec_ref(v_opt_821_);
lean_dec_ref(v_opts_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v___y_832_, uint8_t v_suppressElabErrors_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 1)
{
lean_object* v_pre_835_; 
v_pre_835_ = lean_ctor_get(v_x_834_, 0);
switch(lean_obj_tag(v_pre_835_))
{
case 1:
{
lean_object* v_pre_836_; 
v_pre_836_ = lean_ctor_get(v_pre_835_, 0);
switch(lean_obj_tag(v_pre_836_))
{
case 0:
{
lean_object* v_str_837_; lean_object* v_str_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_str_837_ = lean_ctor_get(v_x_834_, 1);
v_str_838_ = lean_ctor_get(v_pre_835_, 1);
v___x_839_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_840_ = lean_string_dec_eq(v_str_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_842_ = lean_string_dec_eq(v_str_838_, v___x_841_);
if (v___x_842_ == 0)
{
return v___y_832_;
}
else
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_844_ = lean_string_dec_eq(v_str_837_, v___x_843_);
if (v___x_844_ == 0)
{
return v___y_832_;
}
else
{
return v_suppressElabErrors_833_;
}
}
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_846_ = lean_string_dec_eq(v_str_837_, v___x_845_);
if (v___x_846_ == 0)
{
return v___y_832_;
}
else
{
return v_suppressElabErrors_833_;
}
}
}
case 1:
{
lean_object* v_pre_847_; 
v_pre_847_ = lean_ctor_get(v_pre_836_, 0);
if (lean_obj_tag(v_pre_847_) == 0)
{
lean_object* v_str_848_; lean_object* v_str_849_; lean_object* v_str_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_str_848_ = lean_ctor_get(v_x_834_, 1);
v_str_849_ = lean_ctor_get(v_pre_835_, 1);
v_str_850_ = lean_ctor_get(v_pre_836_, 1);
v___x_851_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_852_ = lean_string_dec_eq(v_str_850_, v___x_851_);
if (v___x_852_ == 0)
{
return v___y_832_;
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_854_ = lean_string_dec_eq(v_str_849_, v___x_853_);
if (v___x_854_ == 0)
{
return v___y_832_;
}
else
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_856_ = lean_string_dec_eq(v_str_848_, v___x_855_);
if (v___x_856_ == 0)
{
return v___y_832_;
}
else
{
return v_suppressElabErrors_833_;
}
}
}
}
else
{
return v___y_832_;
}
}
default: 
{
return v___y_832_;
}
}
}
case 0:
{
lean_object* v_str_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_str_857_ = lean_ctor_get(v_x_834_, 1);
v___x_858_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_859_ = lean_string_dec_eq(v_str_857_, v___x_858_);
if (v___x_859_ == 0)
{
return v___y_832_;
}
else
{
return v_suppressElabErrors_833_;
}
}
default: 
{
return v___y_832_;
}
}
}
else
{
return v___y_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_860_, lean_object* v_suppressElabErrors_861_, lean_object* v_x_862_){
_start:
{
uint8_t v___y_24902__boxed_863_; uint8_t v_suppressElabErrors_boxed_864_; uint8_t v_res_865_; lean_object* v_r_866_; 
v___y_24902__boxed_863_ = lean_unbox(v___y_860_);
v_suppressElabErrors_boxed_864_ = lean_unbox(v_suppressElabErrors_861_);
v_res_865_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v___y_24902__boxed_863_, v_suppressElabErrors_boxed_864_, v_x_862_);
lean_dec(v_x_862_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_867_, lean_object* v_msgData_868_, uint8_t v_severity_869_, uint8_t v_isSilent_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; uint8_t v___y_881_; uint8_t v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; uint8_t v___y_916_; uint8_t v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v___y_941_; uint8_t v___y_942_; uint8_t v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; uint8_t v___y_952_; uint8_t v___y_953_; lean_object* v___y_954_; uint8_t v___y_955_; uint8_t v___x_960_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; uint8_t v___y_965_; lean_object* v___y_966_; uint8_t v___y_967_; uint8_t v___y_968_; uint8_t v___y_970_; uint8_t v___x_985_; 
v___x_960_ = 2;
v___x_985_ = l_Lean_instBEqMessageSeverity_beq(v_severity_869_, v___x_960_);
if (v___x_985_ == 0)
{
v___y_970_ = v___x_985_;
goto v___jp_969_;
}
else
{
uint8_t v___x_986_; 
lean_inc_ref(v_msgData_868_);
v___x_986_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_868_);
v___y_970_ = v___x_986_;
goto v___jp_969_;
}
v___jp_876_:
{
lean_object* v___x_886_; lean_object* v_currNamespace_887_; lean_object* v_openDecls_888_; lean_object* v_env_889_; lean_object* v_nextMacroScope_890_; lean_object* v_ngen_891_; lean_object* v_auxDeclNGen_892_; lean_object* v_traceState_893_; lean_object* v_cache_894_; lean_object* v_messages_895_; lean_object* v_infoState_896_; lean_object* v_snapshotTasks_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_911_; 
v___x_886_ = lean_st_ref_take(v___y_885_);
v_currNamespace_887_ = lean_ctor_get(v___y_884_, 6);
v_openDecls_888_ = lean_ctor_get(v___y_884_, 7);
v_env_889_ = lean_ctor_get(v___x_886_, 0);
v_nextMacroScope_890_ = lean_ctor_get(v___x_886_, 1);
v_ngen_891_ = lean_ctor_get(v___x_886_, 2);
v_auxDeclNGen_892_ = lean_ctor_get(v___x_886_, 3);
v_traceState_893_ = lean_ctor_get(v___x_886_, 4);
v_cache_894_ = lean_ctor_get(v___x_886_, 5);
v_messages_895_ = lean_ctor_get(v___x_886_, 6);
v_infoState_896_ = lean_ctor_get(v___x_886_, 7);
v_snapshotTasks_897_ = lean_ctor_get(v___x_886_, 8);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_911_ == 0)
{
v___x_899_ = v___x_886_;
v_isShared_900_ = v_isSharedCheck_911_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_snapshotTasks_897_);
lean_inc(v_infoState_896_);
lean_inc(v_messages_895_);
lean_inc(v_cache_894_);
lean_inc(v_traceState_893_);
lean_inc(v_auxDeclNGen_892_);
lean_inc(v_ngen_891_);
lean_inc(v_nextMacroScope_890_);
lean_inc(v_env_889_);
lean_dec(v___x_886_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_911_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_inc(v_openDecls_888_);
lean_inc(v_currNamespace_887_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_currNamespace_887_);
lean_ctor_set(v___x_901_, 1, v_openDecls_888_);
v___x_902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___y_878_);
lean_inc_ref(v___y_879_);
lean_inc_ref(v___y_883_);
v___x_903_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_903_, 0, v___y_883_);
lean_ctor_set(v___x_903_, 1, v___y_880_);
lean_ctor_set(v___x_903_, 2, v___y_877_);
lean_ctor_set(v___x_903_, 3, v___y_879_);
lean_ctor_set(v___x_903_, 4, v___x_902_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*5, v___y_881_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*5 + 1, v___y_882_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*5 + 2, v_isSilent_870_);
v___x_904_ = l_Lean_MessageLog_add(v___x_903_, v_messages_895_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 6, v___x_904_);
v___x_906_ = v___x_899_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_env_889_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_nextMacroScope_890_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_ngen_891_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_auxDeclNGen_892_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_traceState_893_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v_cache_894_);
lean_ctor_set(v_reuseFailAlloc_910_, 6, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 7, v_infoState_896_);
lean_ctor_set(v_reuseFailAlloc_910_, 8, v_snapshotTasks_897_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_st_ref_set(v___y_885_, v___x_906_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
v___jp_912_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_936_; 
v___x_921_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_868_);
v___x_922_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_921_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_936_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc_ref_n(v___y_915_, 2);
v___x_927_ = l_Lean_FileMap_toPosition(v___y_915_, v___y_914_);
lean_dec(v___y_914_);
v___x_928_ = l_Lean_FileMap_toPosition(v___y_915_, v___y_920_);
lean_dec(v___y_920_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
if (v___y_916_ == 0)
{
lean_del_object(v___x_925_);
lean_dec_ref(v___y_913_);
v___y_877_ = v___x_929_;
v___y_878_ = v_a_923_;
v___y_879_ = v___x_930_;
v___y_880_ = v___x_927_;
v___y_881_ = v___y_917_;
v___y_882_ = v___y_918_;
v___y_883_ = v___y_919_;
v___y_884_ = v___y_873_;
v___y_885_ = v___y_874_;
goto v___jp_876_;
}
else
{
uint8_t v___x_931_; 
lean_inc(v_a_923_);
v___x_931_ = l_Lean_MessageData_hasTag(v___y_913_, v_a_923_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec_ref(v___x_929_);
lean_dec_ref(v___x_927_);
lean_dec(v_a_923_);
v___x_932_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_932_);
v___x_934_ = v___x_925_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_del_object(v___x_925_);
v___y_877_ = v___x_929_;
v___y_878_ = v_a_923_;
v___y_879_ = v___x_930_;
v___y_880_ = v___x_927_;
v___y_881_ = v___y_917_;
v___y_882_ = v___y_918_;
v___y_883_ = v___y_919_;
v___y_884_ = v___y_873_;
v___y_885_ = v___y_874_;
goto v___jp_876_;
}
}
}
}
v___jp_937_:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Syntax_getTailPos_x3f(v___y_939_, v___y_941_);
lean_dec(v___y_939_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_inc(v___y_945_);
v___y_913_ = v___y_938_;
v___y_914_ = v___y_945_;
v___y_915_ = v___y_940_;
v___y_916_ = v___y_942_;
v___y_917_ = v___y_941_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v___y_945_;
goto v___jp_912_;
}
else
{
lean_object* v_val_947_; 
v_val_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_val_947_);
lean_dec_ref(v___x_946_);
v___y_913_ = v___y_938_;
v___y_914_ = v___y_945_;
v___y_915_ = v___y_940_;
v___y_916_ = v___y_942_;
v___y_917_ = v___y_941_;
v___y_918_ = v___y_943_;
v___y_919_ = v___y_944_;
v___y_920_ = v_val_947_;
goto v___jp_912_;
}
}
v___jp_948_:
{
lean_object* v_ref_956_; lean_object* v___x_957_; 
v_ref_956_ = l_Lean_replaceRef(v_ref_867_, v___y_950_);
v___x_957_ = l_Lean_Syntax_getPos_x3f(v_ref_956_, v___y_953_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___y_938_ = v___y_949_;
v___y_939_ = v_ref_956_;
v___y_940_ = v___y_951_;
v___y_941_ = v___y_953_;
v___y_942_ = v___y_952_;
v___y_943_ = v___y_955_;
v___y_944_ = v___y_954_;
v___y_945_ = v___x_958_;
goto v___jp_937_;
}
else
{
lean_object* v_val_959_; 
v_val_959_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_val_959_);
lean_dec_ref(v___x_957_);
v___y_938_ = v___y_949_;
v___y_939_ = v_ref_956_;
v___y_940_ = v___y_951_;
v___y_941_ = v___y_953_;
v___y_942_ = v___y_952_;
v___y_943_ = v___y_955_;
v___y_944_ = v___y_954_;
v___y_945_ = v_val_959_;
goto v___jp_937_;
}
}
v___jp_961_:
{
if (v___y_968_ == 0)
{
v___y_949_ = v___y_964_;
v___y_950_ = v___y_962_;
v___y_951_ = v___y_963_;
v___y_952_ = v___y_965_;
v___y_953_ = v___y_967_;
v___y_954_ = v___y_966_;
v___y_955_ = v_severity_869_;
goto v___jp_948_;
}
else
{
v___y_949_ = v___y_964_;
v___y_950_ = v___y_962_;
v___y_951_ = v___y_963_;
v___y_952_ = v___y_965_;
v___y_953_ = v___y_967_;
v___y_954_ = v___y_966_;
v___y_955_ = v___x_960_;
goto v___jp_948_;
}
}
v___jp_969_:
{
if (v___y_970_ == 0)
{
lean_object* v_fileName_971_; lean_object* v_fileMap_972_; lean_object* v_options_973_; lean_object* v_ref_974_; uint8_t v_suppressElabErrors_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___f_978_; uint8_t v___x_979_; uint8_t v___x_980_; 
v_fileName_971_ = lean_ctor_get(v___y_873_, 0);
v_fileMap_972_ = lean_ctor_get(v___y_873_, 1);
v_options_973_ = lean_ctor_get(v___y_873_, 2);
v_ref_974_ = lean_ctor_get(v___y_873_, 5);
v_suppressElabErrors_975_ = lean_ctor_get_uint8(v___y_873_, sizeof(void*)*14 + 1);
v___x_976_ = lean_box(v___y_970_);
v___x_977_ = lean_box(v_suppressElabErrors_975_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_978_, 0, v___x_976_);
lean_closure_set(v___f_978_, 1, v___x_977_);
v___x_979_ = 1;
v___x_980_ = l_Lean_instBEqMessageSeverity_beq(v_severity_869_, v___x_979_);
if (v___x_980_ == 0)
{
v___y_962_ = v_ref_974_;
v___y_963_ = v_fileMap_972_;
v___y_964_ = v___f_978_;
v___y_965_ = v_suppressElabErrors_975_;
v___y_966_ = v_fileName_971_;
v___y_967_ = v___y_970_;
v___y_968_ = v___x_980_;
goto v___jp_961_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_warningAsError;
v___x_982_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_options_973_, v___x_981_);
v___y_962_ = v_ref_974_;
v___y_963_ = v_fileMap_972_;
v___y_964_ = v___f_978_;
v___y_965_ = v_suppressElabErrors_975_;
v___y_966_ = v_fileName_971_;
v___y_967_ = v___y_970_;
v___y_968_ = v___x_982_;
goto v___jp_961_;
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref(v_msgData_868_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_987_, lean_object* v_msgData_988_, lean_object* v_severity_989_, lean_object* v_isSilent_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v_severity_boxed_996_; uint8_t v_isSilent_boxed_997_; lean_object* v_res_998_; 
v_severity_boxed_996_ = lean_unbox(v_severity_989_);
v_isSilent_boxed_997_ = lean_unbox(v_isSilent_990_);
v_res_998_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_987_, v_msgData_988_, v_severity_boxed_996_, v_isSilent_boxed_997_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v_ref_987_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(lean_object* v_ref_999_, lean_object* v_msgData_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = 1;
v___x_1010_ = 0;
v___x_1011_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_999_, v_msgData_1000_, v___x_1009_, v___x_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(lean_object* v_ref_1012_, lean_object* v_msgData_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_1012_, v_msgData_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec(v_ref_1012_);
return v_res_1022_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(lean_object* v_linterOption_1029_, lean_object* v_stx_1030_, lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_name_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1055_; 
v_name_1040_ = lean_ctor_get(v_linterOption_1029_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_linterOption_1029_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_linterOption_1029_, 1);
lean_dec(v_unused_1056_);
v___x_1042_ = v_linterOption_1029_;
v_isShared_1043_ = v_isSharedCheck_1055_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_name_1040_);
lean_dec(v_linterOption_1029_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1055_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1044_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
lean_inc(v_name_1040_);
v___x_1045_ = l_Lean_MessageData_ofName(v_name_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 7);
lean_ctor_set(v___x_1042_, 1, v___x_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_disable_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1048_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v_disable_1050_ = l_Lean_MessageData_note(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_msg_1031_);
lean_ctor_set(v___x_1051_, 1, v_disable_1050_);
v___x_1052_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_name_1040_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_1030_, v___x_1052_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(lean_object* v_linterOption_1057_, lean_object* v_stx_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v_linterOption_1057_, v_stx_1058_, v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v_stx_1058_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(lean_object* v_msgData_1069_, uint8_t v_severity_1070_, uint8_t v_isSilent_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_ref_1080_; lean_object* v___x_1081_; 
v_ref_1080_ = lean_ctor_get(v___y_1077_, 5);
v___x_1081_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1080_, v_msgData_1069_, v_severity_1070_, v_isSilent_1071_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(lean_object* v_msgData_1082_, lean_object* v_severity_1083_, lean_object* v_isSilent_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_severity_boxed_1093_; uint8_t v_isSilent_boxed_1094_; lean_object* v_res_1095_; 
v_severity_boxed_1093_ = lean_unbox(v_severity_1083_);
v_isSilent_boxed_1094_ = lean_unbox(v_isSilent_1084_);
v_res_1095_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1082_, v_severity_boxed_1093_, v_isSilent_boxed_1094_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(lean_object* v_msgData_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = 1;
v___x_1106_ = 0;
v___x_1107_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1096_, v___x_1105_, v___x_1106_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(lean_object* v_msgData_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_msgData_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
return v_res_1117_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3));
v___x_1129_ = l_Lean_Name_append(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(lean_object* v___x_1136_, uint8_t v_force_1137_, lean_object* v_thm_1138_, lean_object* v_origin_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___x_1180_; 
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
v___x_1180_ = lean_simp(v___x_1136_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___y_1140_);
lean_dec_ref(v_origin_1139_);
lean_dec_ref(v_thm_1138_);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v___x_1180_, 0);
lean_dec(v_unused_1189_);
v___x_1182_ = v___x_1180_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_dec(v___x_1180_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1214_; 
v_a_1190_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1192_ = v___x_1180_;
v_isShared_1193_ = v_isSharedCheck_1214_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1180_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1214_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
uint8_t v___x_1194_; 
v___x_1194_ = l_Lean_Exception_isInterrupt(v_a_1190_);
if (v___x_1194_ == 0)
{
lean_object* v_options_1195_; uint8_t v_hasTrace_1196_; 
lean_del_object(v___x_1192_);
v_options_1195_ = lean_ctor_get(v___y_1145_, 2);
v_hasTrace_1196_ = lean_ctor_get_uint8(v_options_1195_, sizeof(void*)*1);
if (v_hasTrace_1196_ == 0)
{
lean_dec(v_a_1190_);
lean_dec_ref(v_origin_1139_);
v___y_1149_ = v___y_1140_;
v___y_1150_ = v___y_1141_;
v___y_1151_ = v___y_1142_;
v___y_1152_ = v___y_1143_;
v___y_1153_ = v___y_1144_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___y_1146_;
goto v___jp_1148_;
}
else
{
lean_object* v_inheritedTraceOptions_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_inheritedTraceOptions_1197_ = lean_ctor_get(v___y_1145_, 13);
v___x_1198_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4);
v___x_1200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1197_, v_options_1195_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_a_1190_);
lean_dec_ref(v_origin_1139_);
v___y_1149_ = v___y_1140_;
v___y_1150_ = v___y_1141_;
v___y_1151_ = v___y_1142_;
v___y_1152_ = v___y_1143_;
v___y_1153_ = v___y_1144_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___y_1146_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1201_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_1139_);
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
v___x_1207_ = l_Lean_Exception_toMessageData(v_a_1190_);
v___x_1208_ = l_Lean_indentD(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v___x_1198_, v___x_1209_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_dec_ref(v___x_1210_);
v___y_1149_ = v___y_1140_;
v___y_1150_ = v___y_1141_;
v___y_1151_ = v___y_1142_;
v___y_1152_ = v___y_1143_;
v___y_1153_ = v___y_1144_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___y_1146_;
goto v___jp_1148_;
}
else
{
lean_dec(v___y_1140_);
lean_dec_ref(v_thm_1138_);
return v___x_1210_;
}
}
}
}
else
{
lean_object* v___x_1212_; 
lean_dec(v___y_1140_);
lean_dec_ref(v_origin_1139_);
lean_dec_ref(v_thm_1138_);
if (v_isShared_1193_ == 0)
{
v___x_1212_ = v___x_1192_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1190_);
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
v___jp_1148_:
{
if (v_force_1137_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1138_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v_ref_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v_ref_1158_ = lean_ctor_get(v___y_1154_, 5);
v___x_1159_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_1160_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v___x_1159_, v_ref_1158_, v_a_1157_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1149_);
return v___x_1160_;
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v___y_1149_);
v_a_1161_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1156_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1156_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
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
else
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1138_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_a_1170_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1149_);
return v___x_1171_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v___y_1149_);
v_a_1172_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1169_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___boxed(lean_object* v___x_1215_, lean_object* v_force_1216_, lean_object* v_thm_1217_, lean_object* v_origin_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_force_boxed_1227_; lean_object* v_res_1228_; 
v_force_boxed_1227_ = lean_unbox(v_force_1216_);
v_res_1228_ = l_Lean_Meta_Simp_checkLoops___lam__0(v___x_1215_, v_force_boxed_1227_, v_thm_1217_, v_origin_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
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
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(32u);
v___x_1242_ = lean_mk_empty_array_with_capacity(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6(void){
_start:
{
size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1244_ = ((size_t)5ULL);
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_unsigned_to_nat(32u);
v___x_1247_ = lean_mk_empty_array_with_capacity(v___x_1246_);
v___x_1248_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__5, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5);
v___x_1249_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
lean_ctor_set(v___x_1249_, 2, v___x_1245_);
lean_ctor_set(v___x_1249_, 3, v___x_1245_);
lean_ctor_set_usize(v___x_1249_, 4, v___x_1244_);
return v___x_1249_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6);
v___x_1251_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
lean_ctor_set(v___x_1252_, 2, v___x_1251_);
lean_ctor_set(v___x_1252_, 3, v___x_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1(uint8_t v_force_1253_, lean_object* v_thm_1254_, lean_object* v_origin_1255_, uint8_t v_a_1256_, lean_object* v_ctxt_1257_, lean_object* v_methods_1258_, lean_object* v___xs_1259_, lean_object* v_type_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
v___x_1266_ = lean_whnf(v_type_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = l_Lean_Expr_appArg_x21(v_a_1267_);
lean_dec(v_a_1267_);
v___x_1269_ = lean_box(v_force_1253_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1270_, 0, v___x_1268_);
lean_closure_set(v___f_1270_, 1, v___x_1269_);
lean_closure_set(v___f_1270_, 2, v_thm_1254_);
lean_closure_set(v___f_1270_, 3, v_origin_1255_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__1, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1);
v___x_1273_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1274_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*2, v_a_1256_);
v___x_1275_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4);
v___x_1276_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__7, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7);
v___x_1277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1274_);
lean_ctor_set(v___x_1277_, 1, v___x_1272_);
lean_ctor_set(v___x_1277_, 2, v___x_1272_);
lean_ctor_set(v___x_1277_, 3, v___x_1275_);
lean_ctor_set(v___x_1277_, 4, v___x_1271_);
lean_ctor_set(v___x_1277_, 5, v___x_1276_);
v___x_1278_ = l_Lean_Meta_Simp_SimpM_run___redArg(v_ctxt_1257_, v___x_1277_, v_methods_1258_, v___f_1270_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1278_, 0);
lean_dec(v_unused_1287_);
v___x_1280_ = v___x_1278_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_dec(v___x_1278_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(0);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1278_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1278_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_methods_1258_);
lean_dec_ref(v_ctxt_1257_);
lean_dec_ref(v_origin_1255_);
lean_dec_ref(v_thm_1254_);
v_a_1296_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1266_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1266_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___boxed(lean_object* v_force_1304_, lean_object* v_thm_1305_, lean_object* v_origin_1306_, lean_object* v_a_1307_, lean_object* v_ctxt_1308_, lean_object* v_methods_1309_, lean_object* v___xs_1310_, lean_object* v_type_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v_force_boxed_1317_; uint8_t v_a_25605__boxed_1318_; lean_object* v_res_1319_; 
v_force_boxed_1317_ = lean_unbox(v_force_1304_);
v_a_25605__boxed_1318_ = lean_unbox(v_a_1307_);
v_res_1319_ = l_Lean_Meta_Simp_checkLoops___lam__1(v_force_boxed_1317_, v_thm_1305_, v_origin_1306_, v_a_25605__boxed_1318_, v_ctxt_1308_, v_methods_1309_, v___xs_1310_, v_type_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___xs_1310_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops(uint8_t v_force_1320_, lean_object* v_ctxt_1321_, lean_object* v_methods_1322_, lean_object* v_thm_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_1320_, v_ctxt_1321_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1369_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1369_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1369_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_unbox(v_a_1330_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec(v_a_1330_);
lean_dec_ref(v_thm_1323_);
lean_dec_ref(v_methods_1322_);
lean_dec_ref(v_ctxt_1321_);
v___x_1335_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1335_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v_proof_1339_; lean_object* v_origin_1340_; uint8_t v___x_1341_; 
v_proof_1339_ = lean_ctor_get(v_thm_1323_, 2);
v_origin_1340_ = lean_ctor_get(v_thm_1323_, 4);
lean_inc_ref(v_origin_1340_);
v___x_1341_ = l_Lean_Expr_hasFVar(v_proof_1339_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_del_object(v___x_1332_);
lean_inc_ref(v_thm_1323_);
v___x_1342_ = l_Lean_Meta_SimpTheorem_getValue(v_thm_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1342_);
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
v___x_1344_ = lean_infer_type(v_a_1343_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = lean_box(v_force_1320_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1347_, 0, v___x_1346_);
lean_closure_set(v___f_1347_, 1, v_thm_1323_);
lean_closure_set(v___f_1347_, 2, v_origin_1340_);
lean_closure_set(v___f_1347_, 3, v_a_1330_);
lean_closure_set(v___f_1347_, 4, v_ctxt_1321_);
lean_closure_set(v___f_1347_, 5, v_methods_1322_);
v___x_1348_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_1345_, v___f_1347_, v___x_1341_, v___x_1341_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1348_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_origin_1340_);
lean_dec(v_a_1330_);
lean_dec_ref(v_thm_1323_);
lean_dec_ref(v_methods_1322_);
lean_dec_ref(v_ctxt_1321_);
v_a_1349_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1344_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1344_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_origin_1340_);
lean_dec(v_a_1330_);
lean_dec_ref(v_thm_1323_);
lean_dec_ref(v_methods_1322_);
lean_dec_ref(v_ctxt_1321_);
v_a_1357_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1342_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1342_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec_ref(v_origin_1340_);
lean_dec(v_a_1330_);
lean_dec_ref(v_thm_1323_);
lean_dec_ref(v_methods_1322_);
lean_dec_ref(v_ctxt_1321_);
v___x_1365_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1365_);
v___x_1367_ = v___x_1332_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_thm_1323_);
lean_dec_ref(v_methods_1322_);
lean_dec_ref(v_ctxt_1321_);
v_a_1370_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1329_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1329_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
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
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___boxed(lean_object* v_force_1378_, lean_object* v_ctxt_1379_, lean_object* v_methods_1380_, lean_object* v_thm_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
uint8_t v_force_boxed_1387_; lean_object* v_res_1388_; 
v_force_boxed_1387_ = lean_unbox(v_force_1378_);
v_res_1388_ = l_Lean_Meta_Simp_checkLoops(v_force_boxed_1387_, v_ctxt_1379_, v_methods_1380_, v_thm_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(lean_object* v_cls_1389_, lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_1389_, v_msg_1390_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(lean_object* v_cls_1400_, lean_object* v_msg_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(v_cls_1400_, v_msg_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(lean_object* v_ref_1411_, lean_object* v_msgData_1412_, uint8_t v_severity_1413_, uint8_t v_isSilent_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1411_, v_msgData_1412_, v_severity_1413_, v_isSilent_1414_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_1424_, lean_object* v_msgData_1425_, lean_object* v_severity_1426_, lean_object* v_isSilent_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
uint8_t v_severity_boxed_1436_; uint8_t v_isSilent_boxed_1437_; lean_object* v_res_1438_; 
v_severity_boxed_1436_ = lean_unbox(v_severity_1426_);
v_isSilent_boxed_1437_ = lean_unbox(v_isSilent_1427_);
v_res_1438_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_1424_, v_msgData_1425_, v_severity_boxed_1436_, v_isSilent_boxed_1437_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec(v_ref_1424_);
return v_res_1438_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
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
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_LoopProtection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
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

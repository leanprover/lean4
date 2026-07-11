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
uint8_t lean_bool_not(uint8_t);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_r_117_, 1);
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
lean_dec_ref_known(v_r_184_, 1);
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
lean_object* v_a_448_; uint8_t v___y_450_; 
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
v___y_450_ = v___x_457_;
goto v___jp_449_;
}
else
{
if (v_inv_454_ == 0)
{
if (v_inv_456_ == 0)
{
v___y_450_ = v___x_457_;
goto v___jp_449_;
}
else
{
v___y_450_ = v_inv_454_;
goto v___jp_449_;
}
}
else
{
v___y_450_ = v_inv_456_;
goto v___jp_449_;
}
}
}
else
{
uint8_t v___x_458_; 
v___x_458_ = 0;
v___y_450_ = v___x_458_;
goto v___jp_449_;
}
}
else
{
if (lean_obj_tag(v___x_435_) == 0)
{
uint8_t v___x_459_; 
v___x_459_ = 0;
v___y_450_ = v___x_459_;
goto v___jp_449_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = l_Lean_Meta_Origin_key(v_a_448_);
v___x_461_ = l_Lean_Meta_Origin_key(v___x_435_);
v___x_462_ = lean_name_eq(v___x_460_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v___x_460_);
v___y_450_ = v___x_462_;
goto v___jp_449_;
}
}
v___jp_449_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_bool_not(v___y_450_);
if (v___x_451_ == 0)
{
v_a_442_ = v_b_439_;
goto v___jp_441_;
}
else
{
lean_object* v___x_452_; 
lean_inc(v_a_448_);
v___x_452_ = lean_array_push(v_b_439_, v_a_448_);
v_a_442_ = v___x_452_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(lean_object* v___x_463_, lean_object* v_as_464_, lean_object* v_sz_465_, lean_object* v_i_466_, lean_object* v_b_467_, lean_object* v___y_468_){
_start:
{
size_t v_sz_boxed_469_; size_t v_i_boxed_470_; lean_object* v_res_471_; 
v_sz_boxed_469_ = lean_unbox_usize(v_sz_465_);
lean_dec(v_sz_465_);
v_i_boxed_470_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_463_, v_as_464_, v_sz_boxed_469_, v_i_boxed_470_, v_b_467_);
lean_dec_ref(v_as_464_);
lean_dec_ref(v___x_463_);
return v_res_471_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1);
v___x_476_ = l_Lean_MessageData_hint_x27(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5(void){
_start:
{
lean_object* v___x_480_; lean_object* v_msg_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
v_msg_481_ = l_Lean_stringToMessageData(v___x_480_);
return v_msg_481_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg(lean_object* v_thm_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_msg_498_; lean_object* v_origin_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_505_; lean_object* v_usedTheorems_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; size_t v_sz_510_; size_t v___x_511_; lean_object* v___x_512_; 
v_origin_502_ = lean_ctor_get(v_thm_488_, 4);
lean_inc_ref_n(v_origin_502_, 2);
lean_dec_ref(v_thm_488_);
v___x_503_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_502_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = lean_st_ref_get(v_a_491_);
v_usedTheorems_506_ = lean_ctor_get(v___x_505_, 3);
lean_inc_ref(v_usedTheorems_506_);
lean_dec(v___x_505_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v___x_509_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_506_);
lean_dec_ref(v_usedTheorems_506_);
v_sz_510_ = lean_array_size(v___x_509_);
v___x_511_ = ((size_t)0ULL);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_502_, v___x_509_, v_sz_510_, v___x_511_, v___x_508_);
lean_dec_ref(v___x_509_);
lean_dec_ref(v_origin_502_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v_msg_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v_msg_514_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5);
v___x_515_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v_a_504_);
v___x_517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v_msg_514_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_array_get_size(v_a_513_);
v___x_521_ = lean_nat_dec_eq(v___x_520_, v___x_507_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_513_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_a_523_);
v___x_526_ = l_Lean_MessageData_note(v___x_525_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_519_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v_msg_498_ = v___x_527_;
goto v___jp_497_;
}
else
{
lean_dec_ref_known(v___x_519_, 2);
return v___x_522_;
}
}
else
{
lean_dec(v_a_513_);
v_msg_498_ = v___x_519_;
goto v___jp_497_;
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_a_504_);
v_a_528_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_512_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_512_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v_msg_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(lean_object* v_thm_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(lean_object* v___x_546_, lean_object* v_as_547_, size_t v_sz_548_, size_t v_i_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_546_, v_as_547_, v_sz_548_, v_i_549_, v_b_550_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(lean_object* v___x_560_, lean_object* v_as_561_, lean_object* v_sz_562_, lean_object* v_i_563_, lean_object* v_b_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v_sz_boxed_573_ = lean_unbox_usize(v_sz_562_);
lean_dec(v_sz_562_);
v_i_boxed_574_ = lean_unbox_usize(v_i_563_);
lean_dec(v_i_563_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_560_, v_as_561_, v_sz_boxed_573_, v_i_boxed_574_, v_b_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v_as_561_);
lean_dec_ref(v___x_560_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(lean_object* v_o_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v_env_580_; lean_object* v___x_581_; lean_object* v_toEnvExtension_582_; lean_object* v_asyncMode_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_merged_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v___x_579_ = lean_st_ref_get(v___y_577_);
v_env_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_env_580_);
lean_dec(v___x_579_);
v___x_581_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_582_ = lean_ctor_get(v___x_581_, 0);
v_asyncMode_583_ = lean_ctor_get(v_toEnvExtension_582_, 2);
v___x_584_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_585_ = lean_box(0);
v___x_586_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_584_, v___x_581_, v_env_580_, v_asyncMode_583_, v___x_585_);
v_merged_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_586_, 1);
lean_dec(v_unused_596_);
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_merged_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_merged_587_);
lean_ctor_set(v___x_589_, 0, v_o_576_);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_o_576_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_merged_587_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(lean_object* v_o_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_597_, v___y_598_);
lean_dec(v___y_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_options_604_; lean_object* v___x_605_; 
v_options_604_ = lean_ctor_get(v___y_601_, 2);
lean_inc_ref(v_options_604_);
v___x_605_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_options_604_, v___y_602_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops(uint8_t v_force_610_, lean_object* v_ctxt_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_config_615_; uint8_t v_singlePass_616_; 
v_config_615_ = lean_ctor_get(v_ctxt_611_, 0);
v_singlePass_616_ = lean_ctor_get_uint8(v_config_615_, sizeof(void*)*3 + 2);
if (v_singlePass_616_ == 0)
{
if (v_force_610_ == 0)
{
lean_object* v___x_617_; lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_628_; 
v___x_617_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_612_, v_a_613_);
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_628_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_622_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_623_ = l_Lean_Linter_getLinterValue(v___x_622_, v_a_618_);
lean_dec(v_a_618_);
v___x_624_ = lean_box(v___x_623_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(v_force_610_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
else
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = 0;
v___x_632_ = lean_box(v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops___boxed(lean_object* v_force_634_, lean_object* v_ctxt_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
uint8_t v_force_boxed_639_; lean_object* v_res_640_; 
v_force_boxed_639_ = lean_unbox(v_force_634_);
v_res_640_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_639_, v_ctxt_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_ctxt_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(lean_object* v_o_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_641_, v___y_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(lean_object* v_o_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(lean_object* v_k_651_, lean_object* v_b_652_, lean_object* v_c_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
v___x_659_ = lean_apply_7(v_k_651_, v_b_652_, v_c_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, lean_box(0));
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(lean_object* v_k_660_, lean_object* v_b_661_, lean_object* v_c_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_660_, v_b_661_, v_c_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(lean_object* v_type_669_, lean_object* v_k_670_, uint8_t v_cleanupAnnotations_671_, uint8_t v_whnfType_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___f_678_; lean_object* v___x_679_; 
v___f_678_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_678_, 0, v_k_670_);
v___x_679_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_669_, v___f_678_, v_cleanupAnnotations_671_, v_whnfType_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_688_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_679_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_679_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(lean_object* v_type_696_, lean_object* v_k_697_, lean_object* v_cleanupAnnotations_698_, lean_object* v_whnfType_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_705_; uint8_t v_whnfType_boxed_706_; lean_object* v_res_707_; 
v_cleanupAnnotations_boxed_705_ = lean_unbox(v_cleanupAnnotations_698_);
v_whnfType_boxed_706_ = lean_unbox(v_whnfType_699_);
v_res_707_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_696_, v_k_697_, v_cleanupAnnotations_boxed_705_, v_whnfType_boxed_706_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_object* v_00_u03b1_708_, lean_object* v_type_709_, lean_object* v_k_710_, uint8_t v_cleanupAnnotations_711_, uint8_t v_whnfType_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_709_, v_k_710_, v_cleanupAnnotations_711_, v_whnfType_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(lean_object* v_00_u03b1_719_, lean_object* v_type_720_, lean_object* v_k_721_, lean_object* v_cleanupAnnotations_722_, lean_object* v_whnfType_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_729_; uint8_t v_whnfType_boxed_730_; lean_object* v_res_731_; 
v_cleanupAnnotations_boxed_729_ = lean_unbox(v_cleanupAnnotations_722_);
v_whnfType_boxed_730_ = lean_unbox(v_whnfType_723_);
v_res_731_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(v_00_u03b1_719_, v_type_720_, v_k_721_, v_cleanupAnnotations_boxed_729_, v_whnfType_boxed_730_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(lean_object* v_msgData_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v___x_740_; lean_object* v_mctx_741_; lean_object* v_lctx_742_; lean_object* v_options_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_738_ = lean_st_ref_get(v___y_736_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_738_);
v___x_740_ = lean_st_ref_get(v___y_734_);
v_mctx_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_mctx_741_);
lean_dec(v___x_740_);
v_lctx_742_ = lean_ctor_get(v___y_733_, 2);
v_options_743_ = lean_ctor_get(v___y_735_, 2);
lean_inc_ref(v_options_743_);
lean_inc_ref(v_lctx_742_);
v___x_744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_744_, 0, v_env_739_);
lean_ctor_set(v___x_744_, 1, v_mctx_741_);
lean_ctor_set(v___x_744_, 2, v_lctx_742_);
lean_ctor_set(v___x_744_, 3, v_options_743_);
v___x_745_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v_msgData_732_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(lean_object* v_msgData_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_754_; double v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_float_of_nat(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(lean_object* v_cls_758_, lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_ref_765_; lean_object* v___x_766_; lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_811_; 
v_ref_765_ = lean_ctor_get(v___y_762_, 5);
v___x_766_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_811_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_811_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_811_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v_traceState_772_; lean_object* v_env_773_; lean_object* v_nextMacroScope_774_; lean_object* v_ngen_775_; lean_object* v_auxDeclNGen_776_; lean_object* v_cache_777_; lean_object* v_messages_778_; lean_object* v_infoState_779_; lean_object* v_snapshotTasks_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_810_; 
v___x_771_ = lean_st_ref_take(v___y_763_);
v_traceState_772_ = lean_ctor_get(v___x_771_, 4);
v_env_773_ = lean_ctor_get(v___x_771_, 0);
v_nextMacroScope_774_ = lean_ctor_get(v___x_771_, 1);
v_ngen_775_ = lean_ctor_get(v___x_771_, 2);
v_auxDeclNGen_776_ = lean_ctor_get(v___x_771_, 3);
v_cache_777_ = lean_ctor_get(v___x_771_, 5);
v_messages_778_ = lean_ctor_get(v___x_771_, 6);
v_infoState_779_ = lean_ctor_get(v___x_771_, 7);
v_snapshotTasks_780_ = lean_ctor_get(v___x_771_, 8);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_810_ == 0)
{
v___x_782_ = v___x_771_;
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snapshotTasks_780_);
lean_inc(v_infoState_779_);
lean_inc(v_messages_778_);
lean_inc(v_cache_777_);
lean_inc(v_traceState_772_);
lean_inc(v_auxDeclNGen_776_);
lean_inc(v_ngen_775_);
lean_inc(v_nextMacroScope_774_);
lean_inc(v_env_773_);
lean_dec(v___x_771_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
uint64_t v_tid_784_; lean_object* v_traces_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_809_; 
v_tid_784_ = lean_ctor_get_uint64(v_traceState_772_, sizeof(void*)*1);
v_traces_785_ = lean_ctor_get(v_traceState_772_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_traceState_772_);
if (v_isSharedCheck_809_ == 0)
{
v___x_787_ = v_traceState_772_;
v_isShared_788_ = v_isSharedCheck_809_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_traces_785_);
lean_dec(v_traceState_772_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_809_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; double v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
v___x_791_ = 0;
v___x_792_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
v___x_793_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_793_, 0, v_cls_758_);
lean_ctor_set(v___x_793_, 1, v___x_789_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
lean_ctor_set_float(v___x_793_, sizeof(void*)*3, v___x_790_);
lean_ctor_set_float(v___x_793_, sizeof(void*)*3 + 8, v___x_790_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*3 + 16, v___x_791_);
v___x_794_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1));
v___x_795_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v_a_767_);
lean_ctor_set(v___x_795_, 2, v___x_794_);
lean_inc(v_ref_765_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_ref_765_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_PersistentArray_push___redArg(v_traces_785_, v___x_796_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_797_);
v___x_799_ = v___x_787_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_797_);
lean_ctor_set_uint64(v_reuseFailAlloc_808_, sizeof(void*)*1, v_tid_784_);
v___x_799_ = v_reuseFailAlloc_808_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___x_799_);
v___x_801_ = v___x_782_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_env_773_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_nextMacroScope_774_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_ngen_775_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_auxDeclNGen_776_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_807_, 5, v_cache_777_);
lean_ctor_set(v_reuseFailAlloc_807_, 6, v_messages_778_);
lean_ctor_set(v_reuseFailAlloc_807_, 7, v_infoState_779_);
lean_ctor_set(v_reuseFailAlloc_807_, 8, v_snapshotTasks_780_);
v___x_801_ = v_reuseFailAlloc_807_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = lean_st_ref_set(v___y_763_, v___x_801_);
v___x_803_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_803_);
v___x_805_ = v___x_769_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v___y_842_, uint8_t v_suppressElabErrors_843_, lean_object* v_x_844_){
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
return v___y_842_;
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_854_ = lean_string_dec_eq(v_str_847_, v___x_853_);
if (v___x_854_ == 0)
{
return v___y_842_;
}
else
{
return v_suppressElabErrors_843_;
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
return v___y_842_;
}
else
{
return v_suppressElabErrors_843_;
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
return v___y_842_;
}
else
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_864_ = lean_string_dec_eq(v_str_859_, v___x_863_);
if (v___x_864_ == 0)
{
return v___y_842_;
}
else
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_866_ = lean_string_dec_eq(v_str_858_, v___x_865_);
if (v___x_866_ == 0)
{
return v___y_842_;
}
else
{
return v_suppressElabErrors_843_;
}
}
}
}
else
{
return v___y_842_;
}
}
default: 
{
return v___y_842_;
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
return v___y_842_;
}
else
{
return v_suppressElabErrors_843_;
}
}
default: 
{
return v___y_842_;
}
}
}
else
{
return v___y_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_870_, lean_object* v_suppressElabErrors_871_, lean_object* v_x_872_){
_start:
{
uint8_t v___y_24908__boxed_873_; uint8_t v_suppressElabErrors_boxed_874_; uint8_t v_res_875_; lean_object* v_r_876_; 
v___y_24908__boxed_873_ = lean_unbox(v___y_870_);
v_suppressElabErrors_boxed_874_ = lean_unbox(v_suppressElabErrors_871_);
v_res_875_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v___y_24908__boxed_873_, v_suppressElabErrors_boxed_874_, v_x_872_);
lean_dec(v_x_872_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_877_, lean_object* v_msgData_878_, uint8_t v_severity_879_, uint8_t v_isSilent_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; uint8_t v___y_891_; lean_object* v___y_892_; uint8_t v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; uint8_t v___y_926_; uint8_t v___y_927_; lean_object* v___y_928_; uint8_t v___y_929_; lean_object* v___y_930_; lean_object* v___y_948_; lean_object* v___y_949_; uint8_t v___y_950_; uint8_t v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; uint8_t v___y_954_; lean_object* v___y_955_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; uint8_t v___y_962_; lean_object* v___y_963_; uint8_t v___y_964_; uint8_t v___y_965_; uint8_t v___x_970_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; uint8_t v___y_977_; uint8_t v___y_978_; uint8_t v___y_980_; uint8_t v___x_995_; 
v___x_970_ = 2;
v___x_995_ = l_Lean_instBEqMessageSeverity_beq(v_severity_879_, v___x_970_);
if (v___x_995_ == 0)
{
v___y_980_ = v___x_995_;
goto v___jp_979_;
}
else
{
uint8_t v___x_996_; 
lean_inc_ref(v_msgData_878_);
v___x_996_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_878_);
v___y_980_ = v___x_996_;
goto v___jp_979_;
}
v___jp_886_:
{
lean_object* v___x_896_; lean_object* v_currNamespace_897_; lean_object* v_openDecls_898_; lean_object* v_env_899_; lean_object* v_nextMacroScope_900_; lean_object* v_ngen_901_; lean_object* v_auxDeclNGen_902_; lean_object* v_traceState_903_; lean_object* v_cache_904_; lean_object* v_messages_905_; lean_object* v_infoState_906_; lean_object* v_snapshotTasks_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_921_; 
v___x_896_ = lean_st_ref_take(v___y_895_);
v_currNamespace_897_ = lean_ctor_get(v___y_894_, 6);
v_openDecls_898_ = lean_ctor_get(v___y_894_, 7);
v_env_899_ = lean_ctor_get(v___x_896_, 0);
v_nextMacroScope_900_ = lean_ctor_get(v___x_896_, 1);
v_ngen_901_ = lean_ctor_get(v___x_896_, 2);
v_auxDeclNGen_902_ = lean_ctor_get(v___x_896_, 3);
v_traceState_903_ = lean_ctor_get(v___x_896_, 4);
v_cache_904_ = lean_ctor_get(v___x_896_, 5);
v_messages_905_ = lean_ctor_get(v___x_896_, 6);
v_infoState_906_ = lean_ctor_get(v___x_896_, 7);
v_snapshotTasks_907_ = lean_ctor_get(v___x_896_, 8);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_921_ == 0)
{
v___x_909_ = v___x_896_;
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snapshotTasks_907_);
lean_inc(v_infoState_906_);
lean_inc(v_messages_905_);
lean_inc(v_cache_904_);
lean_inc(v_traceState_903_);
lean_inc(v_auxDeclNGen_902_);
lean_inc(v_ngen_901_);
lean_inc(v_nextMacroScope_900_);
lean_inc(v_env_899_);
lean_dec(v___x_896_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
lean_inc(v_openDecls_898_);
lean_inc(v_currNamespace_897_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_currNamespace_897_);
lean_ctor_set(v___x_911_, 1, v_openDecls_898_);
v___x_912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___y_889_);
lean_inc_ref(v___y_887_);
lean_inc_ref(v___y_888_);
v___x_913_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_913_, 0, v___y_888_);
lean_ctor_set(v___x_913_, 1, v___y_892_);
lean_ctor_set(v___x_913_, 2, v___y_890_);
lean_ctor_set(v___x_913_, 3, v___y_887_);
lean_ctor_set(v___x_913_, 4, v___x_912_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*5, v___y_893_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*5 + 1, v___y_891_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*5 + 2, v_isSilent_880_);
v___x_914_ = l_Lean_MessageLog_add(v___x_913_, v_messages_905_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 6, v___x_914_);
v___x_916_ = v___x_909_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_env_899_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_nextMacroScope_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_ngen_901_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_auxDeclNGen_902_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_traceState_903_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_cache_904_);
lean_ctor_set(v_reuseFailAlloc_920_, 6, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_920_, 7, v_infoState_906_);
lean_ctor_set(v_reuseFailAlloc_920_, 8, v_snapshotTasks_907_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_st_ref_set(v___y_895_, v___x_916_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
v___jp_922_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_946_; 
v___x_931_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_878_);
v___x_932_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_931_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_946_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_inc_ref_n(v___y_928_, 2);
v___x_937_ = l_Lean_FileMap_toPosition(v___y_928_, v___y_924_);
lean_dec(v___y_924_);
v___x_938_ = l_Lean_FileMap_toPosition(v___y_928_, v___y_930_);
lean_dec(v___y_930_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
if (v___y_926_ == 0)
{
lean_del_object(v___x_935_);
lean_dec_ref(v___y_923_);
v___y_887_ = v___x_940_;
v___y_888_ = v___y_925_;
v___y_889_ = v_a_933_;
v___y_890_ = v___x_939_;
v___y_891_ = v___y_927_;
v___y_892_ = v___x_937_;
v___y_893_ = v___y_929_;
v___y_894_ = v___y_883_;
v___y_895_ = v___y_884_;
goto v___jp_886_;
}
else
{
uint8_t v___x_941_; 
lean_inc(v_a_933_);
v___x_941_ = l_Lean_MessageData_hasTag(v___y_923_, v_a_933_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_944_; 
lean_dec_ref_known(v___x_939_, 1);
lean_dec_ref(v___x_937_);
lean_dec(v_a_933_);
v___x_942_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_942_);
v___x_944_ = v___x_935_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
else
{
lean_del_object(v___x_935_);
v___y_887_ = v___x_940_;
v___y_888_ = v___y_925_;
v___y_889_ = v_a_933_;
v___y_890_ = v___x_939_;
v___y_891_ = v___y_927_;
v___y_892_ = v___x_937_;
v___y_893_ = v___y_929_;
v___y_894_ = v___y_883_;
v___y_895_ = v___y_884_;
goto v___jp_886_;
}
}
}
}
v___jp_947_:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Syntax_getTailPos_x3f(v___y_953_, v___y_954_);
lean_dec(v___y_953_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_inc(v___y_955_);
v___y_923_ = v___y_948_;
v___y_924_ = v___y_955_;
v___y_925_ = v___y_949_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_950_;
v___y_928_ = v___y_952_;
v___y_929_ = v___y_954_;
v___y_930_ = v___y_955_;
goto v___jp_922_;
}
else
{
lean_object* v_val_957_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___x_956_, 1);
v___y_923_ = v___y_948_;
v___y_924_ = v___y_955_;
v___y_925_ = v___y_949_;
v___y_926_ = v___y_951_;
v___y_927_ = v___y_950_;
v___y_928_ = v___y_952_;
v___y_929_ = v___y_954_;
v___y_930_ = v_val_957_;
goto v___jp_922_;
}
}
v___jp_958_:
{
lean_object* v_ref_966_; lean_object* v___x_967_; 
v_ref_966_ = l_Lean_replaceRef(v_ref_877_, v___y_960_);
v___x_967_ = l_Lean_Syntax_getPos_x3f(v_ref_966_, v___y_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; 
v___x_968_ = lean_unsigned_to_nat(0u);
v___y_948_ = v___y_959_;
v___y_949_ = v___y_961_;
v___y_950_ = v___y_965_;
v___y_951_ = v___y_962_;
v___y_952_ = v___y_963_;
v___y_953_ = v_ref_966_;
v___y_954_ = v___y_964_;
v___y_955_ = v___x_968_;
goto v___jp_947_;
}
else
{
lean_object* v_val_969_; 
v_val_969_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v___x_967_, 1);
v___y_948_ = v___y_959_;
v___y_949_ = v___y_961_;
v___y_950_ = v___y_965_;
v___y_951_ = v___y_962_;
v___y_952_ = v___y_963_;
v___y_953_ = v_ref_966_;
v___y_954_ = v___y_964_;
v___y_955_ = v_val_969_;
goto v___jp_947_;
}
}
v___jp_971_:
{
if (v___y_978_ == 0)
{
v___y_959_ = v___y_973_;
v___y_960_ = v___y_972_;
v___y_961_ = v___y_974_;
v___y_962_ = v___y_975_;
v___y_963_ = v___y_976_;
v___y_964_ = v___y_977_;
v___y_965_ = v_severity_879_;
goto v___jp_958_;
}
else
{
v___y_959_ = v___y_973_;
v___y_960_ = v___y_972_;
v___y_961_ = v___y_974_;
v___y_962_ = v___y_975_;
v___y_963_ = v___y_976_;
v___y_964_ = v___y_977_;
v___y_965_ = v___x_970_;
goto v___jp_958_;
}
}
v___jp_979_:
{
if (v___y_980_ == 0)
{
lean_object* v_fileName_981_; lean_object* v_fileMap_982_; lean_object* v_options_983_; lean_object* v_ref_984_; uint8_t v_suppressElabErrors_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___f_988_; uint8_t v___x_989_; uint8_t v___x_990_; 
v_fileName_981_ = lean_ctor_get(v___y_883_, 0);
v_fileMap_982_ = lean_ctor_get(v___y_883_, 1);
v_options_983_ = lean_ctor_get(v___y_883_, 2);
v_ref_984_ = lean_ctor_get(v___y_883_, 5);
v_suppressElabErrors_985_ = lean_ctor_get_uint8(v___y_883_, sizeof(void*)*14 + 1);
v___x_986_ = lean_box(v___y_980_);
v___x_987_ = lean_box(v_suppressElabErrors_985_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_988_, 0, v___x_986_);
lean_closure_set(v___f_988_, 1, v___x_987_);
v___x_989_ = 1;
v___x_990_ = l_Lean_instBEqMessageSeverity_beq(v_severity_879_, v___x_989_);
if (v___x_990_ == 0)
{
v___y_972_ = v_ref_984_;
v___y_973_ = v___f_988_;
v___y_974_ = v_fileName_981_;
v___y_975_ = v_suppressElabErrors_985_;
v___y_976_ = v_fileMap_982_;
v___y_977_ = v___y_980_;
v___y_978_ = v___x_990_;
goto v___jp_971_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_warningAsError;
v___x_992_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_options_983_, v___x_991_);
v___y_972_ = v_ref_984_;
v___y_973_ = v___f_988_;
v___y_974_ = v_fileName_981_;
v___y_975_ = v_suppressElabErrors_985_;
v___y_976_ = v_fileMap_982_;
v___y_977_ = v___y_980_;
v___y_978_ = v___x_992_;
goto v___jp_971_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v_msgData_878_);
v___x_993_ = lean_box(0);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_997_, lean_object* v_msgData_998_, lean_object* v_severity_999_, lean_object* v_isSilent_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v_severity_boxed_1006_; uint8_t v_isSilent_boxed_1007_; lean_object* v_res_1008_; 
v_severity_boxed_1006_ = lean_unbox(v_severity_999_);
v_isSilent_boxed_1007_ = lean_unbox(v_isSilent_1000_);
v_res_1008_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_997_, v_msgData_998_, v_severity_boxed_1006_, v_isSilent_boxed_1007_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v_ref_997_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(lean_object* v_ref_1009_, lean_object* v_msgData_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = 1;
v___x_1020_ = 0;
v___x_1021_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1009_, v_msgData_1010_, v___x_1019_, v___x_1020_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(lean_object* v_ref_1022_, lean_object* v_msgData_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_1022_, v_msgData_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v_ref_1022_);
return v_res_1032_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(lean_object* v_linterOption_1039_, lean_object* v_stx_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_name_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1068_; 
v_name_1050_ = lean_ctor_get(v_linterOption_1039_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_linterOption_1039_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_linterOption_1039_, 1);
lean_dec(v_unused_1069_);
v___x_1052_ = v_linterOption_1039_;
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_name_1050_);
lean_dec(v_linterOption_1039_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
lean_inc(v_name_1050_);
v___x_1055_ = l_Lean_MessageData_ofName(v_name_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 7);
lean_ctor_set(v___x_1052_, 1, v___x_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_disable_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1058_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v_disable_1060_ = l_Lean_MessageData_note(v___x_1059_);
v___x_1061_ = l_Lean_Linter_linterMessageTag;
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_msg_1041_);
lean_ctor_set(v___x_1062_, 1, v_disable_1060_);
v___x_1063_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_name_1050_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
lean_inc(v_stx_1040_);
v___x_1065_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_stx_1040_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_1040_, v___x_1065_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v_stx_1040_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(lean_object* v_linterOption_1070_, lean_object* v_stx_1071_, lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v_linterOption_1070_, v_stx_1071_, v_msg_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(lean_object* v_msgData_1082_, uint8_t v_severity_1083_, uint8_t v_isSilent_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_ref_1093_; lean_object* v___x_1094_; 
v_ref_1093_ = lean_ctor_get(v___y_1090_, 5);
v___x_1094_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1093_, v_msgData_1082_, v_severity_1083_, v_isSilent_1084_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(lean_object* v_msgData_1095_, lean_object* v_severity_1096_, lean_object* v_isSilent_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_severity_boxed_1106_; uint8_t v_isSilent_boxed_1107_; lean_object* v_res_1108_; 
v_severity_boxed_1106_ = lean_unbox(v_severity_1096_);
v_isSilent_boxed_1107_ = lean_unbox(v_isSilent_1097_);
v_res_1108_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1095_, v_severity_boxed_1106_, v_isSilent_boxed_1107_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(lean_object* v_msgData_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = 1;
v___x_1119_ = 0;
v___x_1120_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1109_, v___x_1118_, v___x_1119_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_msgData_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
return v_res_1130_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1141_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3));
v___x_1142_ = l_Lean_Name_append(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(lean_object* v___x_1149_, uint8_t v_force_1150_, lean_object* v_thm_1151_, lean_object* v_origin_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___x_1193_; 
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v___y_1153_);
v___x_1193_ = lean_simp(v___x_1149_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v___y_1153_);
lean_dec_ref(v_origin_1152_);
lean_dec_ref(v_thm_1151_);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1193_, 0);
lean_dec(v_unused_1202_);
v___x_1195_ = v___x_1193_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v___x_1193_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_box(0);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1227_; 
v_a_1203_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1205_ = v___x_1193_;
v_isShared_1206_ = v_isSharedCheck_1227_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1193_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1227_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Lean_Exception_isInterrupt(v_a_1203_);
if (v___x_1207_ == 0)
{
lean_object* v_options_1208_; uint8_t v_hasTrace_1209_; 
lean_del_object(v___x_1205_);
v_options_1208_ = lean_ctor_get(v___y_1158_, 2);
v_hasTrace_1209_ = lean_ctor_get_uint8(v_options_1208_, sizeof(void*)*1);
if (v_hasTrace_1209_ == 0)
{
lean_dec(v_a_1203_);
lean_dec_ref(v_origin_1152_);
v___y_1162_ = v___y_1153_;
v___y_1163_ = v___y_1154_;
v___y_1164_ = v___y_1155_;
v___y_1165_ = v___y_1156_;
v___y_1166_ = v___y_1157_;
v___y_1167_ = v___y_1158_;
v___y_1168_ = v___y_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v_inheritedTraceOptions_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_inheritedTraceOptions_1210_ = lean_ctor_get(v___y_1158_, 13);
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1212_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4);
v___x_1213_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1210_, v_options_1208_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_a_1203_);
lean_dec_ref(v_origin_1152_);
v___y_1162_ = v___y_1153_;
v___y_1163_ = v___y_1154_;
v___y_1164_ = v___y_1155_;
v___y_1165_ = v___y_1156_;
v___y_1166_ = v___y_1157_;
v___y_1167_ = v___y_1158_;
v___y_1168_ = v___y_1159_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1214_; lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1214_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_1152_);
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref(v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_a_1215_);
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__8, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_Exception_toMessageData(v_a_1203_);
v___x_1221_ = l_Lean_indentD(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1219_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v___x_1211_, v___x_1222_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_dec_ref_known(v___x_1223_, 1);
v___y_1162_ = v___y_1153_;
v___y_1163_ = v___y_1154_;
v___y_1164_ = v___y_1155_;
v___y_1165_ = v___y_1156_;
v___y_1166_ = v___y_1157_;
v___y_1167_ = v___y_1158_;
v___y_1168_ = v___y_1159_;
goto v___jp_1161_;
}
else
{
lean_dec(v___y_1153_);
lean_dec_ref(v_thm_1151_);
return v___x_1223_;
}
}
}
}
else
{
lean_object* v___x_1225_; 
lean_dec(v___y_1153_);
lean_dec_ref(v_origin_1152_);
lean_dec_ref(v_thm_1151_);
if (v_isShared_1206_ == 0)
{
v___x_1225_ = v___x_1205_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1203_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
v___jp_1161_:
{
if (v_force_1150_ == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1151_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v_ref_1171_ = lean_ctor_get(v___y_1167_, 5);
v___x_1172_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
lean_inc(v_ref_1171_);
v___x_1173_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v___x_1172_, v_ref_1171_, v_a_1170_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1162_);
return v___x_1173_;
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v___y_1162_);
v_a_1174_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1169_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1169_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
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
else
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1151_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_a_1183_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1162_);
return v___x_1184_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v___y_1162_);
v_a_1185_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1182_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1182_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___boxed(lean_object* v___x_1228_, lean_object* v_force_1229_, lean_object* v_thm_1230_, lean_object* v_origin_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_force_boxed_1240_; lean_object* v_res_1241_; 
v_force_boxed_1240_ = lean_unbox(v_force_1229_);
v_res_1241_ = l_Lean_Meta_Simp_checkLoops___lam__0(v___x_1228_, v_force_boxed_1240_, v_thm_1230_, v_origin_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1241_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_unsigned_to_nat(16u);
v___x_1244_ = lean_mk_array(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__0, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_unsigned_to_nat(32u);
v___x_1255_ = lean_mk_empty_array_with_capacity(v___x_1254_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6(void){
_start:
{
size_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1257_ = ((size_t)5ULL);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_unsigned_to_nat(32u);
v___x_1260_ = lean_mk_empty_array_with_capacity(v___x_1259_);
v___x_1261_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__5, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5);
v___x_1262_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
lean_ctor_set(v___x_1262_, 2, v___x_1258_);
lean_ctor_set(v___x_1262_, 3, v___x_1258_);
lean_ctor_set_usize(v___x_1262_, 4, v___x_1257_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
lean_ctor_set(v___x_1265_, 2, v___x_1264_);
lean_ctor_set(v___x_1265_, 3, v___x_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1(uint8_t v_force_1266_, lean_object* v_thm_1267_, lean_object* v_origin_1268_, uint8_t v_a_1269_, lean_object* v_ctxt_1270_, lean_object* v_methods_1271_, lean_object* v___xs_1272_, lean_object* v_type_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
v___x_1279_ = lean_whnf(v_type_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = l_Lean_Expr_appArg_x21(v_a_1280_);
lean_dec(v_a_1280_);
v___x_1282_ = lean_box(v_force_1266_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1283_, 0, v___x_1281_);
lean_closure_set(v___f_1283_, 1, v___x_1282_);
lean_closure_set(v___f_1283_, 2, v_thm_1267_);
lean_closure_set(v___f_1283_, 3, v_origin_1268_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__1, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1);
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1287_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*2, v_a_1269_);
v___x_1288_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4);
v___x_1289_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__7, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7);
v___x_1290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1287_);
lean_ctor_set(v___x_1290_, 1, v___x_1285_);
lean_ctor_set(v___x_1290_, 2, v___x_1285_);
lean_ctor_set(v___x_1290_, 3, v___x_1288_);
lean_ctor_set(v___x_1290_, 4, v___x_1284_);
lean_ctor_set(v___x_1290_, 5, v___x_1289_);
v___x_1291_ = l_Lean_Meta_Simp_SimpM_run___redArg(v_ctxt_1270_, v___x_1290_, v_methods_1271_, v___f_1283_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1291_, 0);
lean_dec(v_unused_1300_);
v___x_1293_ = v___x_1291_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v___x_1291_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_box(0);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1291_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_methods_1271_);
lean_dec_ref(v_ctxt_1270_);
lean_dec_ref(v_origin_1268_);
lean_dec_ref(v_thm_1267_);
v_a_1309_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1279_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1279_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___boxed(lean_object* v_force_1317_, lean_object* v_thm_1318_, lean_object* v_origin_1319_, lean_object* v_a_1320_, lean_object* v_ctxt_1321_, lean_object* v_methods_1322_, lean_object* v___xs_1323_, lean_object* v_type_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v_force_boxed_1330_; uint8_t v_a_25617__boxed_1331_; lean_object* v_res_1332_; 
v_force_boxed_1330_ = lean_unbox(v_force_1317_);
v_a_25617__boxed_1331_ = lean_unbox(v_a_1320_);
v_res_1332_ = l_Lean_Meta_Simp_checkLoops___lam__1(v_force_boxed_1330_, v_thm_1318_, v_origin_1319_, v_a_25617__boxed_1331_, v_ctxt_1321_, v_methods_1322_, v___xs_1323_, v_type_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___xs_1323_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops(uint8_t v_force_1333_, lean_object* v_ctxt_1334_, lean_object* v_methods_1335_, lean_object* v_thm_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_1333_, v_ctxt_1334_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1382_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1382_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1382_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_unbox(v_a_1343_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
lean_dec(v_a_1343_);
lean_dec_ref(v_thm_1336_);
lean_dec_ref(v_methods_1335_);
lean_dec_ref(v_ctxt_1334_);
v___x_1348_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v_proof_1352_; lean_object* v_origin_1353_; uint8_t v___x_1354_; 
v_proof_1352_ = lean_ctor_get(v_thm_1336_, 2);
v_origin_1353_ = lean_ctor_get(v_thm_1336_, 4);
lean_inc_ref(v_origin_1353_);
v___x_1354_ = l_Lean_Expr_hasFVar(v_proof_1352_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_del_object(v___x_1345_);
lean_inc_ref(v_thm_1336_);
v___x_1355_ = l_Lean_Meta_SimpTheorem_getValue(v_thm_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
lean_inc(v_a_1340_);
lean_inc_ref(v_a_1339_);
lean_inc(v_a_1338_);
lean_inc_ref(v_a_1337_);
v___x_1357_ = lean_infer_type(v_a_1356_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = lean_box(v_force_1333_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1360_, 0, v___x_1359_);
lean_closure_set(v___f_1360_, 1, v_thm_1336_);
lean_closure_set(v___f_1360_, 2, v_origin_1353_);
lean_closure_set(v___f_1360_, 3, v_a_1343_);
lean_closure_set(v___f_1360_, 4, v_ctxt_1334_);
lean_closure_set(v___f_1360_, 5, v_methods_1335_);
v___x_1361_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_1358_, v___f_1360_, v___x_1354_, v___x_1354_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_origin_1353_);
lean_dec(v_a_1343_);
lean_dec_ref(v_thm_1336_);
lean_dec_ref(v_methods_1335_);
lean_dec_ref(v_ctxt_1334_);
v_a_1362_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1357_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1357_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
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
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_origin_1353_);
lean_dec(v_a_1343_);
lean_dec_ref(v_thm_1336_);
lean_dec_ref(v_methods_1335_);
lean_dec_ref(v_ctxt_1334_);
v_a_1370_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1355_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1355_);
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
else
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v_origin_1353_);
lean_dec(v_a_1343_);
lean_dec_ref(v_thm_1336_);
lean_dec_ref(v_methods_1335_);
lean_dec_ref(v_ctxt_1334_);
v___x_1378_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1378_);
v___x_1380_ = v___x_1345_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v_thm_1336_);
lean_dec_ref(v_methods_1335_);
lean_dec_ref(v_ctxt_1334_);
v_a_1383_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1342_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1342_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___boxed(lean_object* v_force_1391_, lean_object* v_ctxt_1392_, lean_object* v_methods_1393_, lean_object* v_thm_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
uint8_t v_force_boxed_1400_; lean_object* v_res_1401_; 
v_force_boxed_1400_ = lean_unbox(v_force_1391_);
v_res_1401_ = l_Lean_Meta_Simp_checkLoops(v_force_boxed_1400_, v_ctxt_1392_, v_methods_1393_, v_thm_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(lean_object* v_cls_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_1402_, v_msg_1403_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(lean_object* v_cls_1413_, lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(v_cls_1413_, v_msg_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(lean_object* v_ref_1424_, lean_object* v_msgData_1425_, uint8_t v_severity_1426_, uint8_t v_isSilent_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1424_, v_msgData_1425_, v_severity_1426_, v_isSilent_1427_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_1437_, lean_object* v_msgData_1438_, lean_object* v_severity_1439_, lean_object* v_isSilent_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_severity_boxed_1449_; uint8_t v_isSilent_boxed_1450_; lean_object* v_res_1451_; 
v_severity_boxed_1449_ = lean_unbox(v_severity_1439_);
v_isSilent_boxed_1450_ = lean_unbox(v_isSilent_1440_);
v_res_1451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_1437_, v_msgData_1438_, v_severity_boxed_1449_, v_isSilent_boxed_1450_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v_ref_1437_);
return v_res_1451_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

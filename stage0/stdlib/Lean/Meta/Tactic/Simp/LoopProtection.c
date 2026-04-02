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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "loopingSimpArgs"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 197, 78, 135, 53, 39, 179, 65)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 451, .m_capacity = 451, .m_length = 450, .m_data = "When enabled, `simp` will check if the theorems passed as simp arguments (`simp [thm1]`) are possibly looping in the current simp set.\n\nMore precisely, it tries to simplify the right-hand side of the theorem and complains if that fails, which it typically does because of running out of recursion depth.\n\nThis is a relatively expensive check, so it i disabled by default, and only run after a `simp` call actually failed with a recursion depth error."};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(203, 225, 37, 249, 29, 246, 11, 175)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 143, 228, 91, 214, 79, 187, 139)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_));
v___x_62_ = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(lean_object* v_a_65_, lean_object* v_usedTheorems_66_, lean_object* v_a_x3f_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_cache_70_; lean_object* v_congrCache_71_; lean_object* v_dsimpCache_72_; lean_object* v_numSteps_73_; lean_object* v_diag_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_84_; 
v___x_69_ = lean_st_ref_take(v_a_65_);
v_cache_70_ = lean_ctor_get(v___x_69_, 0);
v_congrCache_71_ = lean_ctor_get(v___x_69_, 1);
v_dsimpCache_72_ = lean_ctor_get(v___x_69_, 2);
v_numSteps_73_ = lean_ctor_get(v___x_69_, 4);
v_diag_74_ = lean_ctor_get(v___x_69_, 5);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v___x_69_, 3);
lean_dec(v_unused_85_);
v___x_76_ = v___x_69_;
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_diag_74_);
lean_inc(v_numSteps_73_);
lean_inc(v_dsimpCache_72_);
lean_inc(v_congrCache_71_);
lean_inc(v_cache_70_);
lean_dec(v___x_69_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 3, v_usedTheorems_66_);
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_cache_70_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_congrCache_71_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_dsimpCache_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 3, v_usedTheorems_66_);
lean_ctor_set(v_reuseFailAlloc_83_, 4, v_numSteps_73_);
lean_ctor_set(v_reuseFailAlloc_83_, 5, v_diag_74_);
v___x_79_ = v_reuseFailAlloc_83_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_st_ref_set(v_a_65_, v___x_79_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0___boxed(lean_object* v_a_86_, lean_object* v_usedTheorems_87_, lean_object* v_a_x3f_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_86_, v_usedTheorems_87_, v_a_x3f_88_);
lean_dec(v_a_x3f_88_);
lean_dec(v_a_86_);
return v_res_90_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_cache_108_; lean_object* v_congrCache_109_; lean_object* v_dsimpCache_110_; lean_object* v_numSteps_111_; lean_object* v_diag_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_151_; 
v___x_106_ = lean_st_ref_get(v_a_100_);
v___x_107_ = lean_st_ref_take(v_a_100_);
v_cache_108_ = lean_ctor_get(v___x_107_, 0);
v_congrCache_109_ = lean_ctor_get(v___x_107_, 1);
v_dsimpCache_110_ = lean_ctor_get(v___x_107_, 2);
v_numSteps_111_ = lean_ctor_get(v___x_107_, 4);
v_diag_112_ = lean_ctor_get(v___x_107_, 5);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v___x_107_, 3);
lean_dec(v_unused_152_);
v___x_114_ = v___x_107_;
v_isShared_115_ = v_isSharedCheck_151_;
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
v_isShared_115_ = v_isSharedCheck_151_;
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
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_cache_108_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_congrCache_109_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_dsimpCache_110_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_numSteps_111_);
lean_ctor_set(v_reuseFailAlloc_150_, 5, v_diag_112_);
v___x_118_ = v_reuseFailAlloc_150_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v_usedTheorems_120_; lean_object* v_r_121_; 
v___x_119_ = lean_st_ref_set(v_a_100_, v___x_118_);
v_usedTheorems_120_ = lean_ctor_get(v___x_106_, 3);
lean_inc_ref(v_usedTheorems_120_);
lean_dec(v___x_106_);
lean_inc(v_a_104_);
lean_inc_ref(v_a_103_);
lean_inc(v_a_102_);
lean_inc_ref(v_a_101_);
lean_inc(v_a_100_);
lean_inc_ref(v_a_99_);
lean_inc(v_a_98_);
v_r_121_ = lean_apply_8(v_x_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, lean_box(0));
if (lean_obj_tag(v_r_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_138_; 
v_a_122_ = lean_ctor_get(v_r_121_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v_r_121_);
if (v_isSharedCheck_138_ == 0)
{
v___x_124_ = v_r_121_;
v_isShared_125_ = v_isSharedCheck_138_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v_r_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_138_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
lean_inc(v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 1);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_137_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
v___x_128_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_100_, v_usedTheorems_120_, v___x_127_);
lean_dec_ref(v___x_127_);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_136_);
v___x_130_ = v___x_128_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_dec(v___x_128_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v_a_122_);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_122_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_139_ = lean_ctor_get(v_r_121_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v_r_121_);
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_100_, v_usedTheorems_120_, v___x_140_);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_141_, 0);
lean_dec(v_unused_149_);
v___x_143_ = v___x_141_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_dec(v___x_141_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 1);
lean_ctor_set(v___x_143_, 0, v_a_139_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_139_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems(lean_object* v_00_u03b1_163_, lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_cache_175_; lean_object* v_congrCache_176_; lean_object* v_dsimpCache_177_; lean_object* v_numSteps_178_; lean_object* v_diag_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_218_; 
v___x_173_ = lean_st_ref_get(v_a_167_);
v___x_174_ = lean_st_ref_take(v_a_167_);
v_cache_175_ = lean_ctor_get(v___x_174_, 0);
v_congrCache_176_ = lean_ctor_get(v___x_174_, 1);
v_dsimpCache_177_ = lean_ctor_get(v___x_174_, 2);
v_numSteps_178_ = lean_ctor_get(v___x_174_, 4);
v_diag_179_ = lean_ctor_get(v___x_174_, 5);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_174_, 3);
lean_dec(v_unused_219_);
v___x_181_ = v___x_174_;
v_isShared_182_ = v_isSharedCheck_218_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_diag_179_);
lean_inc(v_numSteps_178_);
lean_inc(v_dsimpCache_177_);
lean_inc(v_congrCache_176_);
lean_inc(v_cache_175_);
lean_dec(v___x_174_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_218_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2, &l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once, _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 3, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_cache_175_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_congrCache_176_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_dsimpCache_177_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_numSteps_178_);
lean_ctor_set(v_reuseFailAlloc_217_, 5, v_diag_179_);
v___x_185_ = v_reuseFailAlloc_217_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; lean_object* v_usedTheorems_187_; lean_object* v_r_188_; 
v___x_186_ = lean_st_ref_set(v_a_167_, v___x_185_);
v_usedTheorems_187_ = lean_ctor_get(v___x_173_, 3);
lean_inc_ref(v_usedTheorems_187_);
lean_dec(v___x_173_);
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
v___x_195_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_167_, v_usedTheorems_187_, v___x_194_);
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
lean_dec_ref(v_r_188_);
v___x_207_ = lean_box(0);
v___x_208_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(v_a_167_, v_usedTheorems_187_, v___x_207_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshUsedTheorems___boxed(lean_object* v_00_u03b1_220_, lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Meta_Simp_withFreshUsedTheorems(v_00_u03b1_220_, v_x_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
return v_res_230_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(lean_object* v_x_240_){
_start:
{
switch(lean_obj_tag(v_x_240_))
{
case 0:
{
lean_object* v_declName_242_; uint8_t v_post_243_; uint8_t v_inv_244_; uint8_t v___x_245_; lean_object* v_r_246_; 
v_declName_242_ = lean_ctor_get(v_x_240_, 0);
lean_inc(v_declName_242_);
v_post_243_ = lean_ctor_get_uint8(v_x_240_, sizeof(void*)*1);
v_inv_244_ = lean_ctor_get_uint8(v_x_240_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_240_);
v___x_245_ = 0;
v_r_246_ = l_Lean_MessageData_ofConstName(v_declName_242_, v___x_245_);
if (v_post_243_ == 0)
{
if (v_inv_244_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_r_246_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_r_246_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
else
{
if (v_inv_244_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_r_246_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_r_246_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
case 1:
{
lean_object* v_fvarId_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_266_; 
v_fvarId_257_ = lean_ctor_get(v_x_240_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_266_ == 0)
{
v___x_259_ = v_x_240_;
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_fvarId_257_);
lean_dec(v_x_240_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = l_Lean_mkFVar(v_fvarId_257_);
v___x_262_ = l_Lean_MessageData_ofExpr(v___x_261_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 0);
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
case 2:
{
lean_object* v_ref_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_ref_267_ = lean_ctor_get(v_x_240_, 1);
lean_inc(v_ref_267_);
lean_dec_ref(v_x_240_);
v___x_268_ = l_Lean_MessageData_ofSyntax(v_ref_267_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
default: 
{
lean_object* v_name_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_name_270_ = lean_ctor_get(v_x_240_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v_x_240_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_name_270_);
lean_dec(v_x_240_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = l_Lean_MessageData_ofName(v_name_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___boxed(lean_object* v_x_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_282_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___boxed(lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(v_x_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_295_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(size_t v_sz_299_, size_t v_i_300_, lean_object* v_bs_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v_bs_301_);
return v___x_308_;
}
else
{
lean_object* v_v_309_; lean_object* v___x_310_; lean_object* v_bs_x27_311_; lean_object* v_a_313_; lean_object* v___x_318_; 
v_v_309_ = lean_array_uget(v_bs_301_, v_i_300_);
v___x_310_ = lean_unsigned_to_nat(0u);
v_bs_x27_311_ = lean_array_uset(v_bs_301_, v_i_300_, v___x_310_);
v___x_318_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_v_309_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_319_);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
v_a_313_ = v___x_322_;
goto v___jp_312_;
}
else
{
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v___x_318_);
v_a_313_ = v_a_323_;
goto v___jp_312_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_bs_x27_311_);
v_a_324_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_318_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_318_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v___jp_312_:
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_300_, v___x_314_);
v___x_316_ = lean_array_uset(v_bs_x27_311_, v_i_300_, v_a_313_);
v_i_300_ = v___x_315_;
v_bs_301_ = v___x_316_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___boxed(lean_object* v_sz_332_, lean_object* v_i_333_, lean_object* v_bs_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_332_);
lean_dec(v_sz_332_);
v_i_boxed_341_ = lean_unbox_usize(v_i_333_);
lean_dec(v_i_333_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_boxed_340_, v_i_boxed_341_, v_bs_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(lean_object* v_origins_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
size_t v_sz_349_; size_t v___x_350_; lean_object* v___x_351_; 
v_sz_349_ = lean_array_size(v_origins_343_);
v___x_350_ = ((size_t)0ULL);
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_349_, v___x_350_, v_origins_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_361_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_361_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_361_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_361_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_356_ = lean_array_to_list(v_a_352_);
v___x_357_ = l_Lean_MessageData_andList(v___x_356_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_357_);
v___x_359_ = v___x_354_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_351_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_351_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins___boxed(lean_object* v_origins_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_origins_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(lean_object* v_x_377_){
_start:
{
switch(lean_obj_tag(v_x_377_))
{
case 0:
{
lean_object* v_declName_379_; uint8_t v_post_380_; uint8_t v_inv_381_; uint8_t v___x_382_; lean_object* v_r_383_; 
v_declName_379_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_declName_379_);
v_post_380_ = lean_ctor_get_uint8(v_x_377_, sizeof(void*)*1);
v_inv_381_ = lean_ctor_get_uint8(v_x_377_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_377_);
v___x_382_ = 0;
v_r_383_ = l_Lean_MessageData_ofConstName(v_declName_379_, v___x_382_);
if (v_post_380_ == 0)
{
if (v_inv_381_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_r_383_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_r_383_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
else
{
if (v_inv_381_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_r_383_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_r_383_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
case 1:
{
lean_object* v_fvarId_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_403_; 
v_fvarId_394_ = lean_ctor_get(v_x_377_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_403_ == 0)
{
v___x_396_ = v_x_377_;
v_isShared_397_ = v_isSharedCheck_403_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_fvarId_394_);
lean_dec(v_x_377_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_403_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = l_Lean_mkFVar(v_fvarId_394_);
v___x_399_ = l_Lean_MessageData_ofExpr(v___x_398_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 0);
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
case 2:
{
lean_object* v_ref_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_ref_404_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_ref_404_);
lean_dec_ref(v_x_377_);
v___x_405_ = l_Lean_MessageData_ofSyntax(v_ref_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
default: 
{
lean_object* v_name_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_name_407_ = lean_ctor_get(v_x_377_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_415_ == 0)
{
v___x_409_ = v_x_377_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_name_407_);
lean_dec(v_x_377_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = l_Lean_MessageData_ofName(v_name_407_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg___boxed(lean_object* v_x_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(lean_object* v_x_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_419_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___boxed(lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(lean_object* v___x_439_, lean_object* v_as_440_, size_t v_sz_441_, size_t v_i_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_a_446_; uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_lt(v_i_442_, v_sz_441_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_b_443_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; uint8_t v___y_456_; 
v_a_452_ = lean_array_uget_borrowed(v_as_440_, v_i_442_);
if (lean_obj_tag(v_a_452_) == 0)
{
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_declName_457_; uint8_t v_inv_458_; lean_object* v_declName_459_; uint8_t v_inv_460_; uint8_t v___x_461_; 
v_declName_457_ = lean_ctor_get(v_a_452_, 0);
v_inv_458_ = lean_ctor_get_uint8(v_a_452_, sizeof(void*)*1 + 1);
v_declName_459_ = lean_ctor_get(v___x_439_, 0);
v_inv_460_ = lean_ctor_get_uint8(v___x_439_, sizeof(void*)*1 + 1);
v___x_461_ = lean_name_eq(v_declName_457_, v_declName_459_);
if (v___x_461_ == 0)
{
v___y_456_ = v___x_461_;
goto v___jp_455_;
}
else
{
if (v_inv_458_ == 0)
{
if (v_inv_460_ == 0)
{
v___y_456_ = v___x_461_;
goto v___jp_455_;
}
else
{
goto v___jp_453_;
}
}
else
{
v___y_456_ = v_inv_460_;
goto v___jp_455_;
}
}
}
else
{
goto v___jp_453_;
}
}
else
{
if (lean_obj_tag(v___x_439_) == 0)
{
goto v___jp_453_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = l_Lean_Meta_Origin_key(v_a_452_);
v___x_463_ = l_Lean_Meta_Origin_key(v___x_439_);
v___x_464_ = lean_name_eq(v___x_462_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_462_);
v___y_456_ = v___x_464_;
goto v___jp_455_;
}
}
v___jp_453_:
{
lean_object* v___x_454_; 
lean_inc(v_a_452_);
v___x_454_ = lean_array_push(v_b_443_, v_a_452_);
v_a_446_ = v___x_454_;
goto v___jp_445_;
}
v___jp_455_:
{
if (v___y_456_ == 0)
{
goto v___jp_453_;
}
else
{
v_a_446_ = v_b_443_;
goto v___jp_445_;
}
}
}
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_442_, v___x_447_);
v_i_442_ = v___x_448_;
v_b_443_ = v_a_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(lean_object* v___x_465_, lean_object* v_as_466_, lean_object* v_sz_467_, lean_object* v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_467_);
lean_dec(v_sz_467_);
v_i_boxed_472_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_465_, v_as_466_, v_sz_boxed_471_, v_i_boxed_472_, v_b_469_);
lean_dec_ref(v_as_466_);
lean_dec_ref(v___x_465_);
return v_res_473_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1);
v___x_478_ = l_Lean_MessageData_hint_x27(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5(void){
_start:
{
lean_object* v___x_482_; lean_object* v_msg_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
v_msg_483_ = l_Lean_stringToMessageData(v___x_482_);
return v_msg_483_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg(lean_object* v_thm_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_msg_500_; lean_object* v_origin_504_; lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v_usedTheorems_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; 
v_origin_504_ = lean_ctor_get(v_thm_490_, 4);
lean_inc_ref_n(v_origin_504_, 2);
lean_dec_ref(v_thm_490_);
v___x_505_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_504_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = lean_st_ref_get(v_a_493_);
v_usedTheorems_508_ = lean_ctor_get(v___x_507_, 3);
lean_inc_ref(v_usedTheorems_508_);
lean_dec(v___x_507_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3));
v___x_511_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_508_);
lean_dec_ref(v_usedTheorems_508_);
v_sz_512_ = lean_array_size(v___x_511_);
v___x_513_ = ((size_t)0ULL);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_504_, v___x_511_, v_sz_512_, v___x_513_, v___x_510_);
lean_dec_ref(v___x_511_);
lean_dec_ref(v_origin_504_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v_msg_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v_msg_516_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5);
v___x_517_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_a_506_);
v___x_519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v_msg_516_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_array_get_size(v_a_515_);
v___x_523_ = lean_nat_dec_eq(v___x_522_, v___x_509_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_515_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_a_525_);
v___x_528_ = l_Lean_MessageData_note(v___x_527_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_521_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v_msg_500_ = v___x_529_;
goto v___jp_499_;
}
else
{
lean_dec_ref(v___x_521_);
return v___x_524_;
}
}
else
{
lean_dec(v_a_515_);
v_msg_500_ = v___x_521_;
goto v___jp_499_;
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_a_506_);
v_a_530_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_514_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_514_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2, &l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once, _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v_msg_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(lean_object* v_thm_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(lean_object* v___x_548_, lean_object* v_as_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_548_, v_as_549_, v_sz_550_, v_i_551_, v_b_552_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(lean_object* v___x_562_, lean_object* v_as_563_, lean_object* v_sz_564_, lean_object* v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
size_t v_sz_boxed_575_; size_t v_i_boxed_576_; lean_object* v_res_577_; 
v_sz_boxed_575_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_576_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_562_, v_as_563_, v_sz_boxed_575_, v_i_boxed_576_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v_as_563_);
lean_dec_ref(v___x_562_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(lean_object* v_o_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v___x_583_; lean_object* v_toEnvExtension_584_; lean_object* v_asyncMode_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_linterSets_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_581_ = lean_st_ref_get(v___y_579_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_env_582_);
lean_dec(v___x_581_);
v___x_583_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_584_ = lean_ctor_get(v___x_583_, 0);
v_asyncMode_585_ = lean_ctor_get(v_toEnvExtension_584_, 2);
v___x_586_ = lean_box(1);
v___x_587_ = lean_box(0);
v_linterSets_588_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_586_, v___x_583_, v_env_582_, v_asyncMode_585_, v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_o_578_);
lean_ctor_set(v___x_589_, 1, v_linterSets_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(lean_object* v_o_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_591_, v___y_592_);
lean_dec(v___y_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_options_598_; lean_object* v___x_599_; 
v_options_598_ = lean_ctor_get(v___y_595_, 2);
lean_inc_ref(v_options_598_);
v___x_599_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_options_598_, v___y_596_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops(uint8_t v_force_604_, lean_object* v_ctxt_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_config_609_; uint8_t v_singlePass_610_; 
v_config_609_ = lean_ctor_get(v_ctxt_605_, 0);
v_singlePass_610_ = lean_ctor_get_uint8(v_config_609_, sizeof(void*)*3 + 2);
if (v_singlePass_610_ == 0)
{
if (v_force_604_ == 0)
{
lean_object* v___x_611_; lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_622_; 
v___x_611_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_606_, v_a_607_);
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_622_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_616_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_617_ = l_Lean_Linter_getLinterValue(v___x_616_, v_a_612_);
lean_dec(v_a_612_);
v___x_618_ = lean_box(v___x_617_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_618_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(v_force_604_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
else
{
uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = 0;
v___x_626_ = lean_box(v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_shouldCheckLoops___boxed(lean_object* v_force_628_, lean_object* v_ctxt_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
uint8_t v_force_boxed_633_; lean_object* v_res_634_; 
v_force_boxed_633_ = lean_unbox(v_force_628_);
v_res_634_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_633_, v_ctxt_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec_ref(v_ctxt_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(lean_object* v_o_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_635_, v___y_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(lean_object* v_o_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(lean_object* v_k_645_, lean_object* v_b_646_, lean_object* v_c_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
lean_inc(v___y_651_);
lean_inc_ref(v___y_650_);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
v___x_653_ = lean_apply_7(v_k_645_, v_b_646_, v_c_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, lean_box(0));
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(lean_object* v_k_654_, lean_object* v_b_655_, lean_object* v_c_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_654_, v_b_655_, v_c_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(lean_object* v_type_663_, lean_object* v_k_664_, uint8_t v_cleanupAnnotations_665_, uint8_t v_whnfType_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___f_672_; lean_object* v___x_673_; 
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_672_, 0, v_k_664_);
v___x_673_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_663_, v___f_672_, v_cleanupAnnotations_665_, v_whnfType_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_673_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_673_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(lean_object* v_type_690_, lean_object* v_k_691_, lean_object* v_cleanupAnnotations_692_, lean_object* v_whnfType_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_699_; uint8_t v_whnfType_boxed_700_; lean_object* v_res_701_; 
v_cleanupAnnotations_boxed_699_ = lean_unbox(v_cleanupAnnotations_692_);
v_whnfType_boxed_700_ = lean_unbox(v_whnfType_693_);
v_res_701_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_690_, v_k_691_, v_cleanupAnnotations_boxed_699_, v_whnfType_boxed_700_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(lean_object* v_00_u03b1_702_, lean_object* v_type_703_, lean_object* v_k_704_, uint8_t v_cleanupAnnotations_705_, uint8_t v_whnfType_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_type_703_, v_k_704_, v_cleanupAnnotations_705_, v_whnfType_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(lean_object* v_00_u03b1_713_, lean_object* v_type_714_, lean_object* v_k_715_, lean_object* v_cleanupAnnotations_716_, lean_object* v_whnfType_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_723_; uint8_t v_whnfType_boxed_724_; lean_object* v_res_725_; 
v_cleanupAnnotations_boxed_723_ = lean_unbox(v_cleanupAnnotations_716_);
v_whnfType_boxed_724_ = lean_unbox(v_whnfType_717_);
v_res_725_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(v_00_u03b1_713_, v_type_714_, v_k_715_, v_cleanupAnnotations_boxed_723_, v_whnfType_boxed_724_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(lean_object* v_msgData_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v_env_733_; lean_object* v___x_734_; lean_object* v_mctx_735_; lean_object* v_lctx_736_; lean_object* v_options_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_732_ = lean_st_ref_get(v___y_730_);
v_env_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_ref(v_env_733_);
lean_dec(v___x_732_);
v___x_734_ = lean_st_ref_get(v___y_728_);
v_mctx_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_mctx_735_);
lean_dec(v___x_734_);
v_lctx_736_ = lean_ctor_get(v___y_727_, 2);
v_options_737_ = lean_ctor_get(v___y_729_, 2);
lean_inc_ref(v_options_737_);
lean_inc_ref(v_lctx_736_);
v___x_738_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_738_, 0, v_env_733_);
lean_ctor_set(v___x_738_, 1, v_mctx_735_);
lean_ctor_set(v___x_738_, 2, v_lctx_736_);
lean_ctor_set(v___x_738_, 3, v_options_737_);
v___x_739_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_msgData_726_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(lean_object* v_msgData_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_748_; double v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_float_of_nat(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(lean_object* v_cls_752_, lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_ref_759_; lean_object* v___x_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_805_; 
v_ref_759_ = lean_ctor_get(v___y_756_, 5);
v___x_760_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_805_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_805_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_805_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v_traceState_766_; lean_object* v_env_767_; lean_object* v_nextMacroScope_768_; lean_object* v_ngen_769_; lean_object* v_auxDeclNGen_770_; lean_object* v_cache_771_; lean_object* v_messages_772_; lean_object* v_infoState_773_; lean_object* v_snapshotTasks_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_804_; 
v___x_765_ = lean_st_ref_take(v___y_757_);
v_traceState_766_ = lean_ctor_get(v___x_765_, 4);
v_env_767_ = lean_ctor_get(v___x_765_, 0);
v_nextMacroScope_768_ = lean_ctor_get(v___x_765_, 1);
v_ngen_769_ = lean_ctor_get(v___x_765_, 2);
v_auxDeclNGen_770_ = lean_ctor_get(v___x_765_, 3);
v_cache_771_ = lean_ctor_get(v___x_765_, 5);
v_messages_772_ = lean_ctor_get(v___x_765_, 6);
v_infoState_773_ = lean_ctor_get(v___x_765_, 7);
v_snapshotTasks_774_ = lean_ctor_get(v___x_765_, 8);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_804_ == 0)
{
v___x_776_ = v___x_765_;
v_isShared_777_ = v_isSharedCheck_804_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_snapshotTasks_774_);
lean_inc(v_infoState_773_);
lean_inc(v_messages_772_);
lean_inc(v_cache_771_);
lean_inc(v_traceState_766_);
lean_inc(v_auxDeclNGen_770_);
lean_inc(v_ngen_769_);
lean_inc(v_nextMacroScope_768_);
lean_inc(v_env_767_);
lean_dec(v___x_765_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_804_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
uint64_t v_tid_778_; lean_object* v_traces_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_803_; 
v_tid_778_ = lean_ctor_get_uint64(v_traceState_766_, sizeof(void*)*1);
v_traces_779_ = lean_ctor_get(v_traceState_766_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_traceState_766_);
if (v_isSharedCheck_803_ == 0)
{
v___x_781_ = v_traceState_766_;
v_isShared_782_ = v_isSharedCheck_803_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_traces_779_);
lean_dec(v_traceState_766_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_803_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; double v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
v___x_785_ = 0;
v___x_786_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
v___x_787_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_787_, 0, v_cls_752_);
lean_ctor_set(v___x_787_, 1, v___x_783_);
lean_ctor_set(v___x_787_, 2, v___x_786_);
lean_ctor_set_float(v___x_787_, sizeof(void*)*3, v___x_784_);
lean_ctor_set_float(v___x_787_, sizeof(void*)*3 + 8, v___x_784_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*3 + 16, v___x_785_);
v___x_788_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1));
v___x_789_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v_a_761_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
lean_inc(v_ref_759_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_ref_759_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = l_Lean_PersistentArray_push___redArg(v_traces_779_, v___x_790_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_791_);
v___x_793_ = v___x_781_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_791_);
lean_ctor_set_uint64(v_reuseFailAlloc_802_, sizeof(void*)*1, v_tid_778_);
v___x_793_ = v_reuseFailAlloc_802_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 4, v___x_793_);
v___x_795_ = v___x_776_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_env_767_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_nextMacroScope_768_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_ngen_769_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_auxDeclNGen_770_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_cache_771_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_messages_772_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_infoState_773_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_snapshotTasks_774_);
v___x_795_ = v_reuseFailAlloc_801_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_st_ref_set(v___y_757_, v___x_795_);
v___x_797_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_797_);
v___x_799_ = v___x_763_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(lean_object* v_cls_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_806_, v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(lean_object* v_opts_814_, lean_object* v_opt_815_){
_start:
{
lean_object* v_name_816_; lean_object* v_defValue_817_; lean_object* v_map_818_; lean_object* v___x_819_; 
v_name_816_ = lean_ctor_get(v_opt_815_, 0);
v_defValue_817_ = lean_ctor_get(v_opt_815_, 1);
v_map_818_ = lean_ctor_get(v_opts_814_, 0);
v___x_819_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_818_, v_name_816_);
if (lean_obj_tag(v___x_819_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = lean_unbox(v_defValue_817_);
return v___x_820_;
}
else
{
lean_object* v_val_821_; 
v_val_821_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_val_821_);
lean_dec_ref(v___x_819_);
if (lean_obj_tag(v_val_821_) == 1)
{
uint8_t v_v_822_; 
v_v_822_ = lean_ctor_get_uint8(v_val_821_, 0);
lean_dec_ref(v_val_821_);
return v_v_822_;
}
else
{
uint8_t v___x_823_; 
lean_dec(v_val_821_);
v___x_823_ = lean_unbox(v_defValue_817_);
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_opts_824_, lean_object* v_opt_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_824_, v_opt_825_);
lean_dec_ref(v_opt_825_);
lean_dec_ref(v_opts_824_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v___y_836_, uint8_t v_suppressElabErrors_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_838_) == 1)
{
lean_object* v_pre_839_; 
v_pre_839_ = lean_ctor_get(v_x_838_, 0);
switch(lean_obj_tag(v_pre_839_))
{
case 1:
{
lean_object* v_pre_840_; 
v_pre_840_ = lean_ctor_get(v_pre_839_, 0);
switch(lean_obj_tag(v_pre_840_))
{
case 0:
{
lean_object* v_str_841_; lean_object* v_str_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_str_841_ = lean_ctor_get(v_x_838_, 1);
v_str_842_ = lean_ctor_get(v_pre_839_, 1);
v___x_843_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_844_ = lean_string_dec_eq(v_str_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_846_ = lean_string_dec_eq(v_str_842_, v___x_845_);
if (v___x_846_ == 0)
{
return v___y_836_;
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_848_ = lean_string_dec_eq(v_str_841_, v___x_847_);
if (v___x_848_ == 0)
{
return v___y_836_;
}
else
{
return v_suppressElabErrors_837_;
}
}
}
else
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_850_ = lean_string_dec_eq(v_str_841_, v___x_849_);
if (v___x_850_ == 0)
{
return v___y_836_;
}
else
{
return v_suppressElabErrors_837_;
}
}
}
case 1:
{
lean_object* v_pre_851_; 
v_pre_851_ = lean_ctor_get(v_pre_840_, 0);
if (lean_obj_tag(v_pre_851_) == 0)
{
lean_object* v_str_852_; lean_object* v_str_853_; lean_object* v_str_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_str_852_ = lean_ctor_get(v_x_838_, 1);
v_str_853_ = lean_ctor_get(v_pre_839_, 1);
v_str_854_ = lean_ctor_get(v_pre_840_, 1);
v___x_855_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_856_ = lean_string_dec_eq(v_str_854_, v___x_855_);
if (v___x_856_ == 0)
{
return v___y_836_;
}
else
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_858_ = lean_string_dec_eq(v_str_853_, v___x_857_);
if (v___x_858_ == 0)
{
return v___y_836_;
}
else
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_860_ = lean_string_dec_eq(v_str_852_, v___x_859_);
if (v___x_860_ == 0)
{
return v___y_836_;
}
else
{
return v_suppressElabErrors_837_;
}
}
}
}
else
{
return v___y_836_;
}
}
default: 
{
return v___y_836_;
}
}
}
case 0:
{
lean_object* v_str_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_str_861_ = lean_ctor_get(v_x_838_, 1);
v___x_862_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_863_ = lean_string_dec_eq(v_str_861_, v___x_862_);
if (v___x_863_ == 0)
{
return v___y_836_;
}
else
{
return v_suppressElabErrors_837_;
}
}
default: 
{
return v___y_836_;
}
}
}
else
{
return v___y_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_864_, lean_object* v_suppressElabErrors_865_, lean_object* v_x_866_){
_start:
{
uint8_t v___y_24899__boxed_867_; uint8_t v_suppressElabErrors_boxed_868_; uint8_t v_res_869_; lean_object* v_r_870_; 
v___y_24899__boxed_867_ = lean_unbox(v___y_864_);
v_suppressElabErrors_boxed_868_ = lean_unbox(v_suppressElabErrors_865_);
v_res_869_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v___y_24899__boxed_867_, v_suppressElabErrors_boxed_868_, v_x_866_);
lean_dec(v_x_866_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_871_, lean_object* v_msgData_872_, uint8_t v_severity_873_, uint8_t v_isSilent_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; uint8_t v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; uint8_t v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; uint8_t v___y_923_; lean_object* v___y_924_; lean_object* v___y_942_; lean_object* v___y_943_; uint8_t v___y_944_; lean_object* v___y_945_; uint8_t v___y_946_; uint8_t v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_953_; uint8_t v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; uint8_t v___y_958_; uint8_t v___y_959_; uint8_t v___x_964_; lean_object* v___y_966_; lean_object* v___y_967_; uint8_t v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; uint8_t v___y_972_; uint8_t v___y_974_; uint8_t v___x_989_; 
v___x_964_ = 2;
v___x_989_ = l_Lean_instBEqMessageSeverity_beq(v_severity_873_, v___x_964_);
if (v___x_989_ == 0)
{
v___y_974_ = v___x_989_;
goto v___jp_973_;
}
else
{
uint8_t v___x_990_; 
lean_inc_ref(v_msgData_872_);
v___x_990_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_872_);
v___y_974_ = v___x_990_;
goto v___jp_973_;
}
v___jp_880_:
{
lean_object* v___x_890_; lean_object* v_currNamespace_891_; lean_object* v_openDecls_892_; lean_object* v_env_893_; lean_object* v_nextMacroScope_894_; lean_object* v_ngen_895_; lean_object* v_auxDeclNGen_896_; lean_object* v_traceState_897_; lean_object* v_cache_898_; lean_object* v_messages_899_; lean_object* v_infoState_900_; lean_object* v_snapshotTasks_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_915_; 
v___x_890_ = lean_st_ref_take(v___y_889_);
v_currNamespace_891_ = lean_ctor_get(v___y_888_, 6);
v_openDecls_892_ = lean_ctor_get(v___y_888_, 7);
v_env_893_ = lean_ctor_get(v___x_890_, 0);
v_nextMacroScope_894_ = lean_ctor_get(v___x_890_, 1);
v_ngen_895_ = lean_ctor_get(v___x_890_, 2);
v_auxDeclNGen_896_ = lean_ctor_get(v___x_890_, 3);
v_traceState_897_ = lean_ctor_get(v___x_890_, 4);
v_cache_898_ = lean_ctor_get(v___x_890_, 5);
v_messages_899_ = lean_ctor_get(v___x_890_, 6);
v_infoState_900_ = lean_ctor_get(v___x_890_, 7);
v_snapshotTasks_901_ = lean_ctor_get(v___x_890_, 8);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_915_ == 0)
{
v___x_903_ = v___x_890_;
v_isShared_904_ = v_isSharedCheck_915_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_snapshotTasks_901_);
lean_inc(v_infoState_900_);
lean_inc(v_messages_899_);
lean_inc(v_cache_898_);
lean_inc(v_traceState_897_);
lean_inc(v_auxDeclNGen_896_);
lean_inc(v_ngen_895_);
lean_inc(v_nextMacroScope_894_);
lean_inc(v_env_893_);
lean_dec(v___x_890_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_915_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
lean_inc(v_openDecls_892_);
lean_inc(v_currNamespace_891_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_currNamespace_891_);
lean_ctor_set(v___x_905_, 1, v_openDecls_892_);
v___x_906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___y_886_);
lean_inc_ref(v___y_883_);
lean_inc_ref(v___y_882_);
v___x_907_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_907_, 0, v___y_882_);
lean_ctor_set(v___x_907_, 1, v___y_884_);
lean_ctor_set(v___x_907_, 2, v___y_887_);
lean_ctor_set(v___x_907_, 3, v___y_883_);
lean_ctor_set(v___x_907_, 4, v___x_906_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*5, v___y_885_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*5 + 1, v___y_881_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*5 + 2, v_isSilent_874_);
v___x_908_ = l_Lean_MessageLog_add(v___x_907_, v_messages_899_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 6, v___x_908_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_env_893_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_nextMacroScope_894_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_ngen_895_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_auxDeclNGen_896_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_traceState_897_);
lean_ctor_set(v_reuseFailAlloc_914_, 5, v_cache_898_);
lean_ctor_set(v_reuseFailAlloc_914_, 6, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 7, v_infoState_900_);
lean_ctor_set(v_reuseFailAlloc_914_, 8, v_snapshotTasks_901_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_st_ref_set(v___y_889_, v___x_910_);
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
v___jp_916_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_940_; 
v___x_925_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_872_);
v___x_926_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_925_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_940_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc_ref_n(v___y_921_, 2);
v___x_931_ = l_Lean_FileMap_toPosition(v___y_921_, v___y_922_);
lean_dec(v___y_922_);
v___x_932_ = l_Lean_FileMap_toPosition(v___y_921_, v___y_924_);
lean_dec(v___y_924_);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4));
if (v___y_918_ == 0)
{
lean_del_object(v___x_929_);
lean_dec_ref(v___y_917_);
v___y_881_ = v___y_920_;
v___y_882_ = v___y_919_;
v___y_883_ = v___x_934_;
v___y_884_ = v___x_931_;
v___y_885_ = v___y_923_;
v___y_886_ = v_a_927_;
v___y_887_ = v___x_933_;
v___y_888_ = v___y_877_;
v___y_889_ = v___y_878_;
goto v___jp_880_;
}
else
{
uint8_t v___x_935_; 
lean_inc(v_a_927_);
v___x_935_ = l_Lean_MessageData_hasTag(v___y_917_, v_a_927_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_931_);
lean_dec(v_a_927_);
v___x_936_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_936_);
v___x_938_ = v___x_929_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_del_object(v___x_929_);
v___y_881_ = v___y_920_;
v___y_882_ = v___y_919_;
v___y_883_ = v___x_934_;
v___y_884_ = v___x_931_;
v___y_885_ = v___y_923_;
v___y_886_ = v_a_927_;
v___y_887_ = v___x_933_;
v___y_888_ = v___y_877_;
v___y_889_ = v___y_878_;
goto v___jp_880_;
}
}
}
}
v___jp_941_:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Syntax_getTailPos_x3f(v___y_948_, v___y_947_);
lean_dec(v___y_948_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_inc(v___y_949_);
v___y_917_ = v___y_942_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_945_;
v___y_920_ = v___y_944_;
v___y_921_ = v___y_943_;
v___y_922_ = v___y_949_;
v___y_923_ = v___y_947_;
v___y_924_ = v___y_949_;
goto v___jp_916_;
}
else
{
lean_object* v_val_951_; 
v_val_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref(v___x_950_);
v___y_917_ = v___y_942_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_945_;
v___y_920_ = v___y_944_;
v___y_921_ = v___y_943_;
v___y_922_ = v___y_949_;
v___y_923_ = v___y_947_;
v___y_924_ = v_val_951_;
goto v___jp_916_;
}
}
v___jp_952_:
{
lean_object* v_ref_960_; lean_object* v___x_961_; 
v_ref_960_ = l_Lean_replaceRef(v_ref_871_, v___y_957_);
v___x_961_ = l_Lean_Syntax_getPos_x3f(v_ref_960_, v___y_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_unsigned_to_nat(0u);
v___y_942_ = v___y_953_;
v___y_943_ = v___y_956_;
v___y_944_ = v___y_959_;
v___y_945_ = v___y_955_;
v___y_946_ = v___y_954_;
v___y_947_ = v___y_958_;
v___y_948_ = v_ref_960_;
v___y_949_ = v___x_962_;
goto v___jp_941_;
}
else
{
lean_object* v_val_963_; 
v_val_963_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_963_);
lean_dec_ref(v___x_961_);
v___y_942_ = v___y_953_;
v___y_943_ = v___y_956_;
v___y_944_ = v___y_959_;
v___y_945_ = v___y_955_;
v___y_946_ = v___y_954_;
v___y_947_ = v___y_958_;
v___y_948_ = v_ref_960_;
v___y_949_ = v_val_963_;
goto v___jp_941_;
}
}
v___jp_965_:
{
if (v___y_972_ == 0)
{
v___y_953_ = v___y_970_;
v___y_954_ = v___y_968_;
v___y_955_ = v___y_967_;
v___y_956_ = v___y_966_;
v___y_957_ = v___y_969_;
v___y_958_ = v___y_971_;
v___y_959_ = v_severity_873_;
goto v___jp_952_;
}
else
{
v___y_953_ = v___y_970_;
v___y_954_ = v___y_968_;
v___y_955_ = v___y_967_;
v___y_956_ = v___y_966_;
v___y_957_ = v___y_969_;
v___y_958_ = v___y_971_;
v___y_959_ = v___x_964_;
goto v___jp_952_;
}
}
v___jp_973_:
{
if (v___y_974_ == 0)
{
lean_object* v_fileName_975_; lean_object* v_fileMap_976_; lean_object* v_options_977_; lean_object* v_ref_978_; uint8_t v_suppressElabErrors_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___f_982_; uint8_t v___x_983_; uint8_t v___x_984_; 
v_fileName_975_ = lean_ctor_get(v___y_877_, 0);
v_fileMap_976_ = lean_ctor_get(v___y_877_, 1);
v_options_977_ = lean_ctor_get(v___y_877_, 2);
v_ref_978_ = lean_ctor_get(v___y_877_, 5);
v_suppressElabErrors_979_ = lean_ctor_get_uint8(v___y_877_, sizeof(void*)*14 + 1);
v___x_980_ = lean_box(v___y_974_);
v___x_981_ = lean_box(v_suppressElabErrors_979_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_982_, 0, v___x_980_);
lean_closure_set(v___f_982_, 1, v___x_981_);
v___x_983_ = 1;
v___x_984_ = l_Lean_instBEqMessageSeverity_beq(v_severity_873_, v___x_983_);
if (v___x_984_ == 0)
{
v___y_966_ = v_fileMap_976_;
v___y_967_ = v_fileName_975_;
v___y_968_ = v_suppressElabErrors_979_;
v___y_969_ = v_ref_978_;
v___y_970_ = v___f_982_;
v___y_971_ = v___y_974_;
v___y_972_ = v___x_984_;
goto v___jp_965_;
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = l_Lean_warningAsError;
v___x_986_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_options_977_, v___x_985_);
v___y_966_ = v_fileMap_976_;
v___y_967_ = v_fileName_975_;
v___y_968_ = v_suppressElabErrors_979_;
v___y_969_ = v_ref_978_;
v___y_970_ = v___f_982_;
v___y_971_ = v___y_974_;
v___y_972_ = v___x_986_;
goto v___jp_965_;
}
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v_msgData_872_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_991_, lean_object* v_msgData_992_, lean_object* v_severity_993_, lean_object* v_isSilent_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
uint8_t v_severity_boxed_1000_; uint8_t v_isSilent_boxed_1001_; lean_object* v_res_1002_; 
v_severity_boxed_1000_ = lean_unbox(v_severity_993_);
v_isSilent_boxed_1001_ = lean_unbox(v_isSilent_994_);
v_res_1002_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_991_, v_msgData_992_, v_severity_boxed_1000_, v_isSilent_boxed_1001_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v_ref_991_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(lean_object* v_ref_1003_, lean_object* v_msgData_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = 1;
v___x_1014_ = 0;
v___x_1015_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1003_, v_msgData_1004_, v___x_1013_, v___x_1014_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(lean_object* v_ref_1016_, lean_object* v_msgData_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_1016_, v_msgData_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v_ref_1016_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(lean_object* v_linterOption_1033_, lean_object* v_stx_1034_, lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_name_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1059_; 
v_name_1044_ = lean_ctor_get(v_linterOption_1033_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_linterOption_1033_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v_linterOption_1033_, 1);
lean_dec(v_unused_1060_);
v___x_1046_ = v_linterOption_1033_;
v_isShared_1047_ = v_isSharedCheck_1059_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_name_1044_);
lean_dec(v_linterOption_1033_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1059_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1048_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
lean_inc(v_name_1044_);
v___x_1049_ = l_Lean_MessageData_ofName(v_name_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 7);
lean_ctor_set(v___x_1046_, 1, v___x_1049_);
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1051_ = v___x_1046_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_disable_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v_disable_1054_ = l_Lean_MessageData_note(v___x_1053_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_msg_1035_);
lean_ctor_set(v___x_1055_, 1, v_disable_1054_);
v___x_1056_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_name_1044_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_1034_, v___x_1056_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(lean_object* v_linterOption_1061_, lean_object* v_stx_1062_, lean_object* v_msg_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v_linterOption_1061_, v_stx_1062_, v_msg_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec(v_stx_1062_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(lean_object* v_msgData_1073_, uint8_t v_severity_1074_, uint8_t v_isSilent_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_ref_1084_; lean_object* v___x_1085_; 
v_ref_1084_ = lean_ctor_get(v___y_1081_, 5);
v___x_1085_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1084_, v_msgData_1073_, v_severity_1074_, v_isSilent_1075_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(lean_object* v_msgData_1086_, lean_object* v_severity_1087_, lean_object* v_isSilent_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_severity_boxed_1097_; uint8_t v_isSilent_boxed_1098_; lean_object* v_res_1099_; 
v_severity_boxed_1097_ = lean_unbox(v_severity_1087_);
v_isSilent_boxed_1098_ = lean_unbox(v_isSilent_1088_);
v_res_1099_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1086_, v_severity_boxed_1097_, v_isSilent_boxed_1098_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(lean_object* v_msgData_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = 1;
v___x_1110_ = 0;
v___x_1111_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(v_msgData_1100_, v___x_1109_, v___x_1110_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(lean_object* v_msgData_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_msgData_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1132_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3));
v___x_1133_ = l_Lean_Name_append(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0(lean_object* v___x_1140_, uint8_t v_force_1141_, lean_object* v_thm_1142_, lean_object* v_origin_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___x_1184_; 
lean_inc(v___y_1150_);
lean_inc_ref(v___y_1149_);
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc(v___y_1144_);
v___x_1184_ = lean_simp(v___x_1140_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v___y_1144_);
lean_dec_ref(v_origin_1143_);
lean_dec_ref(v_thm_1142_);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v___x_1184_, 0);
lean_dec(v_unused_1193_);
v___x_1186_ = v___x_1184_;
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v___x_1184_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(0);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1218_; 
v_a_1194_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1196_ = v___x_1184_;
v_isShared_1197_ = v_isSharedCheck_1218_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1184_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1218_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_Exception_isInterrupt(v_a_1194_);
if (v___x_1198_ == 0)
{
lean_object* v_options_1199_; uint8_t v_hasTrace_1200_; 
lean_del_object(v___x_1196_);
v_options_1199_ = lean_ctor_get(v___y_1149_, 2);
v_hasTrace_1200_ = lean_ctor_get_uint8(v_options_1199_, sizeof(void*)*1);
if (v_hasTrace_1200_ == 0)
{
lean_dec(v_a_1194_);
lean_dec_ref(v_origin_1143_);
v___y_1153_ = v___y_1144_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___y_1146_;
v___y_1156_ = v___y_1147_;
v___y_1157_ = v___y_1148_;
v___y_1158_ = v___y_1149_;
v___y_1159_ = v___y_1150_;
goto v___jp_1152_;
}
else
{
lean_object* v_inheritedTraceOptions_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_inheritedTraceOptions_1201_ = lean_ctor_get(v___y_1149_, 13);
v___x_1202_ = ((lean_object*)(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2));
v___x_1203_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4);
v___x_1204_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1201_, v_options_1199_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec(v_a_1194_);
lean_dec_ref(v_origin_1143_);
v___y_1153_ = v___y_1144_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___y_1146_;
v___y_1156_ = v___y_1147_;
v___y_1157_ = v___y_1148_;
v___y_1158_ = v___y_1149_;
v___y_1159_ = v___y_1150_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1205_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_1143_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_a_1206_);
v___x_1209_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__0___closed__8, &l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once, _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = l_Lean_Exception_toMessageData(v_a_1194_);
v___x_1212_ = l_Lean_indentD(v___x_1211_);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1210_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v___x_1202_, v___x_1213_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec_ref(v___x_1214_);
v___y_1153_ = v___y_1144_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___y_1146_;
v___y_1156_ = v___y_1147_;
v___y_1157_ = v___y_1148_;
v___y_1158_ = v___y_1149_;
v___y_1159_ = v___y_1150_;
goto v___jp_1152_;
}
else
{
lean_dec(v___y_1144_);
lean_dec_ref(v_thm_1142_);
return v___x_1214_;
}
}
}
}
else
{
lean_object* v___x_1216_; 
lean_dec(v___y_1144_);
lean_dec_ref(v_origin_1143_);
lean_dec_ref(v_thm_1142_);
if (v_isShared_1197_ == 0)
{
v___x_1216_ = v___x_1196_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1194_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
v___jp_1152_:
{
if (v_force_1141_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1142_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_ref_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref(v___x_1160_);
v_ref_1162_ = lean_ctor_get(v___y_1158_, 5);
v___x_1163_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
v___x_1164_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(v___x_1163_, v_ref_1162_, v_a_1161_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1153_);
return v___x_1164_;
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v___y_1153_);
v_a_1165_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1160_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1160_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_Simp_mkLoopWarningMsg(v_thm_1142_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(v_a_1174_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1153_);
return v___x_1175_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v___y_1153_);
v_a_1176_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1173_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1173_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__0___boxed(lean_object* v___x_1219_, lean_object* v_force_1220_, lean_object* v_thm_1221_, lean_object* v_origin_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_force_boxed_1231_; lean_object* v_res_1232_; 
v_force_boxed_1231_ = lean_unbox(v_force_1220_);
v_res_1232_ = l_Lean_Meta_Simp_checkLoops___lam__0(v___x_1219_, v_force_boxed_1231_, v_thm_1221_, v_origin_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_unsigned_to_nat(16u);
v___x_1235_ = lean_mk_array(v___x_1234_, v___x_1233_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__0, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
return v___x_1238_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__2, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_unsigned_to_nat(32u);
v___x_1246_ = lean_mk_empty_array_with_capacity(v___x_1245_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6(void){
_start:
{
size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1248_ = ((size_t)5ULL);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_unsigned_to_nat(32u);
v___x_1251_ = lean_mk_empty_array_with_capacity(v___x_1250_);
v___x_1252_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__5, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5);
v___x_1253_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_ctor_set(v___x_1253_, 2, v___x_1249_);
lean_ctor_set(v___x_1253_, 3, v___x_1249_);
lean_ctor_set_usize(v___x_1253_, 4, v___x_1248_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__6, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6);
v___x_1255_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
lean_ctor_set(v___x_1256_, 3, v___x_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1(uint8_t v_force_1257_, lean_object* v_thm_1258_, lean_object* v_origin_1259_, uint8_t v_a_1260_, lean_object* v_ctxt_1261_, lean_object* v_methods_1262_, lean_object* v___xs_1263_, lean_object* v_type_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
v___x_1270_ = lean_whnf(v_type_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = l_Lean_Expr_appArg_x21(v_a_1271_);
lean_dec(v_a_1271_);
v___x_1273_ = lean_box(v_force_1257_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1274_, 0, v___x_1272_);
lean_closure_set(v___f_1274_, 1, v___x_1273_);
lean_closure_set(v___f_1274_, 2, v_thm_1258_);
lean_closure_set(v___f_1274_, 3, v_origin_1259_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__1, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1);
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__3, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3);
v___x_1278_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*2, v_a_1260_);
v___x_1279_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__4, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4);
v___x_1280_ = lean_obj_once(&l_Lean_Meta_Simp_checkLoops___lam__1___closed__7, &l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once, _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7);
v___x_1281_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1278_);
lean_ctor_set(v___x_1281_, 1, v___x_1276_);
lean_ctor_set(v___x_1281_, 2, v___x_1276_);
lean_ctor_set(v___x_1281_, 3, v___x_1279_);
lean_ctor_set(v___x_1281_, 4, v___x_1275_);
lean_ctor_set(v___x_1281_, 5, v___x_1280_);
v___x_1282_ = l_Lean_Meta_Simp_SimpM_run___redArg(v_ctxt_1261_, v___x_1281_, v_methods_1262_, v___f_1274_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1290_; 
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1282_, 0);
lean_dec(v_unused_1291_);
v___x_1284_ = v___x_1282_;
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v___x_1282_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1282_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1282_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_methods_1262_);
lean_dec_ref(v_ctxt_1261_);
lean_dec_ref(v_origin_1259_);
lean_dec_ref(v_thm_1258_);
v_a_1300_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1270_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1270_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___lam__1___boxed(lean_object* v_force_1308_, lean_object* v_thm_1309_, lean_object* v_origin_1310_, lean_object* v_a_1311_, lean_object* v_ctxt_1312_, lean_object* v_methods_1313_, lean_object* v___xs_1314_, lean_object* v_type_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v_force_boxed_1321_; uint8_t v_a_25602__boxed_1322_; lean_object* v_res_1323_; 
v_force_boxed_1321_ = lean_unbox(v_force_1308_);
v_a_25602__boxed_1322_ = lean_unbox(v_a_1311_);
v_res_1323_ = l_Lean_Meta_Simp_checkLoops___lam__1(v_force_boxed_1321_, v_thm_1309_, v_origin_1310_, v_a_25602__boxed_1322_, v_ctxt_1312_, v_methods_1313_, v___xs_1314_, v_type_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___xs_1314_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops(uint8_t v_force_1324_, lean_object* v_ctxt_1325_, lean_object* v_methods_1326_, lean_object* v_thm_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Meta_Simp_shouldCheckLoops(v_force_1324_, v_ctxt_1325_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1373_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1373_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1373_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_unbox(v_a_1334_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v_a_1334_);
lean_dec_ref(v_thm_1327_);
lean_dec_ref(v_methods_1326_);
lean_dec_ref(v_ctxt_1325_);
v___x_1339_ = lean_box(0);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v_proof_1343_; lean_object* v_origin_1344_; uint8_t v___x_1345_; 
v_proof_1343_ = lean_ctor_get(v_thm_1327_, 2);
v_origin_1344_ = lean_ctor_get(v_thm_1327_, 4);
lean_inc_ref(v_origin_1344_);
v___x_1345_ = l_Lean_Expr_hasFVar(v_proof_1343_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_del_object(v___x_1336_);
lean_inc_ref(v_thm_1327_);
v___x_1346_ = l_Lean_Meta_SimpTheorem_getValue(v_thm_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v___x_1346_);
lean_inc(v_a_1331_);
lean_inc_ref(v_a_1330_);
lean_inc(v_a_1329_);
lean_inc_ref(v_a_1328_);
v___x_1348_ = lean_infer_type(v_a_1347_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1348_);
v___x_1350_ = lean_box(v_force_1324_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_checkLoops___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1351_, 0, v___x_1350_);
lean_closure_set(v___f_1351_, 1, v_thm_1327_);
lean_closure_set(v___f_1351_, 2, v_origin_1344_);
lean_closure_set(v___f_1351_, 3, v_a_1334_);
lean_closure_set(v___f_1351_, 4, v_ctxt_1325_);
lean_closure_set(v___f_1351_, 5, v_methods_1326_);
v___x_1352_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_1349_, v___f_1351_, v___x_1345_, v___x_1345_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1352_;
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_origin_1344_);
lean_dec(v_a_1334_);
lean_dec_ref(v_thm_1327_);
lean_dec_ref(v_methods_1326_);
lean_dec_ref(v_ctxt_1325_);
v_a_1353_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1348_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1348_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
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
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_origin_1344_);
lean_dec(v_a_1334_);
lean_dec_ref(v_thm_1327_);
lean_dec_ref(v_methods_1326_);
lean_dec_ref(v_ctxt_1325_);
v_a_1361_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1346_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1346_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
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
else
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec_ref(v_origin_1344_);
lean_dec(v_a_1334_);
lean_dec_ref(v_thm_1327_);
lean_dec_ref(v_methods_1326_);
lean_dec_ref(v_ctxt_1325_);
v___x_1369_ = lean_box(0);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1369_);
v___x_1371_ = v___x_1336_;
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
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_thm_1327_);
lean_dec_ref(v_methods_1326_);
lean_dec_ref(v_ctxt_1325_);
v_a_1374_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1333_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1333_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_checkLoops___boxed(lean_object* v_force_1382_, lean_object* v_ctxt_1383_, lean_object* v_methods_1384_, lean_object* v_thm_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
uint8_t v_force_boxed_1391_; lean_object* v_res_1392_; 
v_force_boxed_1391_ = lean_unbox(v_force_1382_);
v_res_1392_ = l_Lean_Meta_Simp_checkLoops(v_force_boxed_1391_, v_ctxt_1383_, v_methods_1384_, v_thm_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(lean_object* v_cls_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(v_cls_1393_, v_msg_1394_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(lean_object* v_cls_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(v_cls_1404_, v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(lean_object* v_ref_1415_, lean_object* v_msgData_1416_, uint8_t v_severity_1417_, uint8_t v_isSilent_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_1415_, v_msgData_1416_, v_severity_1417_, v_isSilent_1418_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_1428_, lean_object* v_msgData_1429_, lean_object* v_severity_1430_, lean_object* v_isSilent_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v_severity_boxed_1440_; uint8_t v_isSilent_boxed_1441_; lean_object* v_res_1442_; 
v_severity_boxed_1440_ = lean_unbox(v_severity_1430_);
v_isSilent_boxed_1441_ = lean_unbox(v_isSilent_1431_);
v_res_1442_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_1428_, v_msgData_1429_, v_severity_boxed_1440_, v_isSilent_boxed_1441_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec(v_ref_1428_);
return v_res_1442_;
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
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
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

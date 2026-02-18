// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.ShowState
// Imports: public import Lean.Elab.Tactic.Grind.Filter import Lean.Meta.Tactic.Grind.PP import Lean.Meta.Tactic.Grind.EMatchTheoremParam import Lean.Meta.Tactic.Grind.Split
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "facts"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 104, 51, 228, 98, 188, 251, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Asserted facts"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4_value;
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_ppExprArray(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no facts"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindFilter"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value;
lean_object* l_Lean_Elab_Tactic_Grind_elabFilter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "showAsserted"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value),LEAN_SCALAR_PTR_LITERAL(19, 9, 52, 210, 246, 83, 42, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value;
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ShowState"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 25, 164, 64, 171, 22, 6, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 19, 40, 233, 34, 161, 117, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 78, 84, 89, 236, 187, 159, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 245, 207, 60, 37, 134, 98, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(38, 49, 162, 201, 131, 208, 27, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 71, 128, 234, 115, 187, 122, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalShowAsserted"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(200, 208, 203, 159, 70, 103, 81, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14_value;
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "props"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 109, 51, 84, 90, 92, 70, 19)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " propositions"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "no "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTrue"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 221, 230, 107, 62, 158, 128, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(55, 133, 155, 61, 50, 240, 42, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowTrue"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 147, 90, 193, 92, 229, 28, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showFalse"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 23, 10, 157, 249, 80, 147, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalShowFalse"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 252, 51, 157, 108, 134, 132, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isTrue___boxed(lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isTrue___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__0_value;
lean_object* l_Lean_Expr_isFalse___boxed(lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFalse___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__1_value;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_ppEqc(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eqc"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 40, 20, 175, 160, 100, 35, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Equivalence classes"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "others"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no equivalence classes"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showEqcs"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 3, 250, 60, 240, 18, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowEqcs"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 119, 28, 131, 183, 128, 4, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1_value;
static double l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
static lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Grind state"};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5_value;
static lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showState"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 80, 82, 248, 223, 67, 174, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalShowState"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 96, 229, 223, 171, 103, 139, 248)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 90, 54, 167, 41, 130, 106, 252)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_anchorToString(lean_object*, uint64_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "splits"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 201, 206, 84, 124, 223, 95, 96)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Case split candidates"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "no case splits"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Filter_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showCases"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 129, 48, 5, 176, 175, 163, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalShowCases"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 115, 106, 2, 47, 9, 123, 219)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___boxed(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2;
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 106, 229, 125, 19, 158, 75, 156)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "thms"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 43, 249, 113, 45, 82, 7, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Local theorems"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5;
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getLocalTheoremAnchors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "showLocalThms"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 164, 136, 213, 0, 240, 18, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalShowLocalThms"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 150, 229, 48, 187, 110, 180, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___boxed(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 150, 74, 14, 71, 142, 109, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value;
lean_object* l_Lean_Elab_Tactic_Grind_evalGrindTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 168, 61, 18, 39, 162, 48, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_10);
x_11 = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(x_10, x_1, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_18 = lean_unbox(x_12);
lean_dec(x_12);
if (x_18 == 0)
{
lean_dec(x_10);
x_13 = x_5;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_array_push(x_5, x_10);
x_13 = x_19;
goto block_17;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_13;
goto _start;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_st_ref_get(x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 11);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_15);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0;
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_16);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
if (x_20 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_16);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(x_1, x_16, x_24, x_25, x_19, x_2, x_9);
lean_dec_ref(x_16);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_18);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(x_1, x_16, x_27, x_28, x_19, x_2, x_9);
lean_dec_ref(x_16);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed), 12, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Array_isEmpty___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1));
x_16 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2));
x_17 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4));
x_18 = l_Lean_Meta_Grind_ppExprArray(x_15, x_16, x_13, x_17, x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = lean_box(0);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Array_isEmpty___redArg(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1));
x_24 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2));
x_25 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4));
x_26 = l_Lean_Meta_Grind_ppExprArray(x_23, x_24, x_21, x_25, x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_109; uint8_t x_125; 
x_100 = 2;
x_125 = l_Lean_instBEqMessageSeverity_beq(x_3, x_100);
if (x_125 == 0)
{
x_109 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
lean_inc_ref(x_2);
x_126 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_109 = x_126;
goto block_124;
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_18);
x_21 = lean_ctor_get(x_17, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 7);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_13);
lean_ctor_set(x_27, 3, x_11);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_24);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_18, x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
x_38 = lean_ctor_get(x_20, 6);
x_39 = lean_ctor_get(x_20, 7);
x_40 = lean_ctor_get(x_20, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_22);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_14);
lean_ctor_set(x_43, 2, x_13);
lean_ctor_set(x_43, 3, x_11);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_4);
x_44 = l_Lean_MessageLog_add(x_43, x_38);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_18, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_59 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(x_58, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_52);
x_62 = l_Lean_FileMap_toPosition(x_52, x_54);
lean_dec(x_54);
x_63 = l_Lean_FileMap_toPosition(x_52, x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
if (x_53 == 0)
{
lean_free_object(x_59);
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_65;
x_12 = x_61;
x_13 = x_64;
x_14 = x_62;
x_15 = x_55;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_61);
x_66 = l_Lean_MessageData_hasTag(x_50, x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_55);
lean_dec_ref(x_7);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_free_object(x_59);
x_10 = x_51;
x_11 = x_65;
x_12 = x_61;
x_13 = x_64;
x_14 = x_62;
x_15 = x_55;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
lean_inc_ref(x_52);
x_69 = l_Lean_FileMap_toPosition(x_52, x_54);
lean_dec(x_54);
x_70 = l_Lean_FileMap_toPosition(x_52, x_57);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
if (x_53 == 0)
{
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_72;
x_12 = x_68;
x_13 = x_71;
x_14 = x_69;
x_15 = x_55;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_73; 
lean_inc(x_68);
x_73 = l_Lean_MessageData_hasTag(x_50, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_55);
lean_dec_ref(x_7);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_10 = x_51;
x_11 = x_72;
x_12 = x_68;
x_13 = x_71;
x_14 = x_69;
x_15 = x_55;
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Syntax_getTailPos_x3f(x_81, x_78);
lean_dec(x_81);
if (lean_obj_tag(x_85) == 0)
{
lean_inc(x_84);
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_84;
x_55 = x_82;
x_56 = x_83;
x_57 = x_84;
goto block_76;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_50 = x_77;
x_51 = x_78;
x_52 = x_79;
x_53 = x_80;
x_54 = x_84;
x_55 = x_82;
x_56 = x_83;
x_57 = x_86;
goto block_76;
}
}
block_99:
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_replaceRef(x_1, x_92);
lean_dec(x_92);
x_96 = l_Lean_Syntax_getPos_x3f(x_95, x_89);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_unsigned_to_nat(0u);
x_77 = x_88;
x_78 = x_89;
x_79 = x_90;
x_80 = x_91;
x_81 = x_95;
x_82 = x_93;
x_83 = x_94;
x_84 = x_97;
goto block_87;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_77 = x_88;
x_78 = x_89;
x_79 = x_90;
x_80 = x_91;
x_81 = x_95;
x_82 = x_93;
x_83 = x_94;
x_84 = x_98;
goto block_87;
}
}
block_108:
{
if (x_107 == 0)
{
x_88 = x_103;
x_89 = x_106;
x_90 = x_101;
x_91 = x_102;
x_92 = x_104;
x_93 = x_105;
x_94 = x_3;
goto block_99;
}
else
{
x_88 = x_103;
x_89 = x_106;
x_90 = x_101;
x_91 = x_102;
x_92 = x_104;
x_93 = x_105;
x_94 = x_100;
goto block_99;
}
}
block_124:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_115 = lean_box(x_109);
x_116 = lean_box(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = 1;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_118);
if (x_119 == 0)
{
lean_inc_ref(x_110);
lean_inc(x_113);
lean_inc_ref(x_111);
x_101 = x_111;
x_102 = x_114;
x_103 = x_117;
x_104 = x_113;
x_105 = x_110;
x_106 = x_109;
x_107 = x_119;
goto block_108;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_warningAsError;
x_121 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(x_112, x_120);
lean_inc_ref(x_110);
lean_inc(x_113);
lean_inc_ref(x_111);
x_101 = x_111;
x_102 = x_114;
x_103 = x_117;
x_104 = x_113;
x_105 = x_110;
x_106 = x_109;
x_107 = x_121;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 5);
lean_inc(x_13);
x_14 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(x_13, x_1, x_2, x_3, x_8, x_9, x_10, x_11);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = 0;
x_13 = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(x_1, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
if (x_1 == 0)
{
lean_object* x_42; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_42 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_2, x_43);
x_45 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
x_46 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_45);
lean_inc(x_44);
x_47 = l_Lean_Syntax_isOfKind(x_44, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_48 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Syntax_getArg(x_44, x_49);
lean_dec(x_44);
x_51 = l_Lean_Syntax_isNone(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_inc(x_50);
x_52 = l_Lean_Syntax_matchesNull(x_50, x_43);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_53 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Syntax_getArg(x_50, x_49);
lean_dec(x_50);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_16 = x_55;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_41;
}
}
else
{
lean_object* x_56; 
lean_dec(x_50);
x_56 = lean_box(0);
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_41;
}
}
}
block_41:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
x_26 = l_Lean_Elab_Tactic_Grind_elabFilter(x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = 0;
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_17);
x_29 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(x_27, x_28, x_17, x_18, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_31, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
x_33 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1;
x_34 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(x_33, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
x_17 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
x_12 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
x_13 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
x_14 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4));
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed), 15, 6);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_12);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_14);
x_19 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_4);
x_16 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_20; 
x_16 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_16);
x_20 = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(x_16, x_1, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_16);
x_9 = x_5;
x_10 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_23; 
lean_inc(x_16);
x_23 = l_Lean_Expr_isTrue(x_16);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc(x_16);
x_24 = l_Lean_Expr_isFalse(x_16);
if (x_24 == 0)
{
x_17 = lean_box(0);
goto block_19;
}
else
{
lean_dec(x_16);
x_9 = x_5;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_dec(x_16);
x_9 = x_5;
x_10 = lean_box(0);
goto block_14;
}
}
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec_ref(x_20);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_16);
x_9 = x_5;
x_10 = lean_box(0);
goto block_14;
}
else
{
x_17 = lean_box(0);
goto block_19;
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec_ref(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
block_19:
{
lean_object* x_18; 
x_18 = lean_array_push(x_5, x_16);
x_9 = x_18;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_5);
return x_30;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
if (x_2 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_7);
x_14 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_7);
x_14 = x_55;
goto block_53;
}
block_53:
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_3);
x_18 = 0;
x_19 = l_Lean_Meta_Grind_Goal_getEqc(x_17, x_16, x_18);
x_20 = lean_array_mk(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_20);
x_23 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0;
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_14);
x_26 = 0;
x_27 = lean_usize_of_nat(x_22);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(x_1, x_20, x_26, x_27, x_23, x_3, x_10);
lean_dec_ref(x_20);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_free_object(x_14);
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(x_1, x_20, x_29, x_30, x_23, x_3, x_10);
lean_dec_ref(x_20);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_st_ref_get(x_3);
x_34 = 0;
x_35 = l_Lean_Meta_Grind_Goal_getEqc(x_33, x_32, x_34);
x_36 = lean_array_mk(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_get_size(x_36);
x_39 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0;
x_40 = lean_nat_dec_lt(x_37, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_36);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_38, x_38);
if (x_42 == 0)
{
if (x_40 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_36);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_39);
return x_43;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_38);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(x_1, x_36, x_44, x_45, x_39, x_3, x_10);
lean_dec_ref(x_36);
return x_46;
}
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_38);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(x_1, x_36, x_47, x_48, x_39, x_3, x_10);
lean_dec_ref(x_36);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_14, 0);
lean_inc(x_51);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed), 13, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_16 = l_Array_isEmpty___redArg(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1));
if (x_2 == 0)
{
lean_object* x_26; 
x_26 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3));
x_18 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4));
x_18 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4));
x_22 = l_Lean_Meta_Grind_ppExprArray(x_17, x_20, x_14, x_21, x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (lean_is_scalar(x_15)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_15;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_28 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_15;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_Elab_Tactic_Grind_elabFilter(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_15 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(x_13, x_2, x_14, x_3, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_19 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0));
if (x_2 == 0)
{
lean_object* x_28; 
x_28 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1));
x_20 = x_28;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2));
x_20 = x_29;
goto block_27;
}
block_27:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2));
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(x_25, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_26;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1));
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2));
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
lean_dec(x_15);
x_21 = l_Lean_Syntax_isNone(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Syntax_getArg(x_20, x_19);
lean_dec(x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(x_25, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(x_27, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1));
lean_inc(x_1);
x_25 = l_Lean_Syntax_isOfKind(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
lean_dec(x_1);
x_29 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2));
lean_inc(x_28);
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_28, x_32);
lean_dec(x_28);
x_34 = l_Lean_Syntax_isNone(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_inc(x_33);
x_35 = l_Lean_Syntax_matchesNull(x_33, x_27);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_36 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Syntax_getArg(x_33, x_32);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_11 = x_38;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_39; 
lean_dec(x_33);
x_39 = lean_box(0);
x_11 = x_39;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = lean_box(0);
goto block_23;
}
}
}
block_23:
{
uint8_t x_21; lean_object* x_22; 
x_21 = 0;
x_22 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(x_11, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_10);
x_12 = l_Lean_Meta_Grind_isSupportApp(x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_1);
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_20);
x_22 = l_Lean_Meta_Grind_isSupportApp(x_20, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_20);
x_1 = x_21;
goto _start;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_21;
x_2 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(x_9, x_1, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec_ref(x_11);
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_13 = x_3;
} else {
 lean_dec_ref(x_3);
 x_13 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_11);
x_20 = l_Lean_Meta_Grind_isSupportApp(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
x_14 = x_1;
x_15 = lean_box(0);
goto block_19;
}
else
{
x_14 = x_2;
x_15 = lean_box(0);
goto block_19;
}
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_14 = x_24;
x_15 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
block_19:
{
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_17; 
if (lean_is_scalar(x_13)) {
 x_17 = lean_alloc_ctor(1, 2, 0);
} else {
 x_17 = x_13;
}
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_4);
x_3 = x_12;
x_4 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_2);
x_12 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_21 = x_3;
} else {
 lean_dec_ref(x_3);
 x_21 = lean_box(0);
}
x_26 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__0));
lean_inc(x_16);
x_27 = l_List_find_x3f___redArg(x_26, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__1));
lean_inc(x_16);
x_29 = l_List_find_x3f___redArg(x_28, x_16);
if (lean_obj_tag(x_29) == 0)
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_16, 0);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_31);
x_33 = l_Lean_Meta_isProof(x_31, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc_ref(x_16);
lean_inc(x_1);
x_36 = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg(x_1, x_16, x_4, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_18);
lean_dec_ref(x_16);
if (lean_is_scalar(x_32)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_32;
 lean_ctor_set_tag(x_39, 0);
}
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_20);
x_2 = x_17;
x_3 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_58; lean_object* x_59; lean_object* x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; 
x_41 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2;
x_76 = lean_box(0);
x_77 = lean_unbox(x_37);
lean_dec(x_37);
x_78 = lean_unbox(x_34);
lean_dec(x_34);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_16);
x_79 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg(x_77, x_78, x_16, x_76, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = l_List_reverse___redArg(x_80);
x_58 = x_81;
x_59 = lean_box(0);
goto block_75;
}
else
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec_ref(x_79);
x_58 = x_82;
x_59 = lean_box(0);
goto block_75;
}
else
{
uint8_t x_83; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
block_57:
{
uint8_t x_45; 
x_45 = l_List_isEmpty___redArg(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Meta_Grind_ppEqc(x_43, x_41);
x_47 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__3;
x_48 = lean_array_push(x_47, x_46);
x_49 = l_Lean_Meta_Grind_ppEqc(x_42, x_48);
x_50 = lean_array_push(x_20, x_49);
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_32;
 lean_ctor_set_tag(x_51, 0);
}
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_2 = x_17;
x_3 = x_51;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_43);
x_53 = l_Lean_Meta_Grind_ppEqc(x_42, x_41);
x_54 = lean_array_push(x_20, x_53);
if (lean_is_scalar(x_32)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_32;
 lean_ctor_set_tag(x_55, 0);
}
lean_ctor_set(x_55, 0, x_19);
lean_ctor_set(x_55, 1, x_54);
x_2 = x_17;
x_3 = x_55;
goto _start;
}
}
block_75:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_List_lengthTR___redArg(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_18);
x_63 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_64 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(x_16, x_63, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_List_reverse___redArg(x_65);
x_42 = x_58;
x_43 = x_66;
x_44 = lean_box(0);
goto block_57;
}
else
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec_ref(x_64);
x_42 = x_58;
x_43 = x_67;
x_44 = lean_box(0);
goto block_57;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_58);
lean_dec(x_32);
x_71 = l_Lean_Meta_Grind_ppEqc(x_16, x_41);
x_72 = lean_array_push(x_19, x_71);
if (lean_is_scalar(x_18)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_18;
 lean_ctor_set_tag(x_73, 0);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_20);
x_2 = x_17;
x_3 = x_73;
goto _start;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
return x_36;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_inc(x_87);
lean_dec(x_36);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_34);
lean_dec(x_18);
lean_dec_ref(x_16);
if (lean_is_scalar(x_32)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_32;
 lean_ctor_set_tag(x_89, 0);
}
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_20);
x_2 = x_17;
x_3 = x_89;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_33);
if (x_91 == 0)
{
return x_33;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_33, 0);
lean_inc(x_92);
lean_dec(x_33);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_18);
lean_dec_ref(x_16);
x_22 = lean_box(0);
goto block_25;
}
}
else
{
lean_dec(x_18);
lean_dec(x_16);
x_22 = lean_box(0);
goto block_25;
}
}
else
{
lean_object* x_94; 
lean_dec_ref(x_29);
lean_dec(x_21);
lean_dec(x_16);
if (lean_is_scalar(x_18)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_18;
 lean_ctor_set_tag(x_94, 0);
}
lean_ctor_set(x_94, 0, x_19);
lean_ctor_set(x_94, 1, x_20);
x_2 = x_17;
x_3 = x_94;
goto _start;
}
}
else
{
lean_object* x_96; 
lean_dec_ref(x_27);
lean_dec(x_21);
lean_dec(x_16);
if (lean_is_scalar(x_18)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_18;
 lean_ctor_set_tag(x_96, 0);
}
lean_ctor_set(x_96, 0, x_19);
lean_ctor_set(x_96, 1, x_20);
x_2 = x_17;
x_3 = x_96;
goto _start;
}
block_25:
{
lean_object* x_23; 
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
x_2 = x_17;
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_st_ref_get(x_5);
x_31 = 1;
x_32 = l_Lean_Meta_Grind_Goal_getEqcs(x_30, x_31);
lean_inc_ref(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_1);
x_34 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(x_2, x_32, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Array_isEmpty___redArg(x_36);
if (x_38 == 0)
{
lean_object* x_39; double x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1));
lean_inc(x_3);
x_40 = lean_float_of_nat(x_3);
x_41 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_40);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_31);
x_43 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7;
x_44 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_36);
x_45 = lean_array_push(x_37, x_44);
x_16 = x_45;
x_17 = lean_box(0);
goto block_29;
}
else
{
lean_dec(x_36);
x_16 = x_37;
x_17 = lean_box(0);
goto block_29;
}
}
else
{
uint8_t x_46; 
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_29:
{
uint8_t x_18; 
x_18 = l_Array_isEmpty___redArg(x_16);
if (x_18 == 0)
{
lean_object* x_19; double x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1));
x_20 = lean_float_of_nat(x_3);
x_21 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_22 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_22, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 16, x_4);
x_23 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4;
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_16);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2;
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed), 15, 4);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___redArg(x_1, x_2, x_3, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___redArg(x_1, x_2, x_3, x_4, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_2);
x_18 = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
if (x_1 == 0)
{
lean_object* x_42; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_42 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_2, x_43);
x_45 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
x_46 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_45);
lean_inc(x_44);
x_47 = l_Lean_Syntax_isOfKind(x_44, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_48 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Syntax_getArg(x_44, x_49);
lean_dec(x_44);
x_51 = l_Lean_Syntax_isNone(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_inc(x_50);
x_52 = l_Lean_Syntax_matchesNull(x_50, x_43);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_53 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Syntax_getArg(x_50, x_49);
lean_dec(x_50);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_16 = x_55;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_41;
}
}
else
{
lean_object* x_56; 
lean_dec(x_50);
x_56 = lean_box(0);
x_16 = x_56;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_41;
}
}
}
block_41:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
x_26 = l_Lean_Elab_Tactic_Grind_elabFilter(x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = 0;
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_17);
x_29 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(x_27, x_28, x_17, x_18, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_31, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
x_33 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1;
x_34 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(x_33, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
x_17 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
x_12 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
x_13 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
x_14 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1));
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed), 15, 6);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_12);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_14);
x_19 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_array_push(x_1, x_3);
return x_4;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static double _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; lean_object* x_4; lean_object* x_5; 
x_1 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_2 = 0;
x_3 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1));
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(x_1, x_10, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(x_1, x_13, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_18 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_7, 5);
lean_inc(x_20);
x_21 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2;
x_22 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(x_21, x_12);
x_23 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(x_22, x_15);
x_24 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(x_23, x_17);
x_25 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(x_24, x_19);
x_26 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3;
x_27 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
x_29 = 0;
x_30 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(x_20, x_28, x_29, x_2, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_20);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Elab_Tactic_Grind_showState___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Grind_showState___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Elab_Tactic_Grind_showState(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
if (x_1 == 0)
{
lean_object* x_34; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_2, x_35);
x_37 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
x_38 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_37);
lean_inc(x_36);
x_39 = l_Lean_Syntax_isOfKind(x_36, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_40 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_36, x_41);
lean_dec(x_36);
x_43 = l_Lean_Syntax_isNone(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_inc(x_42);
x_44 = l_Lean_Syntax_matchesNull(x_42, x_35);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_45 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Syntax_getArg(x_42, x_41);
lean_dec(x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_16 = x_47;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_33;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_box(0);
x_16 = x_48;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = lean_box(0);
goto block_33;
}
}
}
block_33:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_26 = l_Lean_Elab_Tactic_Grind_elabFilter(x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = 0;
x_29 = l_Lean_Elab_Tactic_Grind_showState___redArg(x_27, x_28, x_17, x_18, x_21, x_22, x_23, x_24);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_17);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
x_17 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
x_12 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
x_13 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
x_14 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1));
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed), 15, 6);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_12);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_14);
x_19 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; double x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1));
x_12 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
x_13 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_14 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_float(x_14, sizeof(void*)*2, x_12);
lean_ctor_set_float(x_14, sizeof(void*)*2 + 8, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 16, x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3;
x_16 = l_Lean_Meta_Grind_anchorToString(x_1, x_8);
x_17 = l_Lean_stringToMessageData(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofExpr(x_7);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2;
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_10, x_3, x_24);
x_3 = x_26;
x_4 = x_27;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; lean_object* x_4; lean_object* x_5; 
x_1 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_2 = 0;
x_3 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1));
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
x_20 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_71; uint8_t x_72; 
x_23 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_72 = l_Lean_Syntax_isNone(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_inc(x_71);
x_73 = l_Lean_Syntax_matchesNull(x_71, x_17);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
x_74 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_Syntax_getArg(x_71, x_23);
lean_dec(x_71);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_43 = x_76;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_11;
x_49 = x_12;
x_50 = x_13;
x_51 = x_14;
x_52 = lean_box(0);
goto block_70;
}
}
else
{
lean_object* x_77; 
lean_dec(x_71);
x_77 = lean_box(0);
x_43 = x_77;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_11;
x_49 = x_12;
x_50 = x_13;
x_51 = x_14;
x_52 = lean_box(0);
goto block_70;
}
block_42:
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_array_size(x_24);
x_36 = 0;
x_37 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(x_25, x_35, x_36, x_24);
lean_dec(x_25);
x_38 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2;
x_39 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5;
x_40 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_37);
x_41 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_40, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_26);
return x_41;
}
block_70:
{
lean_object* x_53; 
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
x_53 = l_Lean_Elab_Tactic_Grind_elabFilter(x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Filter_eval___boxed), 13, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed), 12, 1);
lean_closure_set(x_56, 0, x_55);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_44);
x_57 = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(x_56, x_44, x_45, x_48, x_49, x_50, x_51);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_isEmpty___redArg(x_59);
if (x_61 == 0)
{
x_24 = x_59;
x_25 = x_60;
x_26 = x_44;
x_27 = x_45;
x_28 = x_46;
x_29 = x_47;
x_30 = x_48;
x_31 = x_49;
x_32 = x_50;
x_33 = x_51;
x_34 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_44);
x_62 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7;
x_63 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(x_62, x_48, x_49, x_50, x_51);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_44);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_44);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
return x_53;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
lean_dec(x_53);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
x_17 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
x_12 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
x_13 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
x_14 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1));
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed), 15, 6);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_12);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_14);
x_19 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = 32;
x_6 = lean_uint64_shift_right(x_2, x_5);
x_7 = lean_uint64_xor(x_2, x_6);
x_8 = 16;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = lean_uint64_to_usize(x_10);
x_12 = lean_usize_of_nat(x_4);
x_13 = 1;
x_14 = lean_usize_sub(x_12, x_13);
x_15 = lean_usize_land(x_11, x_14);
x_16 = lean_array_uget(x_3, x_15);
x_17 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(x_1, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_shift_right(x_8, x_7);
x_10 = lean_unbox_uint64(x_4);
x_11 = lean_uint64_xor(x_10, x_9);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = 32;
x_28 = lean_unbox_uint64(x_23);
x_29 = lean_uint64_shift_right(x_28, x_27);
x_30 = lean_unbox_uint64(x_23);
x_31 = lean_uint64_xor(x_30, x_29);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_2, x_7);
x_9 = lean_uint64_xor(x_2, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_6);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_5, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_25 = lean_box_uint64(x_2);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_18);
x_27 = lean_array_uset(x_5, x_17, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_24, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_box_uint64(x_2);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_18);
x_39 = lean_array_uset(x_5, x_17, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_nat_mul(x_36, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
return x_7;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_array_uget(x_4, x_6);
x_13 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_14 = lean_uint64_of_nat(x_1);
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(x_10, x_15, x_18);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(x_3, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_array_uget(x_4, x_6);
x_29 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
lean_dec(x_28);
x_30 = lean_uint64_of_nat(x_1);
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(x_27, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(x_27, x_31, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = 1;
x_38 = lean_usize_add(x_6, x_37);
x_6 = x_38;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_2, x_40);
x_42 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(x_3, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_mul(x_3, x_2);
x_5 = lean_unsigned_to_nat(64u);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_nat_sub(x_5, x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2;
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(x_7, x_2, x_1, x_1, x_9, x_10, x_8);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; double x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint64(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_4, x_3, x_9);
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1));
x_12 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
x_13 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_14 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_float(x_14, sizeof(void*)*2, x_12);
lean_ctor_set_float(x_14, sizeof(void*)*2 + 8, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 16, x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3;
x_16 = l_Lean_Meta_Grind_anchorToString(x_1, x_8);
x_17 = l_Lean_stringToMessageData(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofExpr(x_7);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2;
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_10, x_3, x_24);
x_3 = x_26;
x_4 = x_27;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; lean_object* x_4; lean_object* x_5; 
x_1 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
x_2 = 0;
x_3 = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1));
x_5 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_float(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_float(x_5, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 16, x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getLocalTheoremAnchors___boxed), 11, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_13 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_12, x_1, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(x_14);
x_16 = lean_array_size(x_14);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(x_15, x_16, x_17, x_14);
lean_dec(x_15);
x_19 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2;
x_20 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5;
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
x_22 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0));
x_11 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(x_1, x_2, x_4);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(x_1, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_MessageData_ofExpr(x_12);
x_14 = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1));
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3));
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_21 = l_Lean_Elab_Tactic_Grind_evalGrindTactic(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_22);
x_23 = l_Lean_mkMVar(x_22);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed), 10, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(x_22, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
lean_dec(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_ShowState(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__2);
l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___closed__3);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2 = _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2();
l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3 = _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3);
l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6 = _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1);
l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2);
l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

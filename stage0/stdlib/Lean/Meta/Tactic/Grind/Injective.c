// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injective
// Imports: public import Lean.Meta.Tactic.Grind.EMatchTheorem import Init.Data.Function import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 139, 26, 158, 27, 86, 65, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 254, 56, 239, 242, 165, 158, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 85, 95, 91, 208, 249, 36, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(140, 234, 176, 190, 43, 218, 193, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 59, 181, 124, 129, 144, 131, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 196, 197, 85, 206, 208, 224, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 125, 13, 22, 112, 21, 0, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 23, 83, 242, 225, 126, 92, 93)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 94, 3, 232, 212, 22, 220, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 48, 151, 243, 33, 207, 121, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 17, 242, 221, 11, 253, 57, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 2, 125, 28, 44, 87, 14, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 92, 81, 164, 110, 126, 15, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 139, 26, 158, 27, 86, 65, 26)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 213, 49, 65, 20, 205, 188, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1215188614) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(4, 62, 8, 192, 204, 12, 15, 52)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 214, 79, 233, 161, 131, 40, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 131, 10, 246, 143, 229, 240, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(62, 136, 129, 53, 34, 164, 82, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 101, 131, 165, 128, 151, 24, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "invalid `[grind inj]` theorem, injective function must use at least one constant function symbol"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "invalid `[grind inj]` theorem, theorem has universe levels, but no hypotheses"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 162, 25, 76, 92, 227, 14, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "invalid `[grind inj]` theorem, resulting type is not of the form `Function.Injective <fun>`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3;
static const lean_string_object l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(3173337487u);
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_67_ = l_Lean_Name_num___override(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_70_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
v___x_71_ = l_Lean_Name_str___override(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
v___x_75_ = l_Lean_Name_str___override(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
v___x_78_ = l_Lean_Name_num___override(v___x_77_, v___x_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_81_ = 0;
v___x_82_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
v___x_83_ = l_Lean_registerTraceClass(v___x_80_, v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2____boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_));
v___x_105_ = 0;
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_));
v___x_107_ = l_Lean_registerTraceClass(v___x_104_, v___x_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2____boxed(lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
return v_res_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(3941467707u);
v___x_116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_117_ = l_Lean_Name_num___override(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
v___x_120_ = l_Lean_Name_str___override(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
v___x_123_ = l_Lean_Name_str___override(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
v___x_126_ = l_Lean_Name_num___override(v___x_125_, v___x_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_));
v___x_129_ = 0;
v___x_130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
v___x_131_ = l_Lean_registerTraceClass(v___x_128_, v___x_129_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2____boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
return v_res_133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0(void){
_start:
{
lean_object* v___x_134_; lean_object* v_dummy_135_; 
v___x_134_ = lean_box(0);
v_dummy_135_ = l_Lean_Expr_sort___override(v___x_134_);
return v_dummy_135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(lean_object* v_upperBound_136_, lean_object* v_args_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_b_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_a_148_; uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_lt(v_a_139_, v_upperBound_136_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_dec(v_a_139_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v_b_140_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_array_fget_borrowed(v_args_137_, v_a_139_);
v___x_158_ = lean_array_get_size(v_a_138_);
v___x_159_ = lean_nat_dec_lt(v_a_139_, v___x_158_);
if (v___x_159_ == 0)
{
goto v___jp_156_;
}
else
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_array_fget_borrowed(v_a_138_, v_a_139_);
v___x_161_ = lean_unbox(v___x_160_);
switch(v___x_161_)
{
case 0:
{
goto v___jp_156_;
}
case 3:
{
goto v___jp_156_;
}
default: 
{
v_a_148_ = v___x_154_;
goto v___jp_147_;
}
}
}
v___jp_156_:
{
lean_object* v___x_157_; 
lean_inc(v___x_155_);
v___x_157_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(v___x_155_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_dec_ref_known(v___x_157_, 1);
v_a_148_ = v___x_154_;
goto v___jp_147_;
}
else
{
lean_dec(v_a_139_);
return v___x_157_;
}
}
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_add(v_a_139_, v___x_149_);
lean_dec(v_a_139_);
v_a_139_ = v___x_150_;
v_b_140_ = v_a_148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; 
if (lean_obj_tag(v_x_162_) == 5)
{
lean_object* v_fn_199_; lean_object* v_arg_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_fn_199_ = lean_ctor_get(v_x_162_, 0);
lean_inc_ref(v_fn_199_);
v_arg_200_ = lean_ctor_get(v_x_162_, 1);
lean_inc_ref(v_arg_200_);
lean_dec_ref_known(v_x_162_, 2);
v___x_201_ = lean_array_set(v_x_163_, v_x_164_, v_arg_200_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_sub(v_x_164_, v___x_202_);
lean_dec(v_x_164_);
v_x_162_ = v_fn_199_;
v_x_163_ = v___x_201_;
v_x_164_ = v___x_203_;
goto _start;
}
else
{
lean_dec(v_x_164_);
if (lean_obj_tag(v_x_162_) == 4)
{
lean_object* v_declName_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_declName_205_ = lean_ctor_get(v_x_162_, 0);
v___x_206_ = lean_st_ref_take(v___y_165_);
lean_inc(v_declName_205_);
v___x_207_ = l_Lean_NameSet_insert(v___x_206_, v_declName_205_);
v___x_208_ = lean_st_ref_put(v___y_165_, v___x_207_);
v___y_172_ = v___y_165_;
v___y_173_ = v___y_166_;
v___y_174_ = v___y_167_;
v___y_175_ = v___y_168_;
v___y_176_ = v___y_169_;
goto v___jp_171_;
}
else
{
v___y_172_ = v___y_165_;
v___y_173_ = v___y_166_;
v___y_174_ = v___y_167_;
v___y_175_ = v___y_168_;
v___y_176_ = v___y_169_;
goto v___jp_171_;
}
}
v___jp_171_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_array_get_size(v_x_163_);
v___x_178_ = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(v_x_162_, v___x_177_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_box(0);
v___x_182_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v___x_177_, v_x_163_, v_a_179_, v___x_180_, v___x_181_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v_a_179_);
lean_dec_ref(v_x_163_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v___x_182_, 0);
lean_dec(v_unused_190_);
v___x_184_ = v___x_182_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_dec(v___x_182_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_181_);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_181_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
return v___x_182_;
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v_x_163_);
v_a_191_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_178_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_178_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(lean_object* v_e_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Expr_isApp(v_e_209_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_e_209_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
else
{
lean_object* v_dummy_219_; lean_object* v_nargs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_dummy_219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0);
v_nargs_220_ = l_Lean_Expr_getAppNumArgs(v_e_209_);
lean_inc(v_nargs_220_);
v___x_221_ = lean_mk_array(v_nargs_220_, v_dummy_219_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v_nargs_220_, v___x_222_);
lean_dec(v_nargs_220_);
v___x_224_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(v_e_209_, v___x_221_, v___x_223_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___boxed(lean_object* v_e_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(v_e_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg___boxed(lean_object* v_upperBound_233_, lean_object* v_args_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_b_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v_upperBound_233_, v_args_234_, v_a_235_, v_a_236_, v_b_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_args_234_);
lean_dec(v_upperBound_233_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1___boxed(lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(v_x_245_, v_x_246_, v_x_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(lean_object* v_upperBound_255_, lean_object* v_args_256_, lean_object* v_a_257_, lean_object* v_inst_258_, lean_object* v_R_259_, lean_object* v_a_260_, lean_object* v_b_261_, lean_object* v_c_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v_upperBound_255_, v_args_256_, v_a_257_, v_a_260_, v_b_261_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___boxed(lean_object* v_upperBound_270_, lean_object* v_args_271_, lean_object* v_a_272_, lean_object* v_inst_273_, lean_object* v_R_274_, lean_object* v_a_275_, lean_object* v_b_276_, lean_object* v_c_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(v_upperBound_270_, v_args_271_, v_a_272_, v_inst_273_, v_R_274_, v_a_275_, v_b_276_, v_c_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v_a_272_);
lean_dec_ref(v_args_271_);
lean_dec(v_upperBound_270_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(lean_object* v_f_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
if (lean_obj_tag(v_f_285_) == 4)
{
lean_object* v_declName_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_declName_291_ = lean_ctor_get(v_f_285_, 0);
lean_inc(v_declName_291_);
lean_dec_ref_known(v_f_285_, 2);
v___x_292_ = l_Lean_NameSet_empty;
v___x_293_ = l_Lean_NameSet_insert(v___x_292_, v_declName_291_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_NameSet_empty;
v___x_296_ = lean_st_mk_ref(v___x_295_);
v___x_297_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(v_f_285_, v___x_296_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_297_, 0);
lean_dec(v_unused_306_);
v___x_299_ = v___x_297_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_dec(v___x_297_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_st_ref_get(v___x_296_);
lean_dec(v___x_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v___x_296_);
v_a_307_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_297_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_297_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames___boxed(lean_object* v_f_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(v_f_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(lean_object* v_k_322_, lean_object* v_b_323_, lean_object* v_c_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
v___x_330_ = lean_apply_7(v_k_322_, v_b_323_, v_c_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, lean_box(0));
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed(lean_object* v_k_331_, lean_object* v_b_332_, lean_object* v_c_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(v_k_331_, v_b_332_, v_c_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(lean_object* v_type_340_, lean_object* v_k_341_, uint8_t v_cleanupAnnotations_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___f_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_348_, 0, v_k_341_);
v___x_349_ = 0;
v___x_350_ = lean_box(0);
v___x_351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_349_, v___x_350_, v_type_340_, v___f_348_, v_cleanupAnnotations_342_, v___x_349_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_351_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_351_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___boxed(lean_object* v_type_368_, lean_object* v_k_369_, lean_object* v_cleanupAnnotations_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_376_; lean_object* v_res_377_; 
v_cleanupAnnotations_boxed_376_ = lean_unbox(v_cleanupAnnotations_370_);
v_res_377_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_type_368_, v_k_369_, v_cleanupAnnotations_boxed_376_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(lean_object* v_00_u03b1_378_, lean_object* v_type_379_, lean_object* v_k_380_, uint8_t v_cleanupAnnotations_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_type_379_, v_k_380_, v_cleanupAnnotations_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___boxed(lean_object* v_00_u03b1_388_, lean_object* v_type_389_, lean_object* v_k_390_, lean_object* v_cleanupAnnotations_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_397_; lean_object* v_res_398_; 
v_cleanupAnnotations_boxed_397_ = lean_unbox(v_cleanupAnnotations_391_);
v_res_398_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(v_00_u03b1_388_, v_type_389_, v_k_390_, v_cleanupAnnotations_boxed_397_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(lean_object* v_msgData_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_env_406_; lean_object* v___x_407_; lean_object* v_mctx_408_; lean_object* v_lctx_409_; lean_object* v_options_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_405_ = lean_st_ref_get(v___y_403_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_env_406_);
lean_dec(v___x_405_);
v___x_407_ = lean_st_ref_get(v___y_401_);
v_mctx_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_mctx_408_);
lean_dec(v___x_407_);
v_lctx_409_ = lean_ctor_get(v___y_400_, 2);
v_options_410_ = lean_ctor_get(v___y_402_, 1);
lean_inc_ref(v_options_410_);
lean_inc_ref(v_lctx_409_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_406_);
lean_ctor_set(v___x_411_, 1, v_mctx_408_);
lean_ctor_set(v___x_411_, 2, v_lctx_409_);
lean_ctor_set(v___x_411_, 3, v_options_410_);
v___x_412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_msgData_399_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2___boxed(lean_object* v_msgData_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msgData_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_ref_427_; lean_object* v___x_428_; lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v_ref_427_ = lean_ctor_get(v___y_424_, 4);
v___x_428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_437_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_ref_427_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_ref_427_);
lean_ctor_set(v___x_433_, 1, v_a_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 1);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg___boxed(lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(lean_object* v_init_445_, lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v_k_447_; lean_object* v_l_448_; lean_object* v_r_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_k_447_ = lean_ctor_get(v_x_446_, 1);
v_l_448_ = lean_ctor_get(v_x_446_, 3);
v_r_449_ = lean_ctor_get(v_x_446_, 4);
v___x_450_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v_init_445_, v_r_449_);
lean_inc(v_k_447_);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_k_447_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v_init_445_ = v___x_451_;
v_x_446_ = v_l_448_;
goto _start;
}
else
{
return v_init_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0___boxed(lean_object* v_init_453_, lean_object* v_x_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v_init_453_, v_x_454_);
lean_dec(v_x_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
if (lean_obj_tag(v_a_456_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = l_List_reverse___redArg(v_a_457_);
return v___x_458_;
}
else
{
lean_object* v_head_459_; lean_object* v_tail_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_head_459_ = lean_ctor_get(v_a_456_, 0);
v_tail_460_ = lean_ctor_get(v_a_456_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v_a_456_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_tail_460_);
lean_inc(v_head_459_);
lean_dec(v_a_456_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_464_, 0, v_head_459_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v_a_457_);
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_a_457_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v_a_456_ = v_tail_460_;
v_a_457_ = v___x_466_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0));
v___x_472_ = l_Lean_stringToMessageData(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0(uint8_t v_hasUniverses_483_, lean_object* v_xs_484_, lean_object* v_type_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___y_492_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5));
v___x_543_ = lean_unsigned_to_nat(3u);
v___x_544_ = l_Lean_Expr_isAppOfArity(v_type_485_, v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7);
v___x_546_ = l_Lean_indentExpr(v_type_485_);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_547_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
goto v___jp_526_;
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_box(0);
v___x_494_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v___x_493_, v___y_492_);
lean_dec(v___y_492_);
v___x_495_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(v___x_494_, v___x_493_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
v___jp_497_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_Expr_appArg_x21(v_type_485_);
lean_dec_ref(v_type_485_);
v___x_503_ = l_Lean_Expr_eta(v___x_502_);
lean_inc_ref(v___x_503_);
v___x_504_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(v___x_503_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
if (lean_obj_tag(v_a_505_) == 0)
{
lean_dec_ref(v___x_503_);
v___y_492_ = v_a_505_;
goto v___jp_491_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v___x_506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1);
v___x_507_ = l_Lean_indentExpr(v___x_503_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_508_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v___x_503_);
v_a_518_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_504_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_504_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_array_get_size(v_xs_484_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_nat_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
v___y_498_ = v___y_486_;
v___y_499_ = v___y_487_;
v___y_500_ = v___y_488_;
v___y_501_ = v___y_489_;
goto v___jp_497_;
}
else
{
if (v_hasUniverses_483_ == 0)
{
v___y_498_ = v___y_486_;
v___y_499_ = v___y_487_;
v___y_500_ = v___y_488_;
v___y_501_ = v___y_489_;
goto v___jp_497_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3);
v___x_531_ = l_Lean_indentExpr(v_type_485_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_532_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___boxed(lean_object* v_hasUniverses_557_, lean_object* v_xs_558_, lean_object* v_type_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_hasUniverses_boxed_565_; lean_object* v_res_566_; 
v_hasUniverses_boxed_565_ = lean_unbox(v_hasUniverses_557_);
v_res_566_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0(v_hasUniverses_boxed_565_, v_xs_558_, v_type_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec_ref(v_xs_558_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(lean_object* v_proof_567_, uint8_t v_hasUniverses_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; 
lean_inc(v_a_572_);
lean_inc_ref(v_a_571_);
lean_inc(v_a_570_);
lean_inc_ref(v_a_569_);
v___x_574_ = lean_infer_type(v_proof_567_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___f_577_; uint8_t v___x_578_; lean_object* v___x_579_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_box(v_hasUniverses_568_);
v___f_577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___boxed), 8, 1);
lean_closure_set(v___f_577_, 0, v___x_576_);
v___x_578_ = 0;
v___x_579_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_a_575_, v___f_577_, v___x_578_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_579_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_a_580_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_574_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_574_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___boxed(lean_object* v_proof_588_, lean_object* v_hasUniverses_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
uint8_t v_hasUniverses_boxed_595_; lean_object* v_res_596_; 
v_hasUniverses_boxed_595_ = lean_unbox(v_hasUniverses_589_);
v_res_596_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(v_proof_588_, v_hasUniverses_boxed_595_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(lean_object* v_00_u03b1_597_, lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___boxed(lean_object* v_00_u03b1_605_, lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(v_00_u03b1_605_, v_msg_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
if (lean_obj_tag(v_a_613_) == 0)
{
lean_object* v___x_615_; 
v___x_615_ = l_List_reverse___redArg(v_a_614_);
return v___x_615_;
}
else
{
lean_object* v_head_616_; lean_object* v_tail_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_629_; 
v_head_616_ = lean_ctor_get(v_a_613_, 0);
v_tail_617_ = lean_ctor_get(v_a_613_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_613_);
if (v_isSharedCheck_629_ == 0)
{
v___x_619_ = v_a_613_;
v_isShared_620_ = v_isSharedCheck_629_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_tail_617_);
lean_inc(v_head_616_);
lean_dec(v_a_613_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_629_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___y_622_; 
if (lean_obj_tag(v_head_616_) == 2)
{
lean_object* v_constName_627_; 
v_constName_627_ = lean_ctor_get(v_head_616_, 0);
lean_inc(v_constName_627_);
lean_dec_ref_known(v_head_616_, 1);
v___y_622_ = v_constName_627_;
goto v___jp_621_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v_head_616_);
v___x_628_ = lean_box(0);
v___y_622_ = v___x_628_;
goto v___jp_621_;
}
v___jp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_a_614_);
lean_ctor_set(v___x_619_, 0, v___y_622_);
v___x_624_ = v___x_619_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___y_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_a_614_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v_a_613_ = v_tail_617_;
v_a_614_ = v___x_624_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames(lean_object* v_s_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
v___x_632_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(v_s_630_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
if (lean_obj_tag(v_a_633_) == 0)
{
lean_object* v___x_635_; 
v___x_635_ = l_List_reverse___redArg(v_a_634_);
return v___x_635_;
}
else
{
lean_object* v_head_636_; lean_object* v_tail_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v_head_636_ = lean_ctor_get(v_a_633_, 0);
v_tail_637_ = lean_ctor_get(v_a_633_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_a_633_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v_a_633_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_tail_637_);
lean_inc(v_head_636_);
lean_dec(v_a_633_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_MessageData_ofName(v_head_636_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_a_634_);
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_a_634_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v_a_633_ = v_tail_637_;
v_a_634_ = v___x_643_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_647_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_ctor_set(v___x_652_, 2, v___x_651_);
lean_ctor_set(v___x_652_, 3, v___x_651_);
lean_ctor_set(v___x_652_, 4, v___x_650_);
lean_ctor_set(v___x_652_, 5, v___x_650_);
lean_ctor_set(v___x_652_, 6, v___x_650_);
lean_ctor_set(v___x_652_, 7, v___x_650_);
lean_ctor_set(v___x_652_, 8, v___x_650_);
lean_ctor_set(v___x_652_, 9, v___x_650_);
lean_ctor_set(v___x_652_, 10, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(32u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_unsigned_to_nat(32u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_661_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_657_);
lean_ctor_set(v___x_661_, 3, v___x_657_);
lean_ctor_set_usize(v___x_661_, 4, v___x_656_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_box(1);
v___x_663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_687_, lean_object* v_declHint_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v_env_692_; uint8_t v___x_693_; 
v___x_691_ = lean_st_ref_get(v___y_689_);
v_env_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_env_692_);
lean_dec(v___x_691_);
v___x_693_ = l_Lean_Name_isAnonymous(v_declHint_688_);
if (v___x_693_ == 0)
{
uint8_t v_isExporting_694_; 
v_isExporting_694_ = lean_ctor_get_uint8(v_env_692_, sizeof(void*)*8);
if (v_isExporting_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v_env_692_);
lean_dec(v_declHint_688_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_msg_687_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
lean_inc_ref(v_env_692_);
v___x_696_ = l_Lean_Environment_setExporting(v_env_692_, v___x_693_);
lean_inc(v_declHint_688_);
lean_inc_ref(v___x_696_);
v___x_697_ = l_Lean_Environment_contains(v___x_696_, v_declHint_688_, v_isExporting_694_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec_ref(v___x_696_);
lean_dec_ref(v_env_692_);
lean_dec(v_declHint_688_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v_msg_687_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_c_704_; lean_object* v___x_705_; 
v___x_699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_701_ = l_Lean_Options_empty;
v___x_702_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_702_, 0, v___x_696_);
lean_ctor_set(v___x_702_, 1, v___x_699_);
lean_ctor_set(v___x_702_, 2, v___x_700_);
lean_ctor_set(v___x_702_, 3, v___x_701_);
lean_inc(v_declHint_688_);
v___x_703_ = l_Lean_MessageData_ofConstName(v_declHint_688_, v___x_693_);
v_c_704_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_704_, 0, v___x_702_);
lean_ctor_set(v_c_704_, 1, v___x_703_);
v___x_705_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_692_, v_declHint_688_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec_ref(v_env_692_);
lean_dec(v_declHint_688_);
v___x_706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_c_704_);
v___x_708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_MessageData_note(v___x_709_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v_msg_687_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_748_; 
v_val_713_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_748_ == 0)
{
v___x_715_ = v___x_705_;
v_isShared_716_ = v_isSharedCheck_748_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_val_713_);
lean_dec(v___x_705_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_748_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_mod_720_; uint8_t v___x_721_; 
v___x_717_ = lean_box(0);
v___x_718_ = l_Lean_Environment_header(v_env_692_);
lean_dec_ref(v_env_692_);
v___x_719_ = l_Lean_EnvironmentHeader_moduleNames(v___x_718_);
v_mod_720_ = lean_array_get(v___x_717_, v___x_719_, v_val_713_);
lean_dec(v_val_713_);
lean_dec_ref(v___x_719_);
v___x_721_ = l_Lean_isPrivateName(v_declHint_688_);
lean_dec(v_declHint_688_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_c_704_);
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_MessageData_ofName(v_mod_720_);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_MessageData_note(v___x_729_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v_msg_687_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 0, v___x_731_);
v___x_733_ = v___x_715_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_c_704_);
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_MessageData_ofName(v_mod_720_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_note(v___x_742_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v_msg_687_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 0, v___x_744_);
v___x_746_ = v___x_715_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_749_; 
lean_dec_ref(v_env_692_);
lean_dec(v_declHint_688_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_msg_687_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_750_, lean_object* v_declHint_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_750_, v_declHint_751_, v___y_752_);
lean_dec(v___y_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_755_, lean_object* v_declHint_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_772_; 
v___x_762_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_755_, v_declHint_756_, v___y_760_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_772_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = l_Lean_unknownIdentifierMessageTag;
v___x_768_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_773_, lean_object* v_declHint_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_773_, v_declHint_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_781_, lean_object* v_msg_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_toCold_788_; lean_object* v_options_789_; lean_object* v_currRecDepth_790_; lean_object* v_maxRecDepth_791_; lean_object* v_ref_792_; lean_object* v_currNamespace_793_; lean_object* v_openDecls_794_; lean_object* v_initHeartbeats_795_; lean_object* v_maxHeartbeats_796_; lean_object* v_currMacroScope_797_; uint8_t v_diag_798_; uint8_t v_suppressElabErrors_799_; lean_object* v_ref_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_toCold_788_ = lean_ctor_get(v___y_785_, 0);
v_options_789_ = lean_ctor_get(v___y_785_, 1);
v_currRecDepth_790_ = lean_ctor_get(v___y_785_, 2);
v_maxRecDepth_791_ = lean_ctor_get(v___y_785_, 3);
v_ref_792_ = lean_ctor_get(v___y_785_, 4);
v_currNamespace_793_ = lean_ctor_get(v___y_785_, 5);
v_openDecls_794_ = lean_ctor_get(v___y_785_, 6);
v_initHeartbeats_795_ = lean_ctor_get(v___y_785_, 7);
v_maxHeartbeats_796_ = lean_ctor_get(v___y_785_, 8);
v_currMacroScope_797_ = lean_ctor_get(v___y_785_, 9);
v_diag_798_ = lean_ctor_get_uint8(v___y_785_, sizeof(void*)*10);
v_suppressElabErrors_799_ = lean_ctor_get_uint8(v___y_785_, sizeof(void*)*10 + 1);
v_ref_800_ = l_Lean_replaceRef(v_ref_781_, v_ref_792_);
lean_inc(v_currMacroScope_797_);
lean_inc(v_maxHeartbeats_796_);
lean_inc(v_initHeartbeats_795_);
lean_inc(v_openDecls_794_);
lean_inc(v_currNamespace_793_);
lean_inc(v_maxRecDepth_791_);
lean_inc(v_currRecDepth_790_);
lean_inc_ref(v_options_789_);
lean_inc_ref(v_toCold_788_);
v___x_801_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_801_, 0, v_toCold_788_);
lean_ctor_set(v___x_801_, 1, v_options_789_);
lean_ctor_set(v___x_801_, 2, v_currRecDepth_790_);
lean_ctor_set(v___x_801_, 3, v_maxRecDepth_791_);
lean_ctor_set(v___x_801_, 4, v_ref_800_);
lean_ctor_set(v___x_801_, 5, v_currNamespace_793_);
lean_ctor_set(v___x_801_, 6, v_openDecls_794_);
lean_ctor_set(v___x_801_, 7, v_initHeartbeats_795_);
lean_ctor_set(v___x_801_, 8, v_maxHeartbeats_796_);
lean_ctor_set(v___x_801_, 9, v_currMacroScope_797_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*10, v_diag_798_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*10 + 1, v_suppressElabErrors_799_);
v___x_802_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_782_, v___y_783_, v___y_784_, v___x_801_, v___y_786_);
lean_dec_ref_known(v___x_801_, 10);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_803_, v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_ref_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_811_, lean_object* v_msg_812_, lean_object* v_declHint_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_a_820_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_812_, v_declHint_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
v___x_821_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_811_, v_a_820_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_822_, lean_object* v_msg_823_, lean_object* v_declHint_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_822_, v_msg_823_, v_declHint_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_ref_822_);
return v_res_830_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_837_, lean_object* v_constName_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_844_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_845_ = 0;
lean_inc(v_constName_838_);
v___x_846_ = l_Lean_MessageData_ofConstName(v_constName_838_, v___x_845_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_844_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_837_, v___x_849_, v_constName_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_851_, lean_object* v_constName_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_851_, v_constName_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v_ref_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(lean_object* v_constName_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_ref_865_; lean_object* v___x_866_; 
v_ref_865_ = lean_ctor_get(v___y_862_, 4);
v___x_866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_865_, v_constName_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(lean_object* v_constName_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v_env_881_; uint8_t v___x_882_; lean_object* v___x_883_; 
v___x_880_ = lean_st_ref_get(v___y_878_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_881_);
lean_dec(v___x_880_);
v___x_882_ = 0;
lean_inc(v_constName_874_);
v___x_883_ = l_Lean_Environment_find_x3f(v_env_881_, v_constName_874_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_884_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_constName_874_);
v_val_885_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_883_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v___x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 0);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_val_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0___boxed(lean_object* v_constName_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(v_constName_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0(void){
_start:
{
lean_object* v___x_900_; double v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_float_of_nat(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(lean_object* v_cls_905_, lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_958_; 
v_ref_912_ = lean_ctor_get(v___y_909_, 4);
v___x_913_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msg_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_958_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_958_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_958_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v_traceState_919_; lean_object* v_env_920_; lean_object* v_nextMacroScope_921_; lean_object* v_ngen_922_; lean_object* v_auxDeclNGen_923_; lean_object* v_cache_924_; lean_object* v_messages_925_; lean_object* v_infoState_926_; lean_object* v_snapshotTasks_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_957_; 
v___x_918_ = lean_st_ref_take(v___y_910_);
v_traceState_919_ = lean_ctor_get(v___x_918_, 4);
v_env_920_ = lean_ctor_get(v___x_918_, 0);
v_nextMacroScope_921_ = lean_ctor_get(v___x_918_, 1);
v_ngen_922_ = lean_ctor_get(v___x_918_, 2);
v_auxDeclNGen_923_ = lean_ctor_get(v___x_918_, 3);
v_cache_924_ = lean_ctor_get(v___x_918_, 5);
v_messages_925_ = lean_ctor_get(v___x_918_, 6);
v_infoState_926_ = lean_ctor_get(v___x_918_, 7);
v_snapshotTasks_927_ = lean_ctor_get(v___x_918_, 8);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_957_ == 0)
{
v___x_929_ = v___x_918_;
v_isShared_930_ = v_isSharedCheck_957_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snapshotTasks_927_);
lean_inc(v_infoState_926_);
lean_inc(v_messages_925_);
lean_inc(v_cache_924_);
lean_inc(v_traceState_919_);
lean_inc(v_auxDeclNGen_923_);
lean_inc(v_ngen_922_);
lean_inc(v_nextMacroScope_921_);
lean_inc(v_env_920_);
lean_dec(v___x_918_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_957_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint64_t v_tid_931_; lean_object* v_traces_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_956_; 
v_tid_931_ = lean_ctor_get_uint64(v_traceState_919_, sizeof(void*)*1);
v_traces_932_ = lean_ctor_get(v_traceState_919_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_traceState_919_);
if (v_isSharedCheck_956_ == 0)
{
v___x_934_ = v_traceState_919_;
v_isShared_935_ = v_isSharedCheck_956_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_traces_932_);
lean_dec(v_traceState_919_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_956_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; double v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_936_ = lean_box(0);
v___x_937_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0);
v___x_938_ = 0;
v___x_939_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1));
v___x_940_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_940_, 0, v_cls_905_);
lean_ctor_set(v___x_940_, 1, v___x_936_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
lean_ctor_set_float(v___x_940_, sizeof(void*)*3, v___x_937_);
lean_ctor_set_float(v___x_940_, sizeof(void*)*3 + 8, v___x_937_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 16, v___x_938_);
v___x_941_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2));
v___x_942_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v_a_914_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
lean_inc(v_ref_912_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_ref_912_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_PersistentArray_push___redArg(v_traces_932_, v___x_943_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_944_);
v___x_946_ = v___x_934_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_944_);
lean_ctor_set_uint64(v_reuseFailAlloc_955_, sizeof(void*)*1, v_tid_931_);
v___x_946_ = v_reuseFailAlloc_955_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 4, v___x_946_);
v___x_948_ = v___x_929_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_env_920_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_nextMacroScope_921_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_ngen_922_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_auxDeclNGen_923_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 5, v_cache_924_);
lean_ctor_set(v_reuseFailAlloc_954_, 6, v_messages_925_);
lean_ctor_set(v_reuseFailAlloc_954_, 7, v_infoState_926_);
lean_ctor_set(v_reuseFailAlloc_954_, 8, v_snapshotTasks_927_);
v___x_948_ = v_reuseFailAlloc_954_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = lean_st_ref_put(v___y_910_, v___x_948_);
v___x_950_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_950_);
v___x_952_ = v___x_916_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___boxed(lean_object* v_cls_959_, lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(v_cls_959_, v_msg_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_966_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_973_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2));
v___x_974_ = l_Lean_Name_append(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object* v_declName_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; 
lean_inc(v_declName_978_);
v___x_984_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(v_declName_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
lean_inc(v_declName_978_);
v___x_986_ = l_Lean_Meta_Grind_getProofForDecl(v_declName_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1040_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1040_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1040_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___y_992_; uint8_t v___y_1000_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = l_Lean_ConstantInfo_levelParams(v_a_985_);
lean_dec(v_a_985_);
v___x_1037_ = l_List_isEmpty___redArg(v___x_1036_);
lean_dec(v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; 
v___x_1038_ = 1;
v___y_1000_ = v___x_1038_;
goto v___jp_999_;
}
else
{
uint8_t v___x_1039_; 
v___x_1039_ = 0;
v___y_1000_ = v___x_1039_;
goto v___jp_999_;
}
v___jp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0));
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_declName_978_);
v___x_995_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v_a_987_);
lean_ctor_set(v___x_995_, 2, v___y_992_);
lean_ctor_set(v___x_995_, 3, v___x_994_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_995_);
v___x_997_ = v___x_989_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
v___jp_999_:
{
lean_object* v___x_1001_; 
lean_inc(v_a_987_);
v___x_1001_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(v_a_987_, v___y_1000_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_options_1002_; uint8_t v_hasTrace_1003_; 
v_options_1002_ = lean_ctor_get(v_a_981_, 1);
v_hasTrace_1003_ = lean_ctor_get_uint8(v_options_1002_, sizeof(void*)*1);
if (v_hasTrace_1003_ == 0)
{
lean_object* v_a_1004_; 
v_a_1004_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1001_, 1);
v___y_992_ = v_a_1004_;
goto v___jp_991_;
}
else
{
lean_object* v_toCold_1005_; lean_object* v_a_1006_; lean_object* v_inheritedTraceOptions_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_toCold_1005_ = lean_ctor_get(v_a_981_, 0);
v_a_1006_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1001_, 1);
v_inheritedTraceOptions_1007_ = lean_ctor_get(v_toCold_1005_, 4);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_));
v___x_1009_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3, &l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3_once, _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3);
v___x_1010_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1007_, v_options_1002_, v___x_1009_);
if (v___x_1010_ == 0)
{
v___y_992_ = v_a_1006_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_inc(v_declName_978_);
v___x_1011_ = l_Lean_MessageData_ofName(v_declName_978_);
v___x_1012_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5, &l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5_once, _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_inc(v_a_1006_);
v___x_1014_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames(v_a_1006_);
v___x_1015_ = lean_box(0);
v___x_1016_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(v___x_1014_, v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofList(v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1013_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(v___x_1008_, v___x_1018_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_dec_ref_known(v___x_1019_, 1);
v___y_992_ = v_a_1006_;
goto v___jp_991_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_a_1006_);
lean_del_object(v___x_989_);
lean_dec(v_a_987_);
lean_dec(v_declName_978_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_del_object(v___x_989_);
lean_dec(v_a_987_);
lean_dec(v_declName_978_);
v_a_1028_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1001_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1001_);
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
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_985_);
lean_dec(v_declName_978_);
v_a_1041_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_986_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_986_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_declName_978_);
v_a_1049_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_984_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_984_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem___boxed(lean_object* v_declName_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_declName_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1064_, lean_object* v_constName_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1072_, lean_object* v_constName_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(v_00_u03b1_1072_, v_constName_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1080_, lean_object* v_ref_1081_, lean_object* v_constName_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1081_, v_constName_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_ref_1090_, lean_object* v_constName_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1089_, v_ref_1090_, v_constName_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_ref_1090_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1098_, lean_object* v_ref_1099_, lean_object* v_msg_1100_, lean_object* v_declHint_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1099_, v_msg_1100_, v_declHint_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1108_, lean_object* v_ref_1109_, lean_object* v_msg_1110_, lean_object* v_declHint_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1108_, v_ref_1109_, v_msg_1110_, v_declHint_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v_ref_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1118_, lean_object* v_declHint_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1118_, v_declHint_1119_, v___y_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1126_, lean_object* v_declHint_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1126_, v_declHint_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1134_, lean_object* v_ref_1135_, lean_object* v_msg_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1135_, v_msg_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_ref_1144_, lean_object* v_msg_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1143_, v_ref_1144_, v_msg_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v_ref_1144_);
return v_res_1151_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1);
v___x_1158_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
lean_ctor_set(v___x_1158_, 2, v___x_1157_);
lean_ctor_set(v___x_1158_, 3, v___x_1157_);
lean_ctor_set(v___x_1158_, 4, v___x_1157_);
lean_ctor_set(v___x_1158_, 5, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(lean_object* v_ext_1159_, lean_object* v_b_1160_, uint8_t v_kind_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_currNamespace_1166_; lean_object* v___x_1167_; lean_object* v_env_1168_; lean_object* v_nextMacroScope_1169_; lean_object* v_ngen_1170_; lean_object* v_auxDeclNGen_1171_; lean_object* v_traceState_1172_; lean_object* v_messages_1173_; lean_object* v_infoState_1174_; lean_object* v_snapshotTasks_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1202_; 
v_currNamespace_1166_ = lean_ctor_get(v___y_1163_, 5);
v___x_1167_ = lean_st_ref_take(v___y_1164_);
v_env_1168_ = lean_ctor_get(v___x_1167_, 0);
v_nextMacroScope_1169_ = lean_ctor_get(v___x_1167_, 1);
v_ngen_1170_ = lean_ctor_get(v___x_1167_, 2);
v_auxDeclNGen_1171_ = lean_ctor_get(v___x_1167_, 3);
v_traceState_1172_ = lean_ctor_get(v___x_1167_, 4);
v_messages_1173_ = lean_ctor_get(v___x_1167_, 6);
v_infoState_1174_ = lean_ctor_get(v___x_1167_, 7);
v_snapshotTasks_1175_ = lean_ctor_get(v___x_1167_, 8);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v___x_1167_, 5);
lean_dec(v_unused_1203_);
v___x_1177_ = v___x_1167_;
v_isShared_1178_ = v_isSharedCheck_1202_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snapshotTasks_1175_);
lean_inc(v_infoState_1174_);
lean_inc(v_messages_1173_);
lean_inc(v_traceState_1172_);
lean_inc(v_auxDeclNGen_1171_);
lean_inc(v_ngen_1170_);
lean_inc(v_nextMacroScope_1169_);
lean_inc(v_env_1168_);
lean_dec(v___x_1167_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1202_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
lean_inc(v_currNamespace_1166_);
v___x_1179_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1168_, v_ext_1159_, v_b_1160_, v_kind_1161_, v_currNamespace_1166_);
v___x_1180_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 5, v___x_1180_);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_nextMacroScope_1169_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_ngen_1170_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_auxDeclNGen_1171_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_traceState_1172_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1201_, 6, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1201_, 7, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1201_, 8, v_snapshotTasks_1175_);
v___x_1182_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_mctx_1185_; lean_object* v_zetaDeltaFVarIds_1186_; lean_object* v_postponed_1187_; lean_object* v_diag_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1199_; 
v___x_1183_ = lean_st_ref_put(v___y_1164_, v___x_1182_);
v___x_1184_ = lean_st_ref_take(v___y_1162_);
v_mctx_1185_ = lean_ctor_get(v___x_1184_, 0);
v_zetaDeltaFVarIds_1186_ = lean_ctor_get(v___x_1184_, 2);
v_postponed_1187_ = lean_ctor_get(v___x_1184_, 3);
v_diag_1188_ = lean_ctor_get(v___x_1184_, 4);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v___x_1184_, 1);
lean_dec(v_unused_1200_);
v___x_1190_ = v___x_1184_;
v_isShared_1191_ = v_isSharedCheck_1199_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_diag_1188_);
lean_inc(v_postponed_1187_);
lean_inc(v_zetaDeltaFVarIds_1186_);
lean_inc(v_mctx_1185_);
lean_dec(v___x_1184_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1199_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_mctx_1185_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_zetaDeltaFVarIds_1186_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_postponed_1187_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v_diag_1188_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_st_ref_put(v___y_1162_, v___x_1194_);
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___boxed(lean_object* v_ext_1204_, lean_object* v_b_1205_, lean_object* v_kind_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_kind_boxed_1211_; lean_object* v_res_1212_; 
v_kind_boxed_1211_ = lean_unbox(v_kind_1206_);
v_res_1212_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_1204_, v_b_1205_, v_kind_boxed_1211_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_00_u03c3_1215_, lean_object* v_ext_1216_, lean_object* v_b_1217_, uint8_t v_kind_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_1216_, v_b_1217_, v_kind_1218_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_00_u03b2_1226_, lean_object* v_00_u03c3_1227_, lean_object* v_ext_1228_, lean_object* v_b_1229_, lean_object* v_kind_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v_kind_boxed_1236_; lean_object* v_res_1237_; 
v_kind_boxed_1236_ = lean_unbox(v_kind_1230_);
v_res_1237_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0(v_00_u03b1_1225_, v_00_u03b2_1226_, v_00_u03c3_1227_, v_ext_1228_, v_b_1229_, v_kind_boxed_1236_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object* v_ext_1238_, lean_object* v_declName_1239_, uint8_t v_attrKind_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_declName_1239_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1247_);
v___x_1249_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_1238_, v___x_1248_, v_attrKind_1240_, v_a_1242_, v_a_1243_, v_a_1244_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_ext_1238_);
v_a_1250_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1246_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1246_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr___boxed(lean_object* v_ext_1258_, lean_object* v_declName_1259_, lean_object* v_attrKind_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
uint8_t v_attrKind_boxed_1266_; lean_object* v_res_1267_; 
v_attrKind_boxed_1266_ = lean_unbox(v_attrKind_1260_);
v_res_1267_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_1258_, v_declName_1259_, v_attrKind_boxed_1266_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1267_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
}
#ifdef __cplusplus
}
#endif
